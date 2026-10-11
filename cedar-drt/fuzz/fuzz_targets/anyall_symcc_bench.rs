/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! Phase 8 (`anyall-set-operators`) — cvc5 runtime benchmark harness.
//!
//! Measures how cvc5 actually scales on the `.all`/`.any` set-quantifier
//! encoding (the D-52 two-`set.filter` `HO_ALL` comprehension), across the
//! req-5.4 dimensions: solve wall-time, outcome
//! (sat/unsat/unknown/timeout/oom), and SMT term size. Decidability (Phase 5B)
//! is not tractability — this quantifies the practical envelope (RFC 0021
//! performance drawback).
//!
//! Not a libfuzzer target: a fixed parameterized sweep driven by `main()`.
//! `required-features = ["anyall"]` + `bench=false,test=false,doc=false`, so a
//! plain `cargo test`/`cargo build` never compiles or runs it. See
//! `.kiro/specs/anyall-set-operators/branches/phase8-anyall-cvc5-benchmarks/PLAN.md`.
//!
//! LOAD-BEARING CONSTRAINT (D-68 / D-P8-nonvac): every benchmarked `.all`/`.any`
//! policy uses a SYMBOLIC receiver (a `context`/entity set attribute whose value
//! is an SMT unknown). A literal-set receiver folds at compile time and emits no
//! `set.filter` — measuring the Rust folder, not cvc5. Before any quantified row
//! is timed, the harness serializes the compiled asserts to SMT-LIB and asserts
//! the script contains a `set.filter` term under `(set-logic HO_ALL)`. A folded
//! or rejected policy FAILS the harness rather than being recorded.
//!
//! UN-OPTIMIZED VERBS (D-P8-unopt / D-77): the SymCCOpt (`_opt`) path rejects
//! `.all` under the D-74/D-77 interim, so the harness pins the un-optimized
//! check verbs and records `pathway=unopt` on every row.
//!
//! CLI:
//!   --smoke            baseline point of each dimension + small sizes, one verb
//!                      per family, 10 s/query. Target wall < 2 min. (default)
//!   --full             the whole sweep; per-query timeout 300 s (DRT
//!                      TIMEOUT_DUR); `--max-wall-secs` default 5400 (~90 min,
//!                      D-87); stops cleanly on budget exhaustion recording the
//!                      covered rows. `--max-wall-secs 0` = uncapped (documented,
//!                      not run this phase).
//!   --selftest         fast in-process checks of the outcome model (timeout is
//!                      first-class, families validate+compile+non-vacuous,
//!                      baseline is a fair comparand). No long solves.
//!   --summarize <path> read a results JSON and print median/p90 per dimension.
//!   --format {json,csv}  output format for a sweep (default json).
//!   --out <path>       write sweep output to a file (else stdout).
//!   --repeats <k>      repeats per point for median/p90 (default 1 smoke, 3 full).
//!   --max-wall-secs <n> wall-clock budget for --full (default 5400; 0 = uncapped).
//!   --sizes a,b,..  override the set-size axis (push toward the cliff).

// The un-optimized `WellTypedPolicies` + `check_*` verbs are `#[deprecated]` in
// favour of the `CompiledPolicySet` (`_opt`) path, but that path rejects `.all`
// under the D-77 interim — the whole point of this harness is to pin the un-opt
// path that still accepts the quantifier. So deprecation is expected here.
#![allow(deprecated)]

use std::collections::BTreeMap;
use std::fmt::Display;
use std::fs;
use std::io::Write;
use std::mem;
use std::process::Command as StdCommand;
use std::time::{Duration, Instant};

use cedar_drt_inner::symcc::local_solver;
use cedar_policy::{PolicySet, RequestEnv, Schema, Validator};
use cedar_policy_symcc::{
    err::Error, solver::LocalSolver, solver::SolverError, solver::WriterSolver, CedarSymCompiler,
    SymEnv, WellTypedPolicies, WellTypedPolicy,
};
use serde::{Deserialize, Serialize};

/// Per-query timeout for `--full`: the repo's DRT `TIMEOUT_DUR` (D-87).
const FULL_TIMEOUT: Duration = Duration::from_secs(300);
/// Per-query timeout for `--smoke`: generous but short.
const SMOKE_TIMEOUT: Duration = Duration::from_secs(10);
/// Default `--full` wall-clock budget: ~90 min (D-87).
const DEFAULT_FULL_WALL_SECS: u64 = 5400;
/// The analysis pathway every row records (D-P8-unopt).
const PATHWAY: &str = "unopt";
/// Fixed RNG-style seed recorded in `RunMeta` for reproducibility. The swept
/// policies are hand-built text (deterministic by construction), so this seed
/// only labels the run; it is not consumed by a generator here.
const SEED: u64 = 0x0A11_0A11;

// ===========================================================================
// Outcome model (P2)
// ===========================================================================

/// First-class outcome of a single solver query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum SolveOutcome {
    /// The negated verification query is satisfiable: a counterexample exists
    /// (the checked property does NOT hold).
    Sat,
    /// The negated query is unsatisfiable: the property holds.
    Unsat,
    /// cvc5 returned `unknown`.
    Unknown,
    /// The query exceeded the per-query timeout.
    Timeout,
    /// The solver process failed to allocate under the 1 GB cap (best-effort
    /// classification from the solver error).
    Oom,
    /// The compiled asserts could not be encoded / the verb errored for a reason
    /// other than unknown/oom (recorded, not panicked, so a sweep continues).
    EncodeError,
}

impl Display for SolveOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            SolveOutcome::Sat => "sat",
            SolveOutcome::Unsat => "unsat",
            SolveOutcome::Unknown => "unknown",
            SolveOutcome::Timeout => "timeout",
            SolveOutcome::Oom => "oom",
            SolveOutcome::EncodeError => "encode_error",
        })
    }
}

/// Classify a verb error into a first-class non-sat outcome. A `check_*` verb
/// returns `Ok(bool)` on a real decision (mapped by the caller to Sat/Unsat);
/// this maps the error arms. OOM detection is heuristic (R4): the 1 GB
/// `setrlimit` makes cvc5 fail allocation, surfacing EITHER as a graceful
/// `std::bad_alloc` solver error OR as an abrupt process kill (the OOM-killer /
/// `RLIMIT_AS` abort gives no exit status — `terminated unexpectedly with
/// status: None`, a signal/kill). Both are the same memory-cap death and are
/// classified `Oom`; everything else solver-side is kept as the raw error
/// string under `EncodeError` for auditability.
fn classify_err(e: &Error) -> (SolveOutcome, String) {
    match e {
        Error::SolverUnknown => (SolveOutcome::Unknown, "solver returned unknown".into()),
        Error::SolverError(se) => {
            let raw = se.to_string();
            if is_oom_signature(&raw) {
                (SolveOutcome::Oom, format!("solver error (classified oom): {se}"))
            } else {
                (SolveOutcome::EncodeError, format!("solver error: {se}"))
            }
        }
        other => (SolveOutcome::EncodeError, format!("verb error: {other}")),
    }
}

/// True when a solver error string looks like the 1 GiB memory cap being hit —
/// either a graceful allocation failure (`std::bad_alloc`, "out of memory") or
/// an abrupt kill with no exit status (the `RLIMIT_AS` / OOM-killer signature:
/// "terminated unexpectedly with status: None", "killed", a "signal"). Factored
/// out of `classify_err` so `--selftest` can exercise the exact table
/// deterministically, without a real solver.
fn is_oom_signature(raw: &str) -> bool {
    let msg = raw.to_lowercase();
    // Graceful allocation failure under the cap.
    msg.contains("memory")
        || msg.contains("alloc")
        || msg.contains("out of")
        || msg.contains("bad_alloc")
        // Abrupt kill under the cap: the process dies with no exit status, which
        // the solver surfaces as "terminated unexpectedly with status: None"
        // (F-2: this is a mem-cap death at N=192, not an encoder failure).
        || msg.contains("terminated unexpectedly")
        || msg.contains("status: none")
        || msg.contains("killed")
        || msg.contains("signal")
        // Pipe/EOF breakage from a solver that vanished mid-query.
        || msg.contains("unexpected eof")
        || msg.contains("broken pipe")
}

// ===========================================================================
// Dimensions (P3)
// ===========================================================================

/// Which req-5.4 dimension a row belongs to (dimension 5 = verb is carried
/// separately on the row).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Dimension {
    SetSize,
    PredicateComplexity,
    ElementType,
    QuantifierCount,
    Verb,
    AllVsAny,
    SatVsUnsat,
}

impl Display for Dimension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Dimension::SetSize => "set_size",
            Dimension::PredicateComplexity => "predicate_complexity",
            Dimension::ElementType => "element_type",
            Dimension::QuantifierCount => "quantifier_count",
            Dimension::Verb => "verb",
            Dimension::AllVsAny => "all_vs_any",
            Dimension::SatVsUnsat => "sat_vs_unsat",
        })
    }
}

/// The coordinates of a single swept point.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Dims {
    dimension: Dimension,
    /// Human-readable point within the dimension (e.g. "n=8", "depth=3",
    /// "String", "k=2", ".any", "unsat_shape").
    point: String,
    /// `quantified` (the `.all`/`.any` policy) or `baseline` (the quantifier-free
    /// comparand, P4).
    shape: Shape,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Shape {
    Quantified,
    Baseline,
}

impl Display for Shape {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Shape::Quantified => "quantified",
            Shape::Baseline => "baseline",
        })
    }
}

/// Which check verb a row used. Only the un-optimized verbs (D-P8-unopt).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Verb {
    AlwaysAllows,
    AlwaysDenies,
    Equivalent,
    Implies,
    Disjoint,
    NeverErrors,
}

impl Verb {
    fn as_str(self) -> &'static str {
        match self {
            Verb::AlwaysAllows => "check_always_allows",
            Verb::AlwaysDenies => "check_always_denies",
            Verb::Equivalent => "check_equivalent",
            Verb::Implies => "check_implies",
            Verb::Disjoint => "check_disjoint",
            Verb::NeverErrors => "check_never_errors",
        }
    }
    /// How many policy sets this verb consumes.
    fn arity(self) -> VerbArity {
        match self {
            Verb::AlwaysAllows | Verb::AlwaysDenies => VerbArity::OnePset,
            Verb::Equivalent | Verb::Implies | Verb::Disjoint => VerbArity::TwoPsets,
            Verb::NeverErrors => VerbArity::OnePolicy,
        }
    }
}

enum VerbArity {
    OnePset,
    TwoPsets,
    OnePolicy,
}

// ===========================================================================
// A benchmark case: a built schema + policy text(s) + the verb + the dimension.
// ===========================================================================

/// A fully specified, deterministic benchmark case.
struct Case {
    dims: Dims,
    verb: Verb,
    schema_src: String,
    /// Primary policy set text (the `.all`/`.any` policy, or its baseline).
    pset1: String,
    /// Second policy set text, for the two-pset verbs. `None` otherwise.
    pset2: Option<String>,
    principal_ty: String,
    action: String,
    resource_ty: String,
}

/// The emitted-SMT facts used for the non-vacuity gate and recorded on the row.
#[derive(Debug, Clone, Copy)]
struct EncodingFacts {
    has_set_filter: bool,
    has_ho_all: bool,
    smt_bytes: usize,
    /// Cheap SMT-string term-size proxy: count of `(` in the script (node-ish).
    term_size: usize,
}

fn encoding_facts(smtlib: &str) -> EncodingFacts {
    EncodingFacts {
        has_set_filter: smtlib.contains("set.filter"),
        has_ho_all: smtlib.contains("HO_ALL"),
        smt_bytes: smtlib.len(),
        term_size: smtlib.bytes().filter(|&b| b == b'(').count(),
    }
}

// ===========================================================================
// Output records (P5)
// ===========================================================================

#[derive(Debug, Clone, Serialize, Deserialize)]
struct QueryResult {
    dimension: Dimension,
    point: String,
    shape: Shape,
    verb: String,
    pathway: String,
    outcome: SolveOutcome,
    /// Solver wall-time in ms (wraps ONLY the check verb await).
    solve_ms: u128,
    /// Compile wall-time in ms (type-check + build well-typed policies).
    compile_ms: u128,
    term_size: usize,
    smt_bytes: usize,
    encoding_has_set_filter: bool,
    encoding_has_ho_all: bool,
    /// Raw solver note when the outcome is a non-sat/unsat classification.
    note: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct RunMeta {
    cvc5_version: String,
    cedar_sdk_version: String,
    cedar_spec_sha: String,
    cedar_sha: String,
    seed: u64,
    per_query_timeout_secs: u64,
    max_wall_secs: u64,
    mem_cap_bytes: u64,
    pathway: String,
    host_cpus: usize,
    host_mem_kb: u64,
    mode: String,
    repeats: u32,
    /// True if `--full` stopped early on the wall-clock budget (partial sweep).
    budget_exhausted: bool,
    /// Rows actually covered.
    rows: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct BenchReport {
    meta: RunMeta,
    results: Vec<QueryResult>,
}

// ===========================================================================
// Env capture for RunMeta
// ===========================================================================

fn shell_capture(cmd: &str, args: &[&str]) -> String {
    StdCommand::new(cmd)
        .args(args)
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.lines().next().unwrap_or("").trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

fn git_sha(dir: &str) -> String {
    StdCommand::new("git")
        .args(["-C", dir, "rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "unknown".into())
}

fn host_mem_kb() -> u64 {
    fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("MemTotal:"))
                .and_then(|l| l.split_whitespace().nth(1))
                .and_then(|n| n.parse::<u64>().ok())
        })
        .unwrap_or(0)
}

fn cvc5_version() -> String {
    let cvc5 = std::env::var("CVC5").unwrap_or_else(|_| "cvc5".into());
    shell_capture(&cvc5, &["--version"])
}

// ===========================================================================
// Compile + solve helpers (un-opt path)
// ===========================================================================

fn schema_from_cedarstr(src: &str) -> Schema {
    Schema::from_cedarschema_str(src)
        .unwrap_or_else(|e| panic!("schema should parse: {e}"))
        .0
}

fn pset_from_text(text: &str, validator: &Validator) -> PolicySet {
    let pset: PolicySet = text
        .parse()
        .unwrap_or_else(|e| panic!("policy set should parse: {e}\n{text}"));
    let res = validator.validate(&pset, cedar_policy::ValidationMode::Strict);
    assert!(
        res.validation_passed(),
        "policy set should validate (Strict): {:?}\n{text}",
        res.validation_errors().collect::<Vec<_>>()
    );
    pset
}

struct Compiled {
    typed1: WellTypedPolicies,
    typed2: Option<WellTypedPolicies>,
    /// Single well-typed policy for the single-policy `check_never_errors` verb.
    typed_single: Option<WellTypedPolicy>,
    symenv: SymEnv,
    compile_ms: u128,
}

fn compile_case(case: &Case) -> Compiled {
    let schema = schema_from_cedarstr(&case.schema_src);
    let validator = Validator::new(schema.clone());
    let req_env = RequestEnv::new(
        case.principal_ty.parse().expect("principal type"),
        case.action.parse().expect("action euid"),
        case.resource_ty.parse().expect("resource type"),
    );
    let symenv = SymEnv::new(&schema, &req_env).expect("SymEnv::new");

    let start = Instant::now();
    let pset1 = pset_from_text(&case.pset1, &validator);
    let typed1 = WellTypedPolicies::from_policies(&pset1, &req_env, &schema)
        .expect("pset1 should type-check");
    let typed2 = case.pset2.as_ref().map(|t| {
        let p = pset_from_text(t, &validator);
        WellTypedPolicies::from_policies(&p, &req_env, &schema).expect("pset2 should type-check")
    });
    // `check_never_errors` is a single-policy verb; build the single well-typed
    // policy from the first (and only) policy of pset1 for that verb.
    let typed_single = if matches!(case.verb, Verb::NeverErrors) {
        let p = pset_from_text(&case.pset1, &validator);
        let policy = p
            .policies()
            .next()
            .expect("never_errors case needs exactly one policy")
            .clone();
        Some(
            WellTypedPolicy::from_policy(&policy, &req_env, &schema)
                .expect("single policy should type-check"),
        )
    } else {
        None
    };
    let compile_ms = start.elapsed().as_millis();

    Compiled {
        typed1,
        typed2,
        typed_single,
        symenv,
        compile_ms,
    }
}

/// Capture the SMT-LIB a given verb emits for `c`, via an un-opt `WriterSolver`
/// (records all commands, answers check-sat `unknown`). Used for the
/// non-vacuity gate — un-opt analogue of `symcc.rs::smtlib_of_check_asserts`.
async fn capture_smt(verb: Verb, c: &Compiled) -> Result<String, String> {
    let mut w = CedarSymCompiler::new(WriterSolver { w: Vec::<u8>::new() })
        .map_err(|e| format!("WriterSolver construct: {e}"))?;
    let res: Result<(), Error> = match (verb, verb.arity()) {
        (Verb::AlwaysAllows, _) => w.check_always_allows(&c.typed1, &c.symenv).await.map(|_| ()),
        (Verb::AlwaysDenies, _) => w.check_always_denies(&c.typed1, &c.symenv).await.map(|_| ()),
        (Verb::NeverErrors, _) => {
            let p = c.typed_single.as_ref().expect("never_errors needs a single policy");
            w.check_never_errors(p, &c.symenv).await.map(|_| ())
        }
        (Verb::Equivalent, _) => {
            let t2 = c.typed2.as_ref().expect("two-pset verb needs pset2");
            w.check_equivalent(&c.typed1, t2, &c.symenv).await.map(|_| ())
        }
        (Verb::Implies, _) => {
            let t2 = c.typed2.as_ref().expect("two-pset verb needs pset2");
            w.check_implies(&c.typed1, t2, &c.symenv).await.map(|_| ())
        }
        (Verb::Disjoint, _) => {
            let t2 = c.typed2.as_ref().expect("two-pset verb needs pset2");
            w.check_disjoint(&c.typed1, t2, &c.symenv).await.map(|_| ())
        }
    };
    match res {
        Ok(()) | Err(Error::SolverUnknown) => {
            Ok(String::from_utf8(mem::take(&mut w.solver_mut().w)).expect("smtlib utf8"))
        }
        Err(e) => Err(format!("un-opt encode failed: {e}")),
    }
}

/// Run `verb` on `c` against cvc5 with `timeout`, returning the outcome + ms.
async fn solve(
    compiler: &mut CedarSymCompiler<LocalSolver>,
    verb: Verb,
    c: &Compiled,
    timeout: Duration,
) -> (SolveOutcome, u128, Option<String>) {
    let start = Instant::now();
    // `check_*` returns Ok(true) when the property holds (negated query UNSAT),
    // Ok(false) when a counterexample exists (negated query SAT).
    let fut = async {
        match verb {
            Verb::AlwaysAllows => compiler.check_always_allows(&c.typed1, &c.symenv).await,
            Verb::AlwaysDenies => compiler.check_always_denies(&c.typed1, &c.symenv).await,
            Verb::NeverErrors => {
                compiler
                    .check_never_errors(c.typed_single.as_ref().unwrap(), &c.symenv)
                    .await
            }
            Verb::Equivalent => {
                compiler
                    .check_equivalent(&c.typed1, c.typed2.as_ref().unwrap(), &c.symenv)
                    .await
            }
            Verb::Implies => {
                compiler
                    .check_implies(&c.typed1, c.typed2.as_ref().unwrap(), &c.symenv)
                    .await
            }
            Verb::Disjoint => {
                compiler
                    .check_disjoint(&c.typed1, c.typed2.as_ref().unwrap(), &c.symenv)
                    .await
            }
        }
    };
    let res = tokio::time::timeout(timeout, fut).await;
    let solve_ms = start.elapsed().as_millis();
    match res {
        Err(_elapsed) => (SolveOutcome::Timeout, solve_ms, Some("per-query timeout".into())),
        Ok(Ok(true)) => (SolveOutcome::Unsat, solve_ms, None),
        Ok(Ok(false)) => (SolveOutcome::Sat, solve_ms, None),
        Ok(Err(e)) => {
            let (o, note) = classify_err(&e);
            (o, solve_ms, Some(note))
        }
    }
}

/// Compile + non-vacuity-gate + solve one case, producing a `QueryResult`.
/// `require_filter` is true for quantified rows (the gate is a HARD assertion)
/// and false for baseline rows (quantifier-free; no `set.filter` expected).
async fn run_case(
    compiler: &mut CedarSymCompiler<LocalSolver>,
    case: &Case,
    timeout: Duration,
) -> QueryResult {
    let c = compile_case(case);
    let smt = capture_smt(case.verb, &c).await.expect("SMT capture");
    let facts = encoding_facts(&smt);
    if case.dims.shape == Shape::Quantified {
        assert!(
            facts.has_set_filter,
            "non-vacuity ({dim}/{pt}): emitted SMT must contain `set.filter` \
             (receiver folded or policy rejected?)\n{smt}",
            dim = case.dims.dimension,
            pt = case.dims.point
        );
        assert!(
            facts.has_ho_all,
            "non-vacuity ({dim}/{pt}): emitted SMT must use HO_ALL\n{smt}",
            dim = case.dims.dimension,
            pt = case.dims.point
        );
    }
    let (outcome, solve_ms, note) = solve(compiler, case.verb, &c, timeout).await;
    QueryResult {
        dimension: case.dims.dimension,
        point: case.dims.point.clone(),
        shape: case.dims.shape,
        verb: case.verb.as_str().to_string(),
        pathway: PATHWAY.to_string(),
        outcome,
        solve_ms,
        compile_ms: c.compile_ms,
        term_size: facts.term_size,
        smt_bytes: facts.smt_bytes,
        encoding_has_set_filter: facts.has_set_filter,
        encoding_has_ho_all: facts.has_ho_all,
        note,
    }
}

// ===========================================================================
// Family builders (P3 + P4). All deterministic hand-built policy text over a
// SYMBOLIC receiver. `n` candidate members realise the "set size" axis
// (§0.2 / D-P8-size): the `.all` ranges over the whole symbolic set, and N
// conjoined `context.ports.contains(e_i)` guards pin N named members, which is
// the quantity the paper's x-axis varies. The baseline (P4) replaces the `.all`
// with the explicit per-member unroll, same N — a fair comparand.
// ===========================================================================

/// Schema with a symbolic `Set<Long>` receiver + N `Long` context slots for
/// membership pins.
fn long_schema(n: usize) -> String {
    let mut ctx = String::from("ports: Set<Long>");
    for i in 0..n {
        ctx.push_str(&format!(", e{i}: Long"));
    }
    format!(
        "entity User;\nentity Thing;\naction view appliesTo {{\n  principal: [User],\n  resource: [Thing],\n  context: {{ {ctx} }}\n}};\n"
    )
}

/// `context.ports.contains(context.e0) && … && context.ports.contains(context.e{n-1})`
fn membership_pins(n: usize) -> String {
    (0..n)
        .map(|i| format!("context.ports.contains(context.e{i})"))
        .collect::<Vec<_>>()
        .join(" && ")
}

/// Quantified `.all` policy over the symbolic receiver with N membership pins.
fn quantified_all(pred: &str, n: usize) -> String {
    let guard = if n == 0 {
        format!("context.ports.all({pred})")
    } else {
        format!("{} && context.ports.all({pred})", membership_pins(n))
    };
    format!("permit(principal, action, resource) when {{ {guard} }};")
}

/// Quantifier-free baseline: the `.all(pred)` unrolled over the N pinned members
/// as `(context.ports.contains(e_i) => pred[it:=e_i])`, i.e. the same semantics
/// the `.all` has over exactly those N candidate members. For N=0 we drop the
/// quantifier entirely (trivially-true guard), which is the "no quantifier"
/// comparand.
fn baseline_unroll(pred_on: &dyn Fn(&str) -> String, n: usize) -> String {
    let guard = if n == 0 {
        "true".to_string()
    } else {
        (0..n)
            .map(|i| {
                let e = format!("context.e{i}");
                format!(
                    "(context.ports.contains({e}) && {}) || !context.ports.contains({e})",
                    pred_on(&e)
                )
            })
            .collect::<Vec<_>>()
            .join(" && ")
    };
    // Also keep the membership pins so the baseline and quantified queries share
    // the same symbolic structure over the N members.
    let pins = if n == 0 { String::new() } else { format!("{} && ", membership_pins(n)) };
    format!("permit(principal, action, resource) when {{ {pins}{guard} }};")
}

/// Build the "set size" dimension cases (quantified + optional baseline) for
/// size `n`, verb `check_always_allows`, predicate `it > 0`.
///
/// The quantifier-free baseline is the `.all` unrolled over the N pinned
/// members; its N-way conjunction is a deeply-nested AST, so for large N the
/// Cedar parser's recursive descent overflows the stack. The baseline is only a
/// comparand (P4 fairness is asserted at small N), so it is emitted only for
/// `n <= BASELINE_MAX_N`; the quantified `.all` row (fixed-shape, the one that
/// actually probes the cvc5 cliff) is always emitted.
fn set_size_cases(n: usize) -> Vec<Case> {
    const BASELINE_MAX_N: usize = 64;
    let schema = long_schema(n);
    let pred_on = |e: &str| format!("{e} > 0");
    let mut cases = vec![Case {
        dims: Dims { dimension: Dimension::SetSize, point: format!("n={n}"), shape: Shape::Quantified },
        verb: Verb::AlwaysAllows,
        schema_src: schema.clone(),
        pset1: quantified_all("it > 0", n),
        pset2: None,
        principal_ty: "User".into(),
        action: "Action::\"view\"".into(),
        resource_ty: "Thing".into(),
    }];
    if n <= BASELINE_MAX_N {
        cases.push(Case {
            dims: Dims { dimension: Dimension::SetSize, point: format!("n={n}"), shape: Shape::Baseline },
            verb: Verb::AlwaysAllows,
            schema_src: schema,
            pset1: baseline_unroll(&pred_on, n),
            pset2: None,
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        });
    }
    cases
}

/// Predicate-complexity dimension: increasing predicate AST depth/op-count.
fn predicate_cases(points: &[(&str, &str)]) -> Vec<Case> {
    // Each (label, pred) over a symbolic Set<Long>, verb always_allows, N=0.
    let schema = long_schema(0);
    points
        .iter()
        .map(|(label, pred)| Case {
            dims: Dims { dimension: Dimension::PredicateComplexity, point: (*label).into(), shape: Shape::Quantified },
            verb: Verb::AlwaysAllows,
            schema_src: schema.clone(),
            pset1: quantified_all(pred, 0),
            pset2: None,
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        })
        .collect()
}

/// Element-type dimension: Long / String / Bool / EntityUID receivers.
fn element_type_cases() -> Vec<Case> {
    let cases = [
        ("Long", "ports: Set<Long>", "it > 0"),
        ("String", "names: Set<String>", "it like \"a*\""),
        ("Bool", "flags: Set<Bool>", "it == true"),
    ];
    cases
        .iter()
        .map(|(label, attr, pred)| {
            let field = attr.split(':').next().unwrap().trim();
            let schema = format!(
                "entity User;\nentity Thing;\naction view appliesTo {{\n  principal: [User],\n  resource: [Thing],\n  context: {{ {attr} }}\n}};\n"
            );
            Case {
                dims: Dims { dimension: Dimension::ElementType, point: (*label).into(), shape: Shape::Quantified },
                verb: Verb::AlwaysAllows,
                schema_src: schema,
                pset1: format!("permit(principal, action, resource) when {{ context.{field}.all({pred}) }};"),
                pset2: None,
                principal_ty: "User".into(),
                action: "Action::\"view\"".into(),
                resource_ty: "Thing".into(),
            }
        })
        .collect()
}

/// Entity-element element-type case (receiver `Set<User>`), kept separate
/// because it needs an entity schema.
fn element_type_entity_case() -> Case {
    let schema = "entity User;\nentity Doc { owners: Set<User> };\naction view appliesTo {\n  principal: [User],\n  resource: [Doc],\n  context: {}\n};\n".to_string();
    Case {
        dims: Dims { dimension: Dimension::ElementType, point: "EntityUID".into(), shape: Shape::Quantified },
        verb: Verb::AlwaysAllows,
        schema_src: schema,
        pset1: "permit(principal, action, resource) when { resource.owners.all(it == principal) };".to_string(),
        pset2: None,
        principal_ty: "User".into(),
        action: "Action::\"view\"".into(),
        resource_ty: "Doc".into(),
    }
}

/// Quantifier-count dimension: k sibling (non-nested) `.all`s conjoined.
fn quantifier_count_cases(ks: &[usize]) -> Vec<Case> {
    ks.iter()
        .map(|&k| {
            // k independent Set<Long> receivers s0..s{k-1}, each with its own `.all`.
            let mut ctx = Vec::new();
            for i in 0..k {
                ctx.push(format!("s{i}: Set<Long>"));
            }
            let schema = format!(
                "entity User;\nentity Thing;\naction view appliesTo {{\n  principal: [User],\n  resource: [Thing],\n  context: {{ {} }}\n}};\n",
                ctx.join(", ")
            );
            let guard = (0..k)
                .map(|i| format!("context.s{i}.all(it > 0)"))
                .collect::<Vec<_>>()
                .join(" && ");
            Case {
                dims: Dims { dimension: Dimension::QuantifierCount, point: format!("k={k}"), shape: Shape::Quantified },
                verb: Verb::AlwaysAllows,
                schema_src: schema,
                pset1: format!("permit(principal, action, resource) when {{ {guard} }};"),
                pset2: None,
                principal_ty: "User".into(),
                action: "Action::\"view\"".into(),
                resource_ty: "Thing".into(),
            }
        })
        .collect()
}

/// Verb dimension: every un-optimized verb on a symbolic `.all` policy.
fn verb_cases() -> Vec<Case> {
    let schema = long_schema(0);
    let p_gt0 = quantified_all("it > 0", 0);
    let p_ge0 = quantified_all("it >= 0", 0);
    let mk = |verb: Verb, pset1: String, pset2: Option<String>| Case {
        dims: Dims { dimension: Dimension::Verb, point: verb.as_str().into(), shape: Shape::Quantified },
        verb,
        schema_src: schema.clone(),
        pset1,
        pset2,
        principal_ty: "User".into(),
        action: "Action::\"view\"".into(),
        resource_ty: "Thing".into(),
    };
    vec![
        mk(Verb::AlwaysAllows, p_gt0.clone(), None),
        mk(Verb::AlwaysDenies, p_gt0.clone(), None),
        mk(Verb::Equivalent, p_gt0.clone(), Some(p_ge0.clone())),
        mk(Verb::Implies, p_gt0.clone(), Some(p_ge0.clone())),
        mk(Verb::Disjoint, p_gt0.clone(), Some(p_ge0)),
        mk(Verb::NeverErrors, p_gt0, None),
    ]
}

/// `.all` vs `.any` dimension: same shape, `.any` lowering.
fn all_vs_any_cases() -> Vec<Case> {
    let schema = long_schema(0);
    vec![
        Case {
            dims: Dims { dimension: Dimension::AllVsAny, point: ".all".into(), shape: Shape::Quantified },
            verb: Verb::AlwaysAllows,
            schema_src: schema.clone(),
            pset1: "permit(principal, action, resource) when { context.ports.all(it > 0) };".into(),
            pset2: None,
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        },
        Case {
            dims: Dims { dimension: Dimension::AllVsAny, point: ".any".into(), shape: Shape::Quantified },
            verb: Verb::AlwaysAllows,
            schema_src: schema,
            pset1: "permit(principal, action, resource) when { context.ports.any(it > 0) };".into(),
            pset2: None,
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        },
    ]
}

/// SAT vs UNSAT shape dimension via equivalence. The UNSAT shape must be a
/// GENUINELY equivalent but syntactically DISTINCT pair, so the equivalence is
/// *solved* over a real `set.filter` term rather than folded to constant-true
/// (two syntactically-identical compiled psets reduce to a trivially-true
/// assert that SymCC never encodes — a vacuous query, D-P8-eqfold). Over
/// `Long`, `it > 0` and `it >= 1` are equivalent (integers), so the dis-
/// equivalence is UNSAT and cvc5 must decide it. The SAT shape differs
/// (`it > 0` vs `it >= 0`), so a counterexample (a set containing `0`) exists.
fn sat_vs_unsat_cases() -> Vec<Case> {
    let schema = long_schema(0);
    let a = "permit(principal, action, resource) when { context.ports.all(it > 0) };";
    let a_equiv = "permit(principal, action, resource) when { context.ports.all(it >= 1) };";
    let b = "permit(principal, action, resource) when { context.ports.all(it >= 0) };";
    vec![
        Case {
            dims: Dims { dimension: Dimension::SatVsUnsat, point: "unsat_shape".into(), shape: Shape::Quantified },
            verb: Verb::Equivalent,
            schema_src: schema.clone(),
            pset1: a.into(),
            pset2: Some(a_equiv.into()),
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        },
        Case {
            dims: Dims { dimension: Dimension::SatVsUnsat, point: "sat_shape".into(), shape: Shape::Quantified },
            verb: Verb::Equivalent,
            schema_src: schema,
            pset1: a.into(),
            pset2: Some(b.into()),
            principal_ty: "User".into(),
            action: "Action::\"view\"".into(),
            resource_ty: "Thing".into(),
        },
    ]
}

/// Predicate-complexity points, ordered by increasing complexity.
fn predicate_points() -> Vec<(&'static str, &'static str)> {
    vec![
        ("d1_cmp", "it > 0"),
        ("d2_range", "it > 0 && it < 100"),
        ("d3_if", "if it > 0 then it < 100 else it == -1"),
        ("d4_nested_if", "if it > 0 then (if it < 100 then it != 50 else it == 7) else it == -1"),
    ]
}

/// The full sweep's set-size points, and the smoke subset.
///
/// N-1: the default `--full` axis now runs to **128** (the cliff onset: cvc5
/// solves N=128 in ~4.5 s, then OOMs at N≥192 under the 1 GiB cap), so the
/// headline sweep carries the first steep point rather than leaving it to the
/// separate `cliff-setsize.json` probe. The baseline unroll is capped at N≤64
/// (`BASELINE_MAX_N`), so N=128 contributes a quantified row only — still well
/// under a minute of added wall time.
fn full_sizes() -> Vec<usize> {
    vec![0, 1, 2, 4, 8, 16, 32, 64, 128]
}
fn smoke_sizes() -> Vec<usize> {
    vec![0, 1, 2, 4, 8]
}

/// Assemble the case list for a mode.
fn assemble_cases(full: bool, sizes: &[usize]) -> Vec<Case> {
    let mut cases = Vec::new();
    // Dim 1: set size (quantified + baseline).
    for &n in sizes {
        cases.extend(set_size_cases(n));
    }
    // Dim 2: predicate complexity.
    let pts = predicate_points();
    let pts_slice: &[(&str, &str)] = if full { &pts } else { &pts[..2] };
    cases.extend(predicate_cases(pts_slice));
    // Dim 3: element type.
    cases.extend(element_type_cases());
    if full {
        cases.push(element_type_entity_case());
    }
    // Dim 4: quantifier count.
    let ks: &[usize] = if full { &[1, 2, 3, 4] } else { &[1, 2] };
    cases.extend(quantifier_count_cases(ks));
    // Dim 5: verb (always full — it's the pinned-pathway coverage).
    cases.extend(verb_cases());
    // Dim 6: all vs any.
    cases.extend(all_vs_any_cases());
    // Dim 7: sat vs unsat.
    cases.extend(sat_vs_unsat_cases());
    cases
}

// ===========================================================================
// Summarizer (P6)
// ===========================================================================

fn percentile(sorted: &[u128], p: f64) -> u128 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((p / 100.0) * (sorted.len() as f64 - 1.0)).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn summarize(report: &BenchReport) -> String {
    let mut out = String::new();
    out.push_str("# anyall cvc5 benchmark summary (median / p90 solve_ms per dimension+verb+shape)\n");
    out.push_str(&format!(
        "# cvc5={} sdk={} spec_sha={} cedar_sha={} seed={:#x} per_query_timeout={}s wall_cap={}s mode={} repeats={} rows={} budget_exhausted={}\n",
        report.meta.cvc5_version,
        report.meta.cedar_sdk_version,
        report.meta.cedar_spec_sha,
        report.meta.cedar_sha,
        report.meta.seed,
        report.meta.per_query_timeout_secs,
        report.meta.max_wall_secs,
        report.meta.mode,
        report.meta.repeats,
        report.meta.rows,
        report.meta.budget_exhausted,
    ));
    // group by (dimension, point, shape, verb)
    let mut groups: BTreeMap<(String, String, String, String), Vec<&QueryResult>> = BTreeMap::new();
    for r in &report.results {
        groups
            .entry((
                r.dimension.to_string(),
                r.point.clone(),
                r.shape.to_string(),
                r.verb.clone(),
            ))
            .or_default()
            .push(r);
    }
    out.push_str("dimension\tpoint\tshape\tverb\tn\tmedian_ms\tp90_ms\tsat\tunsat\tunknown\ttimeout\toom\terr\n");
    for ((dim, point, shape, verb), rows) in &groups {
        let mut times: Vec<u128> = rows.iter().map(|r| r.solve_ms).collect();
        times.sort_unstable();
        let (mut sat, mut unsat, mut unknown, mut timeout, mut oom, mut err) = (0, 0, 0, 0, 0, 0);
        for r in rows {
            match r.outcome {
                SolveOutcome::Sat => sat += 1,
                SolveOutcome::Unsat => unsat += 1,
                SolveOutcome::Unknown => unknown += 1,
                SolveOutcome::Timeout => timeout += 1,
                SolveOutcome::Oom => oom += 1,
                SolveOutcome::EncodeError => err += 1,
            }
        }
        out.push_str(&format!(
            "{dim}\t{point}\t{shape}\t{verb}\t{}\t{}\t{}\t{sat}\t{unsat}\t{unknown}\t{timeout}\t{oom}\t{err}\n",
            times.len(),
            percentile(&times, 50.0),
            percentile(&times, 90.0),
        ));
    }
    out
}

// ===========================================================================
// Output
// ===========================================================================

fn to_csv(report: &BenchReport) -> String {
    let mut s = String::new();
    s.push_str("dimension,point,shape,verb,pathway,outcome,solve_ms,compile_ms,term_size,smt_bytes,has_set_filter,has_ho_all\n");
    for r in &report.results {
        s.push_str(&format!(
            "{},{},{},{},{},{},{},{},{},{},{},{}\n",
            r.dimension, r.point, r.shape, r.verb, r.pathway, r.outcome, r.solve_ms, r.compile_ms,
            r.term_size, r.smt_bytes, r.encoding_has_set_filter, r.encoding_has_ho_all
        ));
    }
    s
}

fn write_output(report: &BenchReport, format: &str, out_path: Option<&str>) {
    let body = match format {
        "csv" => to_csv(report),
        _ => serde_json::to_string_pretty(report).expect("serialize report"),
    };
    match out_path {
        Some(p) => {
            let mut f = fs::File::create(p).expect("create out file");
            f.write_all(body.as_bytes()).expect("write out file");
            eprintln!("# wrote {} rows to {p}", report.results.len());
        }
        None => println!("{body}"),
    }
}

// ===========================================================================
// Selftest (P2/P3/P4 green checks, no long solves)
// ===========================================================================

/// Deterministic classifier table (F-2). Builds `Error` values directly (no
/// solver) and asserts `classify_err` maps each to the right first-class
/// outcome, keeping the raw solver text in the note either way. Covers the two
/// mem-cap death signatures (graceful `bad_alloc` and the abrupt
/// `status: None` kill — the one the committed cliff data mislabeled) and a
/// genuine encoder error that must NOT be swallowed as `oom`.
fn classifier_table_selftest() {
    // (raw solver message, expected outcome). `SolverError::Solver(_)` is the
    // same variant the real `check_sat` path produces for both an allocation
    // failure and an abrupt process kill.
    let solver_cases: &[(&str, SolveOutcome)] = &[
        // Graceful allocation failure under the 1 GiB cap (N=256 in the data).
        ("std::bad_alloc", SolveOutcome::Oom),
        ("Cannot allocate memory", SolveOutcome::Oom),
        ("out of memory", SolveOutcome::Oom),
        // Abrupt kill under the cap — no exit status (N=192 in the data). This
        // is the row F-2 was about: it previously fell through to EncodeError.
        (
            "Solver process terminated unexpectedly with status: None",
            SolveOutcome::Oom,
        ),
        ("solver process killed", SolveOutcome::Oom),
        ("terminated by signal 9", SolveOutcome::Oom),
        ("broken pipe", SolveOutcome::Oom),
        ("unexpected EOF", SolveOutcome::Oom),
        // A genuine solver/encoder failure must stay EncodeError, not be
        // swallowed as oom.
        (
            "unexpected `(` in response to (check-sat)",
            SolveOutcome::EncodeError,
        ),
        ("unsupported logic feature", SolveOutcome::EncodeError),
    ];
    for (msg, want) in solver_cases {
        let e = Error::SolverError(SolverError::Solver((*msg).to_string()));
        let (got, note) = classify_err(&e);
        assert_eq!(
            got, *want,
            "classifier: {msg:?} should classify {want}, got {got}"
        );
        // The raw solver text is preserved in the note for audit (F-2 keeps the
        // signature readable even once the label reads `oom`).
        assert!(
            note.to_lowercase().contains(&msg.to_lowercase()),
            "classifier: note for {msg:?} must retain the raw solver text, got {note:?}"
        );
    }
    // `unknown` is its own first-class outcome, not oom/encode_error.
    let (got, _) = classify_err(&Error::SolverUnknown);
    assert_eq!(got, SolveOutcome::Unknown, "classifier: SolverUnknown => Unknown");
    println!(
        "# selftest OK: classifier table ({} solver cases + unknown) — mem-cap kills (bad_alloc, status:None) => oom, genuine errors => encode_error",
        solver_cases.len()
    );
}

async fn selftest() {
    // (0) Classifier table (F-2): `classify_err` is deterministic over the
    // solver error string, so exercise it without a real solver. Both the
    // graceful `std::bad_alloc` AND the abrupt mem-cap kill ("terminated
    // unexpectedly with status: None", the RLIMIT_AS/OOM-killer signature at
    // N=192) must classify `Oom`; a genuine encoder/solver message must stay
    // `EncodeError`; `unknown` must stay `Unknown`.
    classifier_table_selftest();

    // (1) Timeout is first-class: a tiny timeout on a real query yields Timeout.
    let case = &set_size_cases(8)[0];
    let c = compile_case(case);
    let smt = capture_smt(case.verb, &c).await.expect("smt");
    assert!(encoding_facts(&smt).has_set_filter, "selftest: set.filter present");
    let mut compiler = CedarSymCompiler::new(local_solver().expect("cvc5")).expect("compiler");
    let (outcome, _ms, _n) = solve(&mut compiler, case.verb, &c, Duration::from_millis(1)).await;
    let _ = compiler.solver_mut().clean_up().await;
    assert_eq!(outcome, SolveOutcome::Timeout, "selftest: 1ms timeout must classify Timeout, got {outcome}");

    // (2) Every family validates + compiles + is non-vacuous (quantified rows).
    let mut quantified = 0usize;
    for case in assemble_cases(true, &full_sizes()) {
        let c = compile_case(&case);
        if case.dims.shape == Shape::Quantified {
            let smt = capture_smt(case.verb, &c).await.expect("smt");
            assert!(
                encoding_facts(&smt).has_set_filter,
                "selftest: family {}/{} must be non-vacuous",
                case.dims.dimension, case.dims.point
            );
            quantified += 1;
        }
    }
    assert!(quantified > 0, "selftest: must have >0 quantified families");

    // (3) Baseline is a fair comparand: for N=4 always_allows, quantified and
    // baseline return the same verdict.
    let mut compiler = CedarSymCompiler::new(local_solver().expect("cvc5")).expect("compiler");
    let cs = set_size_cases(4);
    let cq = compile_case(&cs[0]);
    let cb = compile_case(&cs[1]);
    let (oq, _, _) = solve(&mut compiler, cs[0].verb, &cq, SMOKE_TIMEOUT).await;
    let (ob, _, _) = solve(&mut compiler, cs[1].verb, &cb, SMOKE_TIMEOUT).await;
    let _ = compiler.solver_mut().clean_up().await;
    assert_eq!(
        oq, ob,
        "selftest: baseline must share the quantified verdict for N=4 (got q={oq} b={ob})"
    );

    println!("# selftest OK: timeout first-class, {quantified} quantified families non-vacuous, baseline fair (N=4 verdict {oq})");
}

// ===========================================================================
// Sweep driver (P7 + D-87 budget)
// ===========================================================================

#[allow(clippy::too_many_arguments)]
async fn run_sweep(mode: &str, full: bool, sizes: Vec<usize>, timeout: Duration, max_wall_secs: u64, repeats: u32) -> BenchReport {
    let cases = assemble_cases(full, &sizes);
    let mut results = Vec::new();
    let mut compiler = CedarSymCompiler::new(local_solver().expect("cvc5")).expect("compiler");
    let wall_start = Instant::now();
    let mut budget_exhausted = false;

    'outer: for case in &cases {
        for _rep in 0..repeats {
            if max_wall_secs != 0 && wall_start.elapsed().as_secs() >= max_wall_secs {
                budget_exhausted = true;
                eprintln!(
                    "# wall budget {max_wall_secs}s exhausted after {} rows; stopping cleanly",
                    results.len()
                );
                break 'outer;
            }
            let r = run_case(&mut compiler, case, timeout).await;
            eprintln!(
                "# [{:>5}s] {}/{} {} {} -> {} ({} ms)",
                wall_start.elapsed().as_secs(),
                r.dimension, r.point, r.shape, r.verb, r.outcome, r.solve_ms
            );
            results.push(r);
            // Restart the solver each query to avoid cross-query state growth.
            let _ = compiler.solver_mut().clean_up().await;
            compiler = CedarSymCompiler::new(local_solver().expect("cvc5")).expect("compiler");
        }
    }
    let _ = compiler.solver_mut().clean_up().await;

    let meta = RunMeta {
        cvc5_version: cvc5_version(),
        cedar_sdk_version: cedar_policy::get_sdk_version().to_string(),
        cedar_spec_sha: git_sha(concat!(env!("CARGO_MANIFEST_DIR"), "/../..")),
        cedar_sha: git_sha(concat!(env!("CARGO_MANIFEST_DIR"), "/../../cedar")),
        seed: SEED,
        per_query_timeout_secs: timeout.as_secs(),
        max_wall_secs,
        mem_cap_bytes: 1024 * 1024 * 1024,
        pathway: PATHWAY.to_string(),
        host_cpus: std::thread::available_parallelism().map(|n| n.get()).unwrap_or(0),
        host_mem_kb: host_mem_kb(),
        mode: mode.to_string(),
        repeats,
        budget_exhausted,
        rows: results.len(),
    };
    BenchReport { meta, results }
}

// ===========================================================================
// main
// ===========================================================================

fn arg_val(args: &[String], flag: &str) -> Option<String> {
    args.iter().position(|a| a == flag).and_then(|i| args.get(i + 1).cloned())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");

    // --summarize <path>: read a report JSON and print the summary.
    if let Some(path) = arg_val(&args, "--summarize") {
        let body = fs::read_to_string(&path).expect("read results json");
        let report: BenchReport = serde_json::from_str(&body).expect("parse results json");
        print!("{}", summarize(&report));
        return;
    }

    if args.iter().any(|a| a == "--selftest") {
        rt.block_on(selftest());
        return;
    }

    let full = args.iter().any(|a| a == "--full");
    let format = arg_val(&args, "--format").unwrap_or_else(|| "json".into());
    let out = arg_val(&args, "--out");
    let max_wall_secs = arg_val(&args, "--max-wall-secs")
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(if full { DEFAULT_FULL_WALL_SECS } else { 0 });
    let repeats = arg_val(&args, "--repeats")
        .and_then(|v| v.parse::<u32>().ok())
        .unwrap_or(if full { 3 } else { 1 });
    let (mode, mut sizes, timeout) = if full {
        ("full", full_sizes(), FULL_TIMEOUT)
    } else {
        ("smoke", smoke_sizes(), SMOKE_TIMEOUT)
    };
    // `--sizes 1,2,...,N` overrides the set-size axis (the D-87 paper-scale knob
    // for pushing toward the cliff). Only the set-size dimension honours it.
    if let Some(spec) = arg_val(&args, "--sizes") {
        let parsed: Vec<usize> = spec
            .split(',')
            .filter_map(|t| t.trim().parse::<usize>().ok())
            .collect();
        if !parsed.is_empty() {
            sizes = parsed;
        }
    }

    let report = rt.block_on(run_sweep(mode, full, sizes, timeout, max_wall_secs, repeats));

    // Hard non-vacuity gate: every quantified row recorded must be a real
    // `set.filter` query.
    let bad = report
        .results
        .iter()
        .filter(|r| r.shape == Shape::Quantified && !r.encoding_has_set_filter)
        .count();
    assert_eq!(bad, 0, "{bad} quantified rows were vacuous (no set.filter)");

    write_output(&report, &format, out.as_deref());

    // Always print a short summary to stderr so a smoke run shows something.
    eprint!("{}", summarize(&report));
}
