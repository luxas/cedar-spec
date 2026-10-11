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
//! This binary measures how cvc5 actually scales on the `.all`/`.any` set
//! quantifier encoding (the D-52 two-`set.filter` `HO_ALL` comprehension),
//! across the req-5.4 dimensions: solve wall-time, outcome
//! (sat/unsat/unknown/timeout/oom), and SMT term size. Decidability (Phase 5B)
//! is not tractability — this quantifies the practical envelope, i.e. the
//! RFC 0021 performance drawback.
//!
//! It is a normal `main()` (NOT a libfuzzer target): it runs a fixed,
//! parameterized sweep, not a byte-stream fuzz loop. It is
//! `required-features = ["anyall"]` + `bench=false,test=false,doc=false`, so a
//! plain `cargo test` / `cargo build` never compiles or runs it (mirrors the
//! `symcc-check-*-ok` bins). See
//! `.kiro/specs/anyall-set-operators/branches/phase8-anyall-cvc5-benchmarks/PLAN.md`.
//!
//! LOAD-BEARING MEASUREMENT CONSTRAINT (D-68 / D-P8-nonvac): every benchmarked
//! policy MUST use a SYMBOLIC receiver (a `context`/entity set attribute whose
//! value is an SMT unknown). A literal-set receiver folds at compile time and
//! emits no `set.filter` term — measuring the Rust folder, not cvc5. Before any
//! row is timed, the harness serializes the compiled asserts to SMT-LIB and
//! asserts the script contains a `set.filter` term under `(set-logic HO_ALL)`;
//! a folded or rejected policy FAILS the harness rather than being recorded.
//!
//! UN-OPTIMIZED VERBS (D-P8-unopt / D-77): the SymCCOpt path rejects `.all`
//! under the D-74/D-77 interim, so the harness pins the un-optimized check
//! verbs (`check_always_allows`, not `_opt`) and records `pathway=unopt`.

// The un-optimized `WellTypedPolicies` + `check_*` verbs are `#[deprecated]` in
// favour of the `CompiledPolicySet` (`_opt`) path, but that path rejects `.all`
// under the D-77 interim — the whole point of this harness is to pin the un-opt
// path that still accepts the quantifier. So deprecation is expected here.
#![allow(deprecated)]

use std::fmt::Display;
use std::mem;
use std::time::Instant;

use cedar_drt_inner::symcc::local_solver;
use cedar_policy::{PolicySet, RequestEnv, Schema, Validator};
use cedar_policy_symcc::{
    err::Error,
    solver::WriterSolver,
    CedarSymCompiler, SymEnv, WellTypedPolicies,
};

/// The analysis pathway every row records: the un-optimized check verbs, which
/// are the only ones that accept `.all` under the D-77 interim.
const PATHWAY: &str = "unopt";

/// Build a `Schema` from Cedar schema text, panicking on parse failure.
fn schema_from_cedarstr(src: &str) -> Schema {
    Schema::from_cedarschema_str(src)
        .unwrap_or_else(|e| panic!("schema should parse: {e}"))
        .0
}

/// Parse + strict-validate a policy set, panicking on parse/validation failure.
fn pset_from_text(text: &str, validator: &Validator) -> PolicySet {
    let pset: PolicySet = text
        .parse()
        .unwrap_or_else(|e| panic!("policy set should parse: {e}"));
    let res = validator.validate(&pset, cedar_policy::ValidationMode::Strict);
    assert!(
        res.validation_passed(),
        "policy set should validate (Strict): {:?}",
        res.validation_errors().collect::<Vec<_>>()
    );
    pset
}

/// A request env + its symbolic environment, built from a schema.
struct Envs {
    req_env: RequestEnv,
    symenv: SymEnv,
}

impl Envs {
    fn new(schema: &Schema, principal_ty: &str, action: &str, resource_ty: &str) -> Self {
        let req_env = RequestEnv::new(
            principal_ty.parse().expect("principal type should parse"),
            action.parse().expect("action euid should parse"),
            resource_ty.parse().expect("resource type should parse"),
        );
        let symenv = SymEnv::new(schema, &req_env).expect("SymEnv::new should succeed");
        Self { req_env, symenv }
    }
}

/// Capture the SMT-LIB script that the UN-OPTIMIZED `check_always_allows` verb
/// emits for `pset` over `symenv`, WITHOUT a real solver.
///
/// A `WriterSolver` records every SMT-LIB command into a buffer and answers
/// `check-sat` with `unknown`, so the un-opt verb runs its full encode (set
/// logic + asserts + `check-sat`) and then returns `Err(SolverUnknown)` — the
/// buffer then holds the complete script, including `(set-logic HO_ALL)` and the
/// `set.filter` comprehension when the receiver is symbolic. This is the un-opt
/// analogue of `symcc.rs::smtlib_of_check_asserts` (which is the opt path and
/// would hit the D-77 `.all` rejection).
async fn smtlib_of_always_allows(typed: &WellTypedPolicies, symenv: &SymEnv) -> Result<String, String> {
    let mut compiler = CedarSymCompiler::new(WriterSolver { w: Vec::<u8>::new() })
        .map_err(|e| format!("WriterSolver compiler construction failed: {e}"))?;
    let res = compiler.check_always_allows(typed, symenv).await;
    match res {
        // `WriterSolver` always answers `unknown`, surfaced as `SolverUnknown`;
        // a real `Ok(_)` would also leave the script in the buffer.
        Ok(_) | Err(Error::SolverUnknown) => {
            Ok(String::from_utf8(mem::take(&mut compiler.solver_mut().w))
                .expect("emitted SMT-LIB should be valid UTF-8"))
        }
        Err(e) => Err(format!("un-opt encode of `.all` failed: {e}")),
    }
}

/// A `set.filter` term present under `(set-logic HO_ALL)` is the fingerprint of
/// a genuine symbolic `.all` query (D-52 encoding), i.e. the receiver did NOT
/// fold (D-68) and the policy was NOT rejected (D-70/D-77). Returns the two
/// facts so a caller can assert both and record the result on the row.
fn encoding_facts(smtlib: &str) -> EncodingFacts {
    EncodingFacts {
        has_set_filter: smtlib.contains("set.filter"),
        has_ho_all: smtlib.contains("(set-logic HO_ALL)") || smtlib.contains("HO_ALL"),
        smt_bytes: smtlib.len(),
    }
}

#[derive(Debug, Clone, Copy)]
struct EncodingFacts {
    has_set_filter: bool,
    has_ho_all: bool,
    smt_bytes: usize,
}

/// Outcome of a single solver query. First-class non-sat outcomes land in P2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    /// `check_always_allows` returned `true` (property holds; the negated query
    /// is unsat).
    Holds,
    /// `check_always_allows` returned `false` (a counterexample exists; the
    /// negated query is sat).
    HasCounterexample,
}

impl Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Outcome::Holds => "holds(unsat)",
            Outcome::HasCounterexample => "has_cex(sat)",
        };
        f.write_str(s)
    }
}

/// One benchmarked query result (P1 shape; extended with full `Dims`/term-size
/// in P2+).
#[derive(Debug, Clone)]
struct Row {
    label: String,
    verb: &'static str,
    pathway: &'static str,
    outcome: Outcome,
    solve_ms: u128,
    encoding_has_set_filter: bool,
    encoding_has_ho_all: bool,
    smt_bytes: usize,
}

impl Display for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "label={label} verb={verb} pathway={pathway} outcome={outcome} \
             solve_ms={solve_ms} encoding_has_set_filter={sf} encoding_has_ho_all={ho} \
             smt_bytes={bytes}",
            label = self.label,
            verb = self.verb,
            pathway = self.pathway,
            outcome = self.outcome,
            solve_ms = self.solve_ms,
            sf = self.encoding_has_set_filter,
            ho = self.encoding_has_ho_all,
            bytes = self.smt_bytes,
        )
    }
}

/// Run the smallest symbolic `.all` query (`context.ports.all(it > 0)`) through
/// the un-opt `check_always_allows` verb against cvc5, after asserting the
/// emitted SMT is a real `set.filter`/`HO_ALL` comprehension (D-P8-nonvac).
async fn run_smallest_always_allows() -> Row {
    let schema = schema_from_cedarstr(
        r#"
        entity User;
        entity Thing;
        action view appliesTo {
          principal: [User],
          resource: [Thing],
          context: { ports: Set<Long> }
        };
        "#,
    );
    let validator = Validator::new(schema.clone());
    // A symbolic receiver: `context.ports` is an SMT unknown Set<Long>, so the
    // `.all` compiles to the real two-`set.filter` HO_ALL term (no D-68 fold).
    let pset = pset_from_text(
        r#"permit(principal, action, resource) when { context.ports.all(it > 0) };"#,
        &validator,
    );
    let envs = Envs::new(&schema, "User", "Action::\"view\"", "Thing");
    let typed = WellTypedPolicies::from_policies(&pset, &envs.req_env, &schema)
        .expect("symbolic `.all` policy should type-check");

    // --- D-P8-nonvac: assert cvc5 is really invoked on a `set.filter` term ---
    let smtlib = smtlib_of_always_allows(&typed, &envs.symenv)
        .await
        .expect("un-opt `.all` should encode to SMT-LIB");
    let facts = encoding_facts(&smtlib);
    assert!(
        facts.has_set_filter,
        "non-vacuity: emitted SMT must contain a `set.filter` term (receiver folded? \
         policy rejected?); script:\n{smtlib}"
    );
    assert!(
        facts.has_ho_all,
        "non-vacuity: emitted SMT must use `(set-logic HO_ALL)`; script:\n{smtlib}"
    );

    // --- time ONLY the solver verb ---
    let mut compiler = CedarSymCompiler::new(local_solver().expect("cvc5 LocalSolver"))
        .expect("CedarSymCompiler over LocalSolver should construct");
    let start = Instant::now();
    let holds = compiler
        .check_always_allows(&typed, &envs.symenv)
        .await
        .expect("cvc5 should decide the symbolic `.all` query under HO_ALL, not error");
    let solve_ms = start.elapsed().as_millis();
    // Reap the solver subprocess.
    let _ = compiler.solver_mut().clean_up().await;

    Row {
        label: "context.ports.all(it > 0) :: always_allows".to_string(),
        verb: "check_always_allows",
        pathway: PATHWAY,
        outcome: if holds {
            Outcome::Holds
        } else {
            Outcome::HasCounterexample
        },
        solve_ms,
        encoding_has_set_filter: facts.has_set_filter,
        encoding_has_ho_all: facts.has_ho_all,
        smt_bytes: facts.smt_bytes,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let smoke = args.iter().any(|a| a == "--smoke");
    if !smoke {
        // P1 only wires `--smoke`; the full sweep (`--full`) and the other CLI
        // modes land in later items. Default to smoke so a bare invocation does
        // something useful and non-vacuous.
    }

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio current-thread runtime");

    let wall_start = Instant::now();
    let row = rt.block_on(run_smallest_always_allows());
    let wall = wall_start.elapsed();

    println!("# anyall cvc5 benchmark — P1 smoke (one symbolic `.all` row)");
    println!("{row}");
    println!(
        "# rows=1 wall_secs={:.3} (non-vacuity: set.filter present = {})",
        wall.as_secs_f64(),
        row.encoding_has_set_filter
    );

    // Hard non-vacuity gate at the process boundary too, so a misbuilt query
    // fails the run rather than printing a vacuous success.
    assert!(
        row.encoding_has_set_filter,
        "every recorded row must be a real symbolic `set.filter` query"
    );
}
