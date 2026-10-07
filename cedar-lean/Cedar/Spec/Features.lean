/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

namespace Cedar.Spec

/--
Feature marker for the non-nested `.any`/`.all` set operators
(spec: `anyall-set-operators`).

Lean has no conditional-compilation mechanism analogous to Rust's
`#[cfg(feature = "anyall")]`, so the *real* gate for this feature is structural:
until the `.all` constructor is added to `Expr` (Phase 2), the Lean spec simply
cannot represent an `all` node, and the differential-testing harness only ever
feeds the Lean spec an `all` node when the Rust `anyall` Cargo feature is enabled
(the generator arm is gated on it, Phase 6). This boolean exists as an explicit,
documented marker of that intent and as a single toggle other Lean code may branch
on if a runtime guard is ever wanted. It is `false` and inert in Phase 0.
-/
public def anyAll : Bool := false

end Cedar.Spec
