# Technical Concerns & Next Architectural Frontiers (`bil`)

1. **Direct AST Lowering vs. Multi-Level IR**:
   - Currently `wp.rs`, `model_check.rs`, `verus.rs`, and `eval.rs` operate directly over the surface `ast::Program`. Introducing the 3-level IR (`HIR` -> `VIR` -> `LIR`) in Milestone v0.2 will eliminate duplicate substitution/desugaring logic and enable ghost erasure before code generation.
2. **Bounded Domain Solver vs. Unbounded SMT-LIB2 / Z3**:
   - `wp.rs` currently discharges Verification Conditions via symbolic substitution + bounded finite-domain counterexample search. Connecting `VIR` to an SMT-LIB2 (Z3/CVC5) process pipe alongside `verus` will provide unbounded mathematical proof discharge.
3. **Liveness / Temporal Properties in Model Checker**:
   - `model_check.rs` currently checks safety invariants, deadlock freedom ($\neg BB$), and strict `variant` decrease. Adding nested DFS / SCC cycle detection for general Linear Temporal Logic (`eventually` / `leads_to` under fairness) is planned for Phase 3.
