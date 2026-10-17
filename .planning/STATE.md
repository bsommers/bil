# Project State (`bil`)

- **Current Milestone**: `v0.2` (Multi-Level IR, Unbounded Verification, LTL Model Checking & Native Compiler) — **COMPLETED**
- **Completed Phases**:
  - `v0.1` Baseline (Lexer/Parser, OntoLogic DAG, HM Types, Dijkstra WP + Refinement, Model Checker, Verus Backend, Tree-Walk Interpreter)
  - `v0.2 Phase 1` (3-Level IR: `src/ir/{hir.rs, vir.rs, lir.rs}` + `bil dump-ir`)
  - `v0.2 Phase 2` (`OntoLogic` + `clif2OntoLogic` SMT-LIB2 Solver Bridge in `src/smt.rs`, static contradiction linter in `src/ontology.rs`, comparative solver agreement, `bil solve`, and Verus `proof` lemmas)
  - `v0.2 Phase 3` (LTL Temporal Model Checking `always`, `eventually`, `~>` / `leads_to` + Tarjan SCC Weak Fairness verifier in `src/model_check.rs`)
  - `v0.2 Phase 4` (Ghost-Erased Register/Stack Bytecode VM in `src/vm.rs` (`bil vm`) + Standalone Native AOT Executable Compiler via `rustc -O` in `src/codegen.rs` (`bil build`))
- **Test Status**: 15/15 integration tests passing (`cargo test`), 0 warnings.
