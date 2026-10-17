# Project State (`bil`)

- **Current Milestone**: `v0.2` (Multi-Level IR, Unbounded Verification & Native Compiler)
- **Completed Phases**:
  - `v0.1` Baseline (Lexer/Parser, OntoLogic DAG, HM Types, Dijkstra WP + Refinement, Model Checker, Verus Backend, Tree-Walk Interpreter)
  - `v0.2 Phase 1` (3-Level IR: `src/ir/{hir.rs, vir.rs, lir.rs}` + `bil dump-ir`)
- **Active Phase**: Ready for **Phase 2: SMT-LIB2 Backend & Verus `spec`/`proof`/`exec` Stratification**
- **Test Status**: 9/9 integration tests passing (`cargo test`), 0 warnings.

## Immediate Next Actions
1. Execute **Phase 2**: Implement `src/smt.rs` (SMT-LIB2 emitter & optional Z3 solver driver from `VIR`) and explicit `proof` blocks.
2. Execute **Phase 3**: Add Linear Temporal Logic (`always` / `eventually` / `leads_to`) to `src/model_check.rs`.
3. Execute **Phase 4**: Implement `bil build <file.bil> -o <bin>` native executable compiler from Ghost-Erased `LIR`.
