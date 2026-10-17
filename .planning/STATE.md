# Project State (`bil`)

- **Current Milestone**: `v0.2` (Multi-Level IR, Unbounded Verification & Native Compiler)
- **Completed Milestone**: `v0.1` (Core Language, OntoLogic DAG, HM Types, Dijkstra WP + Refinement, Model Checker, Verus Backend, Tree-Walk Interpreter)
- **Active Phase**: Ready to plan & execute **Phase 1: Multi-Level Intermediate Representation (`HIR` -> `VIR` -> `LIR`)**
- **Test Status**: 8/8 integration tests passing (`cargo test`), 0 warnings.

## Immediate Next Actions
1. Run `/gsd-plan-phase 1` (or begin Phase 1 implementation directly) to build `src/ir/{hir.rs, vir.rs, lir.rs}` and `bil dump-ir`.
2. Connect `wp.rs`, `model_check.rs`, and `verus.rs` to consume `VIR` and `eval.rs` / native codegen to consume Ghost-Erased `LIR`.
