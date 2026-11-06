# Project State (`bil`)

Numbering and release mapping: see `.planning/ROADMAP.md`. Milestone N ships as release `v0.N.0`.

- **Current Milestone**: 8 (`v0.8.0`) — released 2026-11-06
- **Released**: Milestones 1 to 8 (`v0.1.0` to `v0.8.0`)
  - 1 (v0.1.0): lexer/parser, OntoLogic, HM types, weakest-precondition verifier, model checker, Verus backend, interpreter
  - 2 (v0.2.0): 3-level IR (`src/ir/`), SMT-LIB2 bridge (`src/smt.rs`), LTL model checking with fairness, bytecode VM, native compiler
  - 3 (v0.3.0): soundness, architecture consolidation, security hardening
  - 4 (v0.4.0): verification depth, performance, symbolic BMC
  - 5 (v0.5.0): strict exit codes, CLI validation, type soundness
  - 6 (v0.6.0): `scripts/ci.sh` gate, SMT counterexample values, hardening
  - 7 (v0.7.0, patch v0.7.1): timed guards, SMT unfolding of user functions, recursion by `variant`, sample budget, `bil emit-verus` refinement of `system` blocks, project site
  - 8 (v0.8.0): in-repo `bil-smt` decision procedure (`src/bil_smt.rs`, `--prover bil-smt`, `--prover auto` fallback), repo-wide differential soundness gate against `z3`, solver-free domain verification
- **Next Milestone**: Phase 8.2 (proof checking, not scheduled). See `docs/SOLVER-CONSIDERATIONS.md` and `docs/SOLVER-MEASUREMENT.md`.
- **Test status**: run `scripts/ci.sh` (clippy `-D warnings`, tests under coverage with a 78% floor, Verus tests when `verus` is installed, `cargo audit`). Figures from the last run are in the release tag message.
