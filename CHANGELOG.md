# Changelog

All notable changes to **`bil` (Bounded Invariant Logic)** will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [v0.3.0] - 2026-10-17

### Fixed (P0 Soundness & Correctness)
- **`P0.1` (`src/wp.rs`, `src/smt.rs`)**: Prevent circular self-assumption of `proof` lemmas (only assume previously proved lemmas in declaration order) and detect vacuous/inconsistent `axiom` assumptions prior to obligation verification.
- **`P0.2` (`src/wp.rs`)**: Unify verification verdicts into `ObligationStatus` (`Proved`, `Refuted`, `BoundedOnly`, `Unknown`) via `ProofObligation::decide_status`, ensuring concrete bounded counterexamples always take precedence over inconclusive/spurious solver outputs.
- **`P0.3` (`src/semantics.rs`, `src/eval.rs`, `src/vm.rs`, `src/codegen.rs`)**: Unify 64-bit integer arithmetic across all execution and verification backends with Euclidean division/modulo (`checked_div_euclid`, `checked_rem_euclid`, matching SMT-LIB2 `div`/`mod`) and checked overflow semantics.
- **`P0.4` (`src/wp.rs`)**: Implement capture-avoiding alpha-renaming and complete expression coverage (`LetIn`, `Match`, `List`, `Pipe`, `IfFi`, `DoOd`) in `subst_expr`, and fail closed when bounded obligation evaluation encounters a `RuntimeError`.
- **`P0.5` (`src/model_check.rs`)**: Replace per-queue-entry path cloning with parent-pointer trace reconstruction (`O(1)` memory per visited state) and report `truncated: bool` (`is_complete()`) when `--max-states` is reached.
- **`P0.6` (`src/ir/vir.rs`, `src/wp.rs`)**: Decouple pure VC generation (`generate_program_obligations`) from SMT solver execution during `VIR` lowering (`bil vm`, `bil build`, `bil dump-ir`).

### Changed (P1 Architecture Consolidation)
- **`P1.1` (`src/semantics.rs`, `src/runtime_prelude.rs`)**: Unify runtime unary/binary operator evaluation and pattern matching across `eval` and `vm`, and extract the standalone AOT runtime prelude into compile-tested `src/runtime_prelude.rs`.
- **`P1.2` (`src/builtins.rs`)**: Centralize `BuiltinFn` and `PipeStageBuiltin` metadata, type signatures, runtime evaluation, and SMT-LIB2 lowering.
- **`P1.3` (`src/driver.rs`, `src/cli.rs`)**: Split high-level pipeline driver and CLI command dispatcher out of `src/lib.rs` and `src/main.rs`.
- **`P1.4` (`src/symbol.rs`, `src/error.rs`)**: Add `Symbol`/`SymbolInterner` and structured `BilError` diagnostics with source spans.
- **`P1.5` (`src/smt.rs`, `src/codegen.rs`)**: Support configurable external solver and compiler paths (`BIL_<SOLVER>_PATH`, `BIL_SOLVER_DIR`, `BIL_RUSTC_PATH`, `RUSTC`).

### Security (`SEC-1`–`SEC-5`)
- **`SEC-1` (`src/verus.rs`, `src/codegen.rs`)**: Escape string literals in Verus codegen and sanitize Rust keyword/special identifiers in native AOT codegen (`sanitize_rust_ident`).
- **`SEC-2` (`src/codegen.rs`)**: Use atomic `OpenOptions::create_new(true)` temporary file creation in `compile_native_binary`.
- **`SEC-3` (`src/smt.rs`)**: Add non-blocking pipe reader threads and hard wall-clock timeout (`BIL_SOLVER_TIMEOUT_MS`) killing hung solver subprocesses.
- **`SEC-4` (`src/parser.rs`, `src/ontology.rs`, `src/eval.rs`, `src/vm.rs`)**: Enforce recursion depth limits (`MAX_PARSE_DEPTH = 128`, `MAX_CALL_DEPTH = 64`) and VM instruction fuel (`DEFAULT_VM_MAX_STEPS = 1_000_000`).
- **`SEC-5` (`tests/security.rs`, `tests/soundness.rs`)**: Add dedicated soundness (`6` tests) and security (`5` tests) regression suites.

## [v0.2.0] - 2026-10-17

### Added
- **Phase 1 — 3-Level Intermediate Representation (`src/ir/`)**:
  - `HIR` (`src/ir/hir.rs`): Flattens BFO `concept` inheritance layouts, desugars `|>` pipelines into explicit `PipeStage` nodes, and annotates expressions with resolved Hindley-Milner + subtyping types.
  - `VIR` (`src/ir/vir.rs`): Verus-inspired `ghost(spec)`, `ghost(proof)`, and `exec` mode stratification with verification conditions.
  - `LIR` (`src/ir/lir.rs`): Performs **Ghost Erasure** (stripping `axiom`, `spec`, `proof`, `requires`, `ensures`, `invariant`, and `variant` annotations) and lowers GCL into executable nodes.
  - `bil dump-ir <file.bil> [--level hir|vir|lir|all]` CLI inspection command and `docs/ARCHITECTURE_AND_VERUS.md`.
- **Phase 2 — `OntoLogic` + `clif2OntoLogic` SMT-LIB2 Solver Bridge & Verus `proof` Lemmas (`src/smt.rs`, `src/ontology.rs`)**:
  - Two-pass SMT-LIB2 generator (`(declare-sort Entity 0)`, `subClassOf` partial order, relativized quantifiers) with automatic `Z3` $\to$ `CVC5` $\to$ `Vampire` prover cascade.
  - Static propositional (`P && !P`) and pairwise numeric bound contradiction linter (`x > 100 && x < 50`).
  - Taxonomic subsumption prover (`bil solve <file.bil> --subsumes Child Parent`) and comparative agreement (`Match` / `Disagreement` / `Inconclusive`) between bounded search and unbounded SMT refutation.
  - Explicit Verus-style `proof <name>(...) requires ... ensures ...` ghost lemmas verified by Z3/CVC5 and emitted as `pub proof fn` in `bil emit-verus`.
- **Phase 3 — LTL Temporal Model Checking & Weak Fairness (`src/model_check.rs`)**:
  - Added `temporal <Name>: ...` specifications in `system` blocks supporting `always(P)` ($\square P$), `eventually(Q)` ($\lozenge Q$), and `P ~> Q` / `leads_to(P, Q)` ($\square(P \implies \lozenge Q)$).
  - Tarjan Strongly Connected Component (SCC) decomposition over $\neg Q$-subgraphs with Weak Fairness (Justice) cycle verification and lasso counterexample traces.
- **Phase 4 — Register/Stack Bytecode VM & Standalone Native AOT Compiler (`src/vm.rs`, `src/codegen.rs`)**:
  - `bil vm <file.bil> [--dump-bytecode]`: Compiles Ghost-Erased `LIR` into `BytecodeProgram` instructions and executes on `BytecodeVm`.
  - `bil build <file.bil> [-o <out_bin>]`: Compiles Ghost-Erased `LIR` into standalone native ELF executables via `rustc -O` (LLVM backend).

## [v0.1.0] - 2026-10-17

### Added
- Dual ASCII/Unicode Lexer (`src/lexer.rs`) and Recursive Descent + Pratt Parser (`src/parser.rs`).
- OntoLogic BFO `concept` hierarchy with DAG cycle detection and `.logic` S-expression transpiler (`src/ontology.rs`).
- Hindley-Milner (Algorithm W) type inference with nominal `concept` subtyping (`<:`) and ADT exhaustiveness checking (`src/types.rs`).
- Dijkstra Guarded Command Language (`if ... fi`, `do ... od`), Weakest Precondition (`wp`) calculus, and Formal Refinement (`spec` / `refines`) verifier (`src/wp.rs`).
- Explicit-state BFS model checker for nondeterministic `system` blocks (`src/model_check.rs`).
- Verus (`verus! { ... }`) Rust code generator (`src/verus.rs`) and Tree-Walk Interpreter (`src/eval.rs`).
- Five domain examples (`smart_grid.bil`, `mutex_protocol.bil`, `arbiter_controller.bil`, `gcd_refinement.bil`, `security_policy.bil`).
