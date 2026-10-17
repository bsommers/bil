# Changelog

All notable changes to **`bil` (Bounded Invariant Logic)** will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
