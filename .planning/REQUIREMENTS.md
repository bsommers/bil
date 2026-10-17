# Requirements (`bil` v0.2 Milestone — Multi-Level IR, SMT/Verus Proof Engine & Native Compiler Backend)

## Completed Baseline (v0.1 — Shipped & Verified)
- [x] **REQ-001**: Dual ASCII/Unicode Lexer & Recursive Descent / Pratt Parser (`lexer.rs`, `parser.rs`).
- [x] **REQ-002**: OntoLogic BFO `concept` hierarchy with DAG circular inheritance linter and `.logic` S-expression importer (`ontology.rs`).
- [x] **REQ-003**: Hindley-Milner (Algorithm W) type inference with nominal `concept` subtyping (`<:`) and ADT `match` exhaustiveness (`types.rs`).
- [x] **REQ-004**: Dijkstra Weakest Precondition (`wp`) & Refinement Calculus (`refines`) verifier (`wp.rs`).
- [x] **REQ-005**: Explicit-State BFS Model Checker for nondeterministic `system` blocks (`model_check.rs`).
- [x] **REQ-006**: Verus (`verus! { ... }`) Rust codegen backend (`verus.rs`) and Tree-Walk Interpreter (`eval.rs`).

## Active Milestone Requirements (v0.2)

### Phase 1: 3-Level Intermediate Representation (`HIR` $\to$ `VIR` $\to$ `LIR`)
- [x] **REQ-101 (`HIR`)**: High-Level Ontology & Typed Logic IR — flatten inherited `concept` fields, desugar `|>` pipelines and `_` partial applications into explicit closures, and annotate all nodes with resolved Hindley-Milner types.
- [x] **REQ-102 (`VIR`)**: Verification & Guarded Transition IR (Verus-style `spec` / `proof` / `exec` modes) — canonical representation of proof obligations, `requires`/`ensures`, `invariant`/`variant`, and nondeterministic guarded transitions (`[]`, `choose`).
- [x] **REQ-103 (`LIR`)**: Low-Level SSA / Control & Dataflow IR — perform Ghost Erasure (stripping `spec`, `axiom`, `invariant`, `variant` after verification) and lower GCL `if..fi` / `do..od` into deterministic basic-block control flow.

### Phase 2: Unbounded SMT-LIB2 / Z3 & Enhanced Verus Verification
- [ ] **REQ-201**: Emit standard SMT-LIB2 queries from `VIR` Verification Conditions and optionally invoke `z3` / `cvc5` for unbounded mathematical proof discharge alongside the built-in finite-domain solver.
- [ ] **REQ-202**: Support explicit Verus-inspired `spec fn`, `proof { ... }` lemma blocks, and lock/resource invariants in `.bil` syntax and `bil emit-verus`.

### Phase 3: LTL Temporal Model Checking & Fairness
- [ ] **REQ-301**: Add Linear Temporal Logic operators (`always` / `□`, `eventually` / `◇`, `leads_to` / `~>`) and weak/strong fairness constraints to `system` blocks in `model_check.rs`.

### Phase 4: Compiler Backend (Native Rust/LLVM & Bytecode VM)
- [ ] **REQ-401**: Compile Ghost-Erased `LIR` to standalone native executables via `rustc` (leveraging `rustc`'s LLVM backend with zero `unsafe` C++ FFI dependencies) via `bil build <file.bil> -o <bin>`.
- [ ] **REQ-402**: Compile `LIR` to a fast register-based bytecode VM for high-throughput tabular/JSON pipeline execution.
