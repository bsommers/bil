# Architecture (`bil`)

## Current v0.1 Pipeline
```mermaid
flowchart LR
    Src[".bil / .logic"] --> Lex["lexer.rs"]
    Lex --> Par["parser.rs (AST)"]
    Par --> Onto["ontology.rs (DAG Linter)"]
    Onto --> Types["types.rs (HM + Subtyping)"]
    Types --> WP["wp.rs (Dijkstra WP + Refinement)"]
    Types --> MC["model_check.rs (BFS State Explorer)"]
    Types --> Verus["verus.rs (verus! Rust Codegen)"]
    Types --> Eval["eval.rs (Tree-Walk + Pipelines)"]
```

## Target v0.2 Multi-Level IR Architecture (`HIR` -> `VIR` -> `LIR`)
```mermaid
flowchart TD
    AST["Surface AST (ast.rs)"] --> HIR["Level 1: HIR (Desugared Pipelines, Flattened OntoLogic Concepts, HM Typed)"]
    HIR --> VIR["Level 2: VIR (Verification & Guarded Transition IR: spec/proof/exec, WP, Model Checking)"]
    VIR -->|Verification Path| Solver["WP Solver / SMT-LIB2 / Model Checker"]
    VIR -->|Ghost Erasure + Determinization| LIR["Level 3: LIR / SSA (Executable Control & Dataflow IR)"]
    LIR --> VerusBackend["Verus / Rustc Native Backend"]
    LIR --> VMBackend["Register Bytecode VM / Cranelift JIT"]
```

## Core Invariants
1. **OntoLogic Taxonomic Acyclicity**: Every `concept` hierarchy must form a strict DAG (`ontology.rs`).
2. **True Nondeterminism (`[]` & `choose`)**: Guards in `if..fi`, `do..od`, and `system` transitions are evaluated without order bias; deductive proofs (`wp.rs`) must hold for *all* enabled guards demonically, and model checking (`model_check.rs`) explores *all* enabled branches.
3. **Total Guard Coverage ($BB$)**: Executing `if..fi` when $\neg(\bigvee G_i)$ is a static `wp` failure and runtime abort.
