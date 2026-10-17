# Stack (`bil`)

## Language & Runtime
- **Host Language**: Rust (Edition 2021, `cargo`)
- **Crate Type**: Dual Library (`src/lib.rs`) + CLI Binary (`src/main.rs`)
- **Runtime Dependencies**: `serde` (`1.0`, `derive`), `serde_json` (`1.0`) — zero heavy C/C++ external build chains

## Subsystems
- **Frontend**: Custom zero-dependency Lexer (`src/lexer.rs`) + Recursive Descent & Pratt Parser (`src/parser.rs`) supporting dual ASCII and Unicode mathematical notation (`∀`, `∃`, `⇒`, `⇔`, `∧`, `∨`, `¬`, `▯`, `→`, `⊑`, `▷`).
- **Ontology Engine**: BFO/OntoLogic DAG hierarchy validator and `.logic` S-expression transpiler (`src/ontology.rs`).
- **Type System**: Hindley-Milner (Algorithm W) type inference extended with nominal `concept` subtyping and ADT exhaustiveness (`src/types.rs`).
- **Deductive Verifier**: Dijkstra Weakest Precondition (`wp`) calculus & Refinement Calculus (`refines`) verification condition generator + bounded solver (`src/wp.rs`).
- **Model Checker**: SPIN/Promela-style explicit-state BFS model checker (`src/model_check.rs`).
- **Verus Codegen**: Provably correct Rust (`verus! { ... }`) emitter (`src/verus.rs`).
- **Interpreter**: Tree-walk evaluator with seeded reproducible nondeterminism and functional query pipelines (`src/eval.rs`).
