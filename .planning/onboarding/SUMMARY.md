# openGSD Onboarding Summary — `bil`

## 1. Assimilated Baseline (`v0.1.0`)
- **Repository**: `/home/bill/src/lang/bil`
- **Core Modules**:
  - `src/lexer.rs`, `src/ast.rs`, `src/parser.rs`: Dual ASCII/Unicode parser for OntoLogic, FOL, GCL, and `|>` pipelines.
  - `src/ontology.rs`: BFO `concept` DAG cycle detector, field inheritance resolver, and `.logic` importer.
  - `src/types.rs`: Hindley-Milner type inference with nominal `concept` subtyping and ADT exhaustiveness.
  - `src/wp.rs`: Dijkstra Weakest Precondition (`wp`) & Refinement Calculus (`refines`) verifier.
  - `src/model_check.rs`: Explicit-state BFS model checker for nondeterministic `system` blocks.
  - `src/verus.rs`: Verus (`verus! { ... }`) Rust codegen backend (`bil emit-verus`).
  - `src/eval.rs`: Tree-walk interpreter with reproducible seeded nondeterminism and relational pipelines.

## 2. Generated openGSD Artifacts
- `.planning/codebase/` (`STACK.md`, `INTEGRATIONS.md`, `ARCHITECTURE.md`, `STRUCTURE.md`, `CONVENTIONS.md`, `TESTING.md`, `CONCERNS.md`)
- `.planning/PROJECT.md`
- `.planning/REQUIREMENTS.md`
- `.planning/ROADMAP.md`
- `.planning/STATE.md`
- `.planning/config.json`

## 3. Recommended Next Command
- Execute **Phase 1: Multi-Level IR (`HIR` $\to$ `VIR` $\to$ `LIR`)** via `/gsd-plan-phase 1` or direct implementation.
