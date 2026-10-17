# Integrations (`bil`)

## 1. OntoLogic Ecosystem (`/home/bill/src/OntoLogic`)
- **Integration**: `bil import-ontologic <file.logic>` (`src/ontology.rs::transpile_ontologic_sexpr`)
- **Direction**: Ingests S-expression `.logic` files (`def-concept`, `def-property`, `forall`, `exists`, `implies`, `and`, `or`, `not`) and transpiles them into native `.bil` `concept` hierarchies and `axiom` declarations.

## 2. Verus Deductive Rust Verifier (`https://github.com/verus-lang/verus`)
- **Integration**: `bil emit-verus <file.bil>` (`src/verus.rs::emit_verus_rust`)
- **Direction**: Compiles checked and WP-verified `.bil` programs into `verus! { ... }` Rust modules (`vstd::prelude::*`), mapping `concept` to `#[derive(Structural)] pub struct`, `axiom` and `spec` to `pub open spec fn`, GCL `if..fi` to `proof { assert(BB); }` guarded branches, `do..od` to `while` loops with `invariant` and `decreases`, and `system` blocks to state-machine structs with inductive `invariant(&self)` predicates.

## 3. Planned Backends (v0.2 Roadmap)
- **SMT-LIB2 / Z3**: Discharge unbounded `VIR` verification conditions via standard SMT-LIB2 pipes.
- **Multi-Level IR (`HIR` -> `VIR` -> `LIR`)**: Lowering `LIR` to native binaries via `rustc`/Verus and bytecode/Cranelift JIT.
