# Structure (`bil`)

```text
/home/bill/src/lang/bil/
├── Cargo.toml                  # Rust package manifest
├── README.md                   # Quickstart, CLI usage, and examples overview
├── src/
│   ├── lib.rs                  # Public compiler/verifier/interpreter API
│   ├── main.rs                 # CLI entrypoint (check, verify, model-check, run, all, emit-verus, import-ontologic, repl)
│   ├── lexer.rs                # Dual ASCII/Unicode tokenizer with Span tracking
│   ├── ast.rs                  # Surface AST definitions
│   ├── parser.rs               # Recursive descent + Pratt expression parser
│   ├── ontology.rs             # OntoLogic DAG cycle linter, field inheritance & .logic importer
│   ├── types.rs                # Hindley-Milner (Algorithm W) + nominal concept subtyping & ADT exhaustiveness
│   ├── wp.rs                   # Dijkstra Weakest Precondition (wp) & Refinement Calculus verifier
│   ├── model_check.rs          # Explicit-state BFS model checker for `system` blocks
│   ├── verus.rs                # Verus (`verus! { ... }`) Rust code generator
│   └── eval.rs                 # Tree-walk interpreter, seeded nondeterminism & `|>` query engine
├── examples/
│   ├── smart_grid.bil          # Industrial IoT / BFO ontology + GCL controller + pipelines
│   ├── mutex_protocol.bil      # Peterson's mutual exclusion protocol (model-checked)
│   ├── arbiter_controller.bil  # Asynchronous dual-channel hardware bus arbiter
│   ├── gcd_refinement.bil      # Dijkstra GCL GCD refining abstract FOL spec
│   └── security_policy.bil     # Zero-Trust cloud policy auditing + nondeterministic `choose`
└── tests/
    └── bil_tests.rs            # End-to-end integration test suite
```
