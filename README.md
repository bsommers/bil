# `bil` — Bounded Invariant Logic

`bil` is a mathematically grounded, statically typed formal verification, ontology, and functional data language written in Rust. It unifies:

1. **Correctness by Construction (Dijkstra GCL & Refinement Calculus)**:
   - Guarded Command Language (`if ... fi`, `do ... od`) with loop `invariant` and termination `variant` (bound function).
   - Weakest Precondition (`wp`) verification condition generator & bounded solver (`bil verify`).
   - Formal Refinement (`spec` and `refines` / `⊑`), proving concrete implementations satisfy abstract First-Order Logic specifications.
2. **True Nondeterminism (`[]` / `▯` & `choose`)**:
   - Guarded alternatives (`[]`) evaluate all guards simultaneously and choose nondeterministically among enabled branches—verified demonically at proof time and explored exhaustively at model-check time.
   - Nondeterministic selection (`choose x in S : P(x)`) defers implementation details in high-level designs.
3. **Foundation for Formal Methods (`system` & Explicit-State Model Checking)**:
   - Reactive concurrent state machines (`system`) with `state`, `invariant`, `variant`, `terminal`, and interleaved guarded `transition` blocks (SPIN / Promela style).
   - Exhaustive BFS state-space explorer (`bil model-check`) checking safety invariants, deadlock freedom ($\neg BB$), and progress variants with shortest-path counterexample traces.
4. **OntoLogic Taxonomies, First-Order Logic & Functional Pipelines**:
   - BFO-compatible `concept` hierarchies (`<:`) with compile-time DAG cycle linting and nominal subtyping inside Hindley-Milner type inference.
   - Dual ASCII / Unicode logical syntax (`forall`/`∀`, `exists`/`∃`, `=>`/`⇒`, `<=>`/`⇔`, `&&`/`∧`, `||`/`∨`, `!`/`¬`, `[]`/`▯`, `|>`/`▷`).
   - Built-in `.logic` S-expression importer (`bil import-ontologic <file.logic>`).

---

## CLI Usage

```bash
cargo run -- check <file.bil>                    # OntoLogic DAG + contradiction linter + HM typechecker
cargo run -- solve <file.bil> [--subsumes C P]   # Z3/CVC5 SMT-LIB2 ontology consistency & subsumption prover
cargo run -- verify <file.bil> [--allow-bounded] # Dijkstra WP, Refinement & Verus proof verifier (Bounded + Z3); exits 1 on bounded-only obligations unless --allow-bounded
cargo run -- model-check <file.bil>              # Explicit-state + LTL temporal (`~>`, `eventually`) model checker
cargo run -- run <file.bil> [--seed N] [--trace] # Tree-walk interpreter with nondeterministic trace
cargo run -- vm <file.bil> [--dump-bytecode]     # Execute Ghost-Erased LIR on the Register/Stack Bytecode VM
cargo run -- build <file.bil> [-o <out_bin>]     # Compile Ghost-Erased LIR to a standalone native ELF binary
cargo run -- dump-ir <file.bil> [--level all]    # Inspect 3-Level IR (HIR -> VIR -> LIR)
cargo run -- emit-verus <file.bil>               # Emit Verus Rust verification code (`verus! { ... }`)
cargo run -- import-ontologic <file.logic>       # Transpile OntoLogic .logic files into .bil
cargo run -- all <file.bil> [--seed N] [--trace] # Run check + verify + model-check + run
cargo run -- repl                                # Interactive REPL
```

## Local CI

There is no hosted CI. Run the gate before pushing:

```bash
scripts/ci.sh              # clippy -D warnings, tests under coverage (75% line floor), cargo audit
scripts/ci.sh --fuzz 300   # also fuzz lex/parse/check for 300 s each (nightly + cargo-fuzz)
git config core.hooksPath .githooks   # optional: run scripts/ci.sh automatically on git push
```

Requires `cargo-llvm-cov`, `cargo-audit` and z3 (on `PATH` or in `~/.local/bin`).

## Practical Application Examples (`examples/`)

- [`examples/smart_grid.bil`](examples/smart_grid.bil) — **Industrial IoT & Smart Energy**: BFO `concept` hierarchy, FOL `axiom`s, WP-verified nondeterministic pressure-bleed `do ... od` controller, and `|>` telemetry pipelines.
- [`examples/mutex_protocol.bil`](examples/mutex_protocol.bil) — **Distributed Protocols**: Peterson's mutual exclusion protocol verified for safety and deadlock freedom via `bil model-check`.
- [`examples/arbiter_controller.bil`](examples/arbiter_controller.bil) — **Hardware & Digital Controllers**: Dual-channel asynchronous bus arbiter with overlapping nondeterministic request guards and progress `variant`.
- [`examples/gcd_refinement.bil`](examples/gcd_refinement.bil) — **Verified Algorithms & Refinement**: Dijkstra's GCL greatest-common-divisor proved to refine an abstract FOL specification (`refines gcd_spec`).
- [`examples/security_policy.bil`](examples/security_policy.bil) — **Zero-Trust Cloud Policy Auditing**: FOL compliance axioms and nondeterministic failover selection (`choose`).
