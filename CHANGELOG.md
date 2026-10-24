# Changelog

All notable changes to **`bil` (Bounded Invariant Logic)** will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- **Timed guards in `system` blocks.** `clock scan period 1ms` declares a controller's scan period, and `deadline CutOnDetect: detected => !lamp within 3ms in phase == Soak` states that once the latched signal is seen the response must hold within a bound, optionally per phase. A deadline is rounded up to whole scans, and a phase change does not stop a running timer. A pass in `bil::timed` lowers each deadline into a pending flag, a scan counter and two invariants, `Deadline_<name>` and `Latch_<name>` (a latch cleared before the response), which `model-check` and `model-check --bmc` then check. The SMT encoder now treats the two-branch `if g -> a [] !g -> b fi` as `ite`. `examples/domains/semiconductor_se_spe.bil` gains a detect-to-cut-off deadline, and the seeded bug `spe_late_cutoff.bil` misses it. Semantics: `docs/SEMANTICS.md` §4.3.

- **SMT proofs see through calls to user-defined functions.** Before, a contract whose body or clauses called another `fn` could not be encoded for the solver, so it was only sampled (`BOUNDED`). Each call is now unfolded into the callee's body. The query also requires the callee's `requires` and `ensures` (and those of a refined `spec`) at the call site, guarded by the `&&`, `||` and `=>` short-circuits around it, because execution checks them on every call. A call that breaks the callee's precondition is therefore refuted even at values the sampler never tries. Calls nested more than 16 deep are not unfolded, and stay bounded; recursive calls are handled as described next. `examples/domains/process_safety_reactor.bil` now calls `vote_2oo3` instead of inlining it. The seeded bug `reactor_trip_via_call.bil`, which only documented the old limitation, is replaced by `reactor_trip_shared_input.bil`, a voter wiring fault caught through the unfolded call.

- **Recursive functions can be proved by induction.** A `fn` may now declare `variant <Int expr>` after its `ensures`, a measure that every recursive call must keep non-negative and strictly decrease. At a recursive call to such a function, the SMT query no longer gives up: it checks the call's `requires` and the variant decrease, and assumes the function's `ensures` for the call's result, which is the induction hypothesis that the function's own obligation proves. `if … fi` in a function body is now encoded for the solver too, demonically: the obligation must hold for every branch whose guard is true, and at least one guard must be. A recursive function without a `variant` is still only bounded-checked. See `examples/recursive_contracts.bil`. The Verus export emits the variant as `decreases`.

### Fixed
- **Running out of interpreter call depth is no longer a counterexample.** The bounded cross-check samples values such as `n = 800`, and a correct recursive function then hits the interpreter's 64-call limit. That sample is now skipped and not counted, instead of refuting an obligation that SMT proves.

### Changed
- **The bounded cross-check has a sample budget.** It used to evaluate every combination of every parameter's sample values, which grows exponentially: a `do … od` function with a record and four `Int` parameters took 12 seconds in a release build (59 in debug). Up to 10,000 combinations are still all evaluated, in the same order as before, so existing results and counterexamples are unchanged. Above that, `bil` evaluates 10,000 distinct combinations and reports them as `BOUNDED (10000 of 19683 samples)`. They start with a pairwise covering array (built with the IPOG strategy), so every pair of sample values of every two parameters is tried together; a fixed-seed pseudo-random sample fills the rest. When the two largest sample domains alone have more than 10,000 combinations, the sample instead starts with combinations that use every value of every parameter. The same function now verifies in 0.14 seconds. `Status::BoundedOnly` gains a `space` field (also in JSON output); `decide_status_sampled` and `SAMPLE_BUDGET` are new in `bil::wp`.

## [v0.6.0] - 2026-10-23

### Added
- **Local CI gate, `scripts/ci.sh`.** It runs clippy with `-D warnings`, the full test suite under `cargo llvm-cov` with a 78% line-coverage floor (80.7% today), and `cargo audit`. An optional pre-push hook lives in `.githooks/pre-push`. Hosted CI is disabled; this script is the gate.

### Changed
- **Type errors point at the offending subexpression.** Before, every error inside a function body, contract or system member was reported at the enclosing declaration's header (for example `1:1`). It now gives that expression's own line and column: the operator of a binary expression, otherwise the first token. The parser records a span for every expression node in `Program::expr_spans`, in the order of `Program::for_each_expr_postorder`. The `Expr` type itself is unchanged.
- **Counterexamples found only by the SMT solver now show concrete values**, for example `Counterexample: { x = 37 }`, in the same form as bounded counterexamples. Before, they printed just `SMT model: sat`. When a refutation comes back `sat`, `bil` runs the same script again with `(get-model)` on the same solver and renders the constants. If no model is available (Vampire, for example), the old text is kept.

### Fixed
- **The solver timeout now always applies.** `bil` wrote the whole SMT-LIB script to the solver's stdin before starting the timeout clock, so a solver that stopped reading (or any script larger than the 64 KiB pipe buffer sent to one) made `bil` hang forever. The script is now written on a separate thread, and a timed-out solver is killed and reported as Unknown.
- **Substitution no longer captures variables bound by `match` patterns or `do … od` loops.** For example, `match s { Some(y) -> x + y }` with `x := y` used to become `Some(y) -> y + y`, which silently changed the verification condition. Those binders are now renamed to a fresh name first, as quantifier and `let` binders already were.
- **Whole-valued Floats keep their decimal point.** `run`, `vm` and native binaries printed `-3.0` as `-3`, so a Float result could not be told apart from an Int. They now print `-3.0`, as do expression messages and `emit-verus` (where `0.0` used to come out as the integer literal `0`).

### Security
- **Source files over 16 MiB are rejected** (`error: … exceeds maximum size`, exit `1`) instead of being read into memory whole. Before, `bil check /dev/zero` or a multi-gigabyte file kept allocating until it ran out of memory.
- **Native binaries from `bil build` now limit recursion depth and loop steps**, the same way `eval` does: at most 64 nested calls and 100,000 steps per `do … od` loop. Before, runaway recursion crashed the binary with a stack overflow, and a loop that never ended hung it. Both now stop with the same error message as `eval` (Rust panic, exit code `101`).
- **`BIL_RUSTC_PATH` and `RUSTC` overrides are validated.** Surrounding whitespace is trimmed, and a value that names a path must be an existing file. Otherwise `bil build` stops with `BIL_RUSTC_PATH=… is not a file` before writing anything, instead of trying to run it. A bare command name such as `RUSTC=rustc` is still looked up on `PATH`.

## [v0.5.0] - 2026-10-19

### ⚠️ Breaking
- **`bil verify` and `bil all` exit `1` when any obligation is only bounded-checked** (`BoundedOnly`: sampled, never proved by a solver). Previously these counted as passing, so a solver failure plus a sampling miss let a false contract exit `0`. Pass the new **`--allow-bounded`** flag to accept bounded evidence. `examples/gcd_refinement.bil` and `examples/smart_grid.bil` now need it. The library's `ProofObligation::verified` field is unchanged.
- **Unknown CLI options and invalid flag values are now errors** (exit `1`, `error: …` on stderr). Before, they were silently ignored or replaced by defaults: `--bmc abc` ran explicit-state checking instead, `--max-states 1O0` became `50000`, `--prover z4` became `auto`, and typos such as `--jsno` were dropped.

### Fixed (Type Soundness & Backend Parity)
- **`P0.1` (`src/types.rs`)**: Directional subtyping (`actual <: expected`) in `TypeEnv::unify`, contravariant function parameters, and `join_types` via the ontology's common ancestor for lists, `if`/`match` branches, `==`/`!=` and `in`.
- **`P0.2` (`src/types.rs`)**: Numeric and comparable type constraints on arithmetic and relational operators (`%` on `Int`; `- * / < <= > >=` on `Int | Float`; `+` on `Int | Float | Str`).
- **`P0.3` (`src/ir/lir.rs`, `src/vm.rs`, `src/codegen.rs`)**: Top-level `assert` declarations are lowered into LIR and enforced by the bytecode VM and native AOT binaries, not only by `bil run`.

### Added
- **`P1.1` (`src/expr_utils.rs`)**: Extracted `free_vars`, `subst_expr`, `format_expr_concise` and `extract_int_constants` from `wp.rs`, removing the `smt`/`model_check`/`verus` → `wp` dependency.
- **`P1.2` (`src/smt.rs`, `src/wp.rs`)**: Multi-obligation `if..fi` and `do..od` functions are discharged in one incremental `(push 1)`/`(pop 1)` solver session.
- **`P1.3` (`src/runtime_prelude.rs`, `src/codegen.rs`)**: A runtime concept instance store in native AOT binaries, with `is_a` and `choose` support.
- **`P2.1` (`src/driver.rs`, `src/cli.rs`)**: `bil model-check --bmc <k>` / `--bmc=<k>` runs symbolic bounded model checking, with text and `--json` output.
- **Fuzzing (`fuzz/`)**: `cargo-fuzz` targets `lex`, `parse` and `check`. Run them with `cargo +nightly fuzz run <target>`.
- **Tests**: `tests/cli.rs` runs the `bil` binary end to end (exit codes, JSON output, fake solvers that error, crash, print garbage or time out). `tests/soundness.rs` now covers every outcome of `decide_status`. There are now 53 tests, up from 37.

### Changed
- `Cargo.lock` is now committed for reproducible builds and `cargo audit`.
- `graphify-out/` is ignored.

### Documentation
- `docs/TEST_COVERAGE.md`: a `cargo-llvm-cov` baseline (74.2% lines) and a prioritized list of gaps.
- `.security-reports/scan-2026-10-17.md` and `docs/DEPENDENCY_AUDIT.md`: security scan (grade A) and dependency audit (0 advisories).

## [v0.4.0] - 2026-10-17

### Added (P2 Verification Depth & P3 Performance/Architecture)
- **`P2.1` (`src/wp.rs`)**: Constant-guided boundary sampling (`extract_int_constants` probing $c - 1, c, c + 1$ for every literal constant in functions and obligations), ADT/List/skewed multi-field `ConceptInstance` witness generation, and recursive `do ... od` invariant verification under `let` bindings.
- **`P2.2` (`src/semantics.rs`, `src/runtime_prelude.rs`)**: Enforce a `100_000`-element cap on materialized integer ranges (`..` and `..=`) across interpreter, bytecode VM, and native AOT execution.
- **`P2.3` (`src/smt.rs`)**: Escape SMT-LIB2 string literals via `""` doubling, enforce strict sort mapping (`map_type_to_smt_opt`) so unsupported non-nullary parameter sorts return `None` rather than unsoundly mapping to `Int`, and introduce the `SolverBackend` trait (`ProcessSolver`, `MockSolver`).
- **`P2.4` + `P2.5` (`src/model_check.rs`, `src/cli.rs`, `src/wp.rs`)**: Precompute `q_holds` once per temporal property, eliminate duplicate Tarjan SCC passes in `check_eventually_from`, add `--format json` to `bil verify` and `bil model-check`, add `--seed <N>` to `bil vm`, and achieve zero `cargo clippy --all-targets -- -D warnings` warnings.
- **`P2.6` + `P2.7` (`docs/SEMANTICS.md`, `tests/differential.rs`, `src/codegen.rs`, `src/runtime_prelude.rs`)**: Document formal language semantics across all four backends and add a 3-way differential equivalence suite verifying identical outputs across `eval`, `vm`, and standalone native AOT binaries (including seeded Xorshift64* GCL nondeterminism).
- **`P3.1` (`src/smt.rs`)**: Add incremental `(push 1)` / `(pop 1)` SMT batch execution (`run_smt_incremental_batch`) and in-memory `SMT_CACHE`.
- **`P3.2` (`src/model_check.rs`)**: Add Symbolic Bounded Model Checking (`symbolic_bmc_program`, `symbolic_bmc_system`, `emit_symbolic_bmc_smt2`) unrolling `system` transition relations in SMT-LIB2 up to depth $k$.
- **`P3.3` (`src/driver.rs`, `src/cli.rs`)**: Add memoized `CompilationSession` so `bil all` parses, validates OntoLogic DAGs, and typechecks once across all pipeline stages.

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
