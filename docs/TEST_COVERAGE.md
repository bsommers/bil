# Test Suite & Coverage Report — `bil`

**Date:** `2026-10-18` (baseline at commit `31e5c38`, v0.4.0+; updated the same day after adding `tests/cli.rs`, see §8)
**Tooling used:** `cargo-llvm-cov 0.9.1` (stable rustc 1.89 for line/function/region; nightly `--branch` for branch coverage)

This is the first coverage report for the repo, so there's no earlier one to compare against.

---

## 1. Test Suite Inventory

| Dimension | Value |
|---|---|
| Test framework(s) | Built-in `cargo test` (`#[test]`), plus `cargo-fuzz`/libFuzzer targets in `fuzz/` (`lex`, `parse`, `check`) |
| Total test files | 4 integration (`tests/bil_tests.rs`, `differential.rs`, `security.rs`, `soundness.rs`), plus unit tests in `src/codegen.rs`, `src/smt.rs` and `src/symbol.rs` |
| Total test cases | 37 at baseline (15 integration + 6 differential + 5 security + 8 soundness + 3 unit); 47 runnable plus 4 ignored after §8 |
| CI-enforced? | **No.** The repo has no `.github/workflows` and no other CI config |
| Runtime | ≈ 8 s (`cargo test`, debug build, z3 and cvc5 on `PATH`) |

---

## 2. Coverage Summary

| Metric | Value | Source |
|---|---|---|
| Line coverage | **73.2%** (6807 / 9303) | `cargo llvm-cov` (stable) |
| Function coverage | **74.6%** (369 / 495, closures counted separately) | `cargo llvm-cov` (stable) |
| Region coverage | 73.1% (12773 / 17485) | `cargo llvm-cov` (stable) |
| Branch coverage | **59.0%** (875 / 1484) | `cargo +nightly llvm-cov --branch` |

> **Measurement caveats**
> - **The nightly run doesn't match stable.** It uses finer-grained instrumentation and reports 65.0% lines and 41.0% regions. Treat the stable numbers as the headline and use nightly only for the branch figure.
> - **`runtime_prelude.rs` (21.8%) is under-measured, not under-tested.** `codegen.rs` embeds it with `include_str!` into generated native binaries, and code that runs inside those child processes isn't instrumented. The differential tests do exercise it through `build_native_source`, so the real coverage is higher than shown. Only the copy pulled in by the `include!` unit test in `codegen.rs` gets measured.
> - **`cli.rs` (15.6%) and `main.rs` (0%)** are low because almost every test calls the library facade (`*_source`) rather than the CLI. Only `run_cli` for `model-check` is called once, from `tests/differential.rs:286`.

### Per-module line coverage

| Module | Lines | Module | Lines |
|---|---|---|---|
| `wp.rs` | 88.8% | `smt.rs` | 78.1% |
| `parser.rs` | 89.0% | `model_check.rs` | 75.3% |
| `driver.rs` | 92.6% | `verus.rs` | 74.2% |
| `ir/lir.rs` | 87.5% | `builtins.rs` | 74.0% |
| `ir/hir.rs` | 84.4% | `lexer.rs` | 71.1% |
| `symbol.rs` | 85.0% | `eval.rs` | 69.3% |
| `vm.rs` | 82.7% | `ontology.rs` | 68.9% |
| `codegen.rs` | 81.6% | `types.rs` | 65.1% |
| `expr_utils.rs` | 62.7% | `semantics.rs` | 60.9% |
| `error.rs` | 62.5% | `ir/vir.rs` | 35.2% (mostly `Display`) |
| `cli.rs` | 15.6% | `runtime_prelude.rs` | 21.8% (see caveat) |

---

## 3. Coverage Gaps (Prioritized)

A verifier has a different kind of critical path than a web service. Its worst failure is **reporting PROVED or VERIFIED, or exiting 0, when the property doesn't hold**. That outcome is P0 here, alongside process spawning and file I/O.

### P0 — Untested code on the critical path (soundness, process spawning, the verdict users see)

| Function/Module | File | Why it matters |
|---|---|---|
| `decide_status`: the SMT `sat`-but-no-bounded-counterexample arm, plus both `Unknown` arms | `src/wp.rs:45-57` | This is the only function that turns evidence into a verdict, and three of its five outcomes are never exercised. **No test covers "bounded search misses but SMT finds a model"**, which is the main reason the SMT backend exists. The `Unknown` arms (no solver and no samples, or a solver error) are also never reached, so a regression that maps them to `Proved`/`BoundedOnly` would go unnoticed. |
| `bil verify` exit code and verdict rendering | `src/cli.rs:340-400` (34 of 60 lines missed) | CI and users rely on the exit code. No test checks that `bil verify` returns non-zero for a `Refuted` or `Unknown` obligation. The probe from the architecture review (false lemma gives exit 1) is currently checked by hand only. |
| **BOUNDED obligations exit 0, even when the solver failed** | `src/wp.rs:259`, `:401`, `:554` (`verified` includes `BoundedOnly`); `src/cli.rs:389` | **Confirmed false pass:** if every solver errors or crashes and bounded sampling misses the counterexample, a false contract (`requires x * x == 1369 ensures result == 0`, refuted by x = ±37) prints `[BOUNDED (12 samples)]` and `bil verify` **exits 0**. The display is honest, but CI only looks at the exit code. This is a policy decision rather than a plain bug; options are a nonzero exit for `BoundedOnly`, or a `--strict` flag. Pinned by the ignored test `verify_exits_nonzero_when_solver_fails_and_sampling_misses` in `tests/cli.rs`. |
| `run_single_binary`: the SMT-LIB `(error …)` path and the spawn/wait failure paths | `src/smt.rs:298-305`, `:344-352`, `:399-407`, `:425-427` | These paths produce `Skipped`/`Unknown` when the solver is missing, fails to spawn, or rejects the script. None are tested. If one regresses to `Inconsistent`, every obligation becomes PROVED. A fake solver on `BIL_Z3` that prints `(error "x")\nunsat` would cover the most dangerous case. |
| `find_solver_binary`: the `PATH` search and env-dir branches | `src/smt.rs:123-145` | This decides which executable gets spawned. The env-override branch is covered, but the `PATH` fallback and the `is_file` checks aren't. |
| `collect_free_vars` for `Match`, `LetIn`, `Call`, `FieldAccess`, `RecordInit`/`RecordWith`, `List` and `Unary` | `src/expr_utils.rs:22-113` (71 of 88 lines missed) | Capture-avoiding substitution (P0.4) depends on free-variable sets. If a binding form is wrong here, `subst_expr` can capture variables without any error, and the resulting VC is quietly wrong. Today only `Var`, `Binary`, `Quantifier`, `IfFi` and `DoOd` are exercised. |
| `subst_expr` for `RecordInit`, `RecordWith`, `List` and the `FieldAccess`-over-`RecordWith` shortcut | `src/expr_utils.rs:265-312` | These are the same soundness concern, for concept or record postconditions. |

### P1 — Untested core execution paths

| Function/Module | File | Why it matters |
|---|---|---|
| CLI flag parsing: silent fallbacks | `src/cli.rs:302-333`, `:63-70`, `:153` | **Confirmed:** `--bmc abc` silently falls back to explicit-state checking, so a different analysis runs than the one requested. That analysis is still sound: a violation still exits 1. `--max-states 1O0` silently becomes 50 000, `--seed x` becomes 42, and unknown flags (`--jsno`, `--bmcc`, `--dump-bytcode`) fall through `_ => {}`. Pinned by three ignored tests in `tests/cli.rs`. *(An earlier draft of this report said `--bmc abc` gave a false `[VERIFIED]`. That came from a shell pipe hiding the exit code. Corrected 2026-10-18.)* |
| SMT counterexamples contain no model | `src/wp.rs:45-47`, `src/smt.rs` | When only the solver refutes a VC, the counterexample printed is `SMT model: sat`, because the script never asks the solver for a model (`(get-model)`), so no values for `x` are shown. The verdict is correct but the counterexample isn't usable. |
| `encode_value_canonical` for `List`, `ConceptInstance`, `PartialCall`, `Float` and `Unit` | `src/model_check.rs:77-120` | This is the state-deduplication key. A collision makes BFS skip reachable states, so the checker reports VERIFIED without exploring them. Only systems whose state is `Int`, `Bool` or `Str` are tested. |
| `model_check_system` (114 of 348 lines missed) | `src/model_check.rs:180` | The fairness and LTL branches beyond the basic `~>` case, and the deadlock reporting, are only partly exercised. |
| `infer_expr` / `infer_pipe` (137 + 73 lines missed) | `src/types.rs:523`, `:1027` | Pipe stages and less common expression forms in the type checker. A type hole here lets an ill-typed program reach the verifier. |
| `eval_binary_value`: `Implies`/`Iff`, `Float` comparisons and arithmetic, `In`, `Range` and its 100k cap, string `+` | `src/semantics.rs:69-112` | This is the shared semantics module that `eval` and `vm` both call, but the differential suite only covers the `Int` and `Bool` arithmetic subset. The range-cap error path guards against running out of memory and has no test. |
| `exec_pipe_stage` / `eval_pipe` (53 + 70 lines missed) | `src/vm.rs:738`, `src/eval.rs:748` | Pipeline built-ins are duplicated in both runtimes and only partly tested. There's no differential test proving the two runtimes agree. |
| `render_fol_sexpr` (103 of 167 lines missed) | `src/ontology.rs:346` | This emits the first-order logic sent to vampire. The quantifier, implication and record branches are untested. |
| `run_repl` (0%) | `src/cli.rs:520` | The interactive REPL is user-facing and has no tests. |

### P2 — Untested edge cases and error handling

| Function/Module | File | Missing scenario |
|---|---|---|
| `compile_native_binary` | `src/codegen.rs:806-842` | The temp file already exists (the `O_EXCL` collision), a write fails, or `rustc` fails to spawn. |
| `run_single_binary` stdin write | `src/smt.rs:356-358` | The write happens **before** the timeout loop starts. If a solver stops reading stdin while its stdout pipe is full (a large VC plus large output), `write_all` blocks and the wall-clock timeout never fires. There's no test with a solver that ignores stdin. |
| `tokenize` (103 of 362 lines missed) | `src/lexer.rs:133` | Error branches for malformed numbers, strings and Unicode operators. The fuzz targets are a backstop, but there are no assertions on the error messages. |
| `search_counterexample` | `src/wp.rs:912` | Paths where the sample domain is empty or evaluation errors on every sample. |
| `Display` impls (`hir`/`vir`/`lir`/`vm`/`ast` `fmt`) | various | `dump-ir` / `--dump-bytecode` output is never snapshot-tested. This is low risk but cheap to cover. |

---

## 4. Shell Test-Quality Checklist (adapted for a Rust CLI)

`bil` has no shell code. The checklist items still apply to how it spawns processes and parses its arguments:

- [ ] ~~`set -e` interaction~~: not applicable.
- [~] **External commands are mocked.** `BIL_Z3` and the `BIL_<PROVER>_PATH` overrides exist, and `SolverBackend`/`MockSolver` support in-process fakes. But no test uses a fake solver *binary* on the real spawn path to cover the `(error`, crash, garbage-output or ignores-stdin cases.
- [x] **No command strings are built by splicing.** Solvers and `rustc` are invoked with argv arrays, and the SMT-LIB and Rust emitters escape their input (SEC-1; `tests/security.rs`).
- [ ] **Unknown values in dispatch tables fail loudly.** The top-level command dispatch does (`_ => print_usage(); 1`). Per-command flag parsing does not: unknown flags and unparseable values are silently ignored (see the P1 row above).

---

## 5. Recommended Additions (Action Plan)

In priority order. Each item names the file it belongs in.

1. ✅ *Done 2026-10-18 (`test_decide_status_covers_every_verdict_arm`).* **`tests/soundness.rs`: unit tests for every arm of `decide_status`.** Cover the bounded counterexample beating `unsat`, `unsat` alone giving `Proved`, `sat` with no bounded counterexample giving `Refuted`, `Unknown` with samples giving `BoundedOnly`, `Unknown` with 0 samples giving `Unknown`, and `None` with 0 samples giving `Unknown`. These are pure function calls taking about 5 minutes to write, and they pin the verdict lattice.
2. ✅ *Done 2026-10-18; flag fixes still open, pinned by 3 ignored tests.* **New `tests/cli.rs` that runs `env!("CARGO_BIN_EXE_bil")` end to end.** Check that `verify` exits non-zero on the false-lemma probe and exits 0 on `examples/gcd_refinement.bil`. Check that `model-check --bmc abc`, `--max-states 1O0` and an unknown flag each **fail with exit 2 and a message**. This needs a code change first: replace the `unwrap_or(default)` and `_ => {}` fallbacks with errors. Write the test before the fix.
3. 🟡 *Partly done: `broken_solver_output_is_never_reported_as_proved` in `tests/cli.rs` covers the error-then-unsat, crash, garbage and timeout cases. The stdin-ignoring solver is still open.* **`tests/security.rs`: a fake-solver binary harness.** Write a temp script on `BIL_Z3` for each case:
   - `(error "x")\nunsat` must give `Unknown`, not `Proved`.
   - Exit 139 with no output must give `Unknown`.
   - A sleep longer than the timeout must give `Unknown` within the timeout plus slack.
   - A solver that never reads stdin, given a VC over 64 KiB, should give `Unknown`. This case is expected to hang today; mark it `#[ignore]` until the stdin write is moved to a thread.
4. **`src/expr_utils.rs` unit tests: free variables and substitution for every `Expr` variant.** Use a table-driven test asserting `free_vars(subst(e, x↦y))` equals `free_vars(e)` with `x` replaced by `y` whenever `x` is free, including `Match`, `LetIn` and quantifiers whose bound name is in `free_vars(y)`. A `proptest` over generated `Expr`s would cover this more completely, but it would add a dependency.
5. **`tests/differential.rs`: extend the 3-way equivalence suite** to floats, `Implies`/`Iff`, `in`, ranges including the 100k cap error, string concatenation and pipeline built-ins, so that `eval`, `vm` and native agree on more than `Int`/`Bool` arithmetic.
6. **`tests/soundness.rs`: model checking over `List`- and concept-valued state.** Use a system whose state is a list, plus a test asserting that `encode_value_canonical` gives different keys for structurally different values, e.g. `[1,[2]]` vs `[[1],2]` and records with swapped fields.
7. **`tests/bil_tests.rs`: snapshot tests for `dump-ir` (hir, vir, lir) and `vm --dump-bytecode`** on one example program. This is cheap and covers the 0% `Display` impls.
8. **Raise the coverage floor in CI** (see §7) once items 1–3 land. The expected floor after them is about 76% lines.

---

## 6. What's Already Solid

- **The original P0 soundness fixes all have regression tests** in `tests/soundness.rs`: the false lemma is never assumed, a concrete counterexample beats SMT, Euclidean and checked integer semantics, capture-avoiding substitution, and model-check truncation reporting. All five probes from the architecture review still hold at `31e5c38`.
- **`wp.rs` (88.8%) and `parser.rs` (89.0%, every function executed)** are the best-covered modules, and they matter most.
- **A 3-way differential suite** (`eval` vs `vm` vs native AOT) is unusual for a project this size and is the right structure. It mainly needs wider input.
- **Security hardening is tested:** codegen escaping, exclusive temp files, solver timeout kill, and recursion and VM fuel limits (`tests/security.rs`).
- **Fuzzing is set up:** 3 targets, about 3.9M runs on 2026-10-18 with no crashes.
- **`cargo audit` is clean** (12 crates, 1338 advisories checked), and `Cargo.lock` is now committed.

---

## 7. CI Wiring (proposed, not yet added)

The repo has no CI. A minimal `.github/workflows/ci.yml` would:

1. Run `cargo test`, `cargo clippy --all-targets -- -D warnings` and `cargo audit` on every push and PR, with z3 installed via `apt-get install z3`.
2. Run `cargo llvm-cov --lcov --output-path lcov.info --fail-under-lines 73` and upload `lcov.info` as an artifact. This makes the gate "never drop below today's 73% baseline".
3. On a nightly schedule, run each fuzz target for 5 minutes with `cargo +nightly fuzz run <t> -- -max_total_time=300`, and upload any `fuzz/artifacts/` as a failure.

To reproduce this report locally:

```bash
cargo llvm-cov --summary-only                              # line/function/region
cargo +nightly llvm-cov --branch --summary-only            # branch
cargo llvm-cov --html && xdg-open target/llvm-cov/html/index.html
```

---

## 8. Update — 2026-10-18, after action items 1–2

Added `test_decide_status_covers_every_verdict_arm` (`tests/soundness.rs`) and a new `tests/cli.rs`. The CLI file has 9 passing tests, plus 4 `#[ignore]`d tests that reproduce open bugs: 3 flag-parsing tests, and 1 for exit 0 on `BoundedOnly` after a solver failure. Run the ignored ones with `cargo test --test cli -- --ignored`.

| Module | Before | After |
|---|---|---|
| `cli.rs` | 15.6% | 37.2% |
| `main.rs` | 0% | 100% |
| `wp.rs` | 88.8% | 91.7% |
| `smt.rs` | 78.1% | 80.3% |
| **Total lines** | **73.2%** | **74.2%** |

Totals are from `cargo llvm-cov` on stable. The line count rose from 9303 to 9376 because the `bil` binary itself is now instrumented.
