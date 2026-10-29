# Solver considerations

Status: analysis only. No code changed. Effort figures are estimates, not measurements.

## How bil uses solvers today

- bil has no built-in SMT solver. `src/smt.rs` (1,103 lines) pipes SMT-LIB2 to an external `z3`, `cvc5` or `vampire`, selected with `--prover` (including `auto`).
- Lookup order: `BIL_<NAME>_PATH`, `BIL_SOLVER_DIR`, `~/.local/bin`, then `PATH`. Timeout: `BIL_SOLVER_TIMEOUT_MS`.
- Built in, no solver needed: the sampling checker (`src/wp.rs`, "BOUNDED (N samples)"), the explicit-state and LTL model checker (`src/model_check.rs`), and run/vm/build.
- Needs a solver: `solve`, `verify` proofs, `model-check --bmc`. Without one, `verify` falls back to BOUNDED with `[SMT ...: skipped]` and exits 1 unless `--allow-bounded`.
- Not checked: what `solve` and `model-check --bmc` do with no solver installed.
- Theories seen in `src/smt.rs`: `set-logic ALL`, `Int`, `Real`, `forall` (8 uses), `exists` (1), `declare-sort`, `declare-fun`, `declare-const`. Results read back: sat, unsat, unknown. How many real queries use each feature has not been measured.

## Can we do better than z3?

Not as a general solver. A narrow solver for the fragment bil emits is realistic, and is worth building only as a fallback (see the recommendation).

## Options

| Option | What it is | Effort (estimate) | Pros | Cons |
|---|---|---|---|---|
| A. Status quo | Shell out to z3, cvc5 or vampire | 0 | Mature, already works, three independent provers | External install; `verify` degrades to BOUNDED without one |
| B. Bundle or auto-fetch z3 | Ship the binary, or download a pinned one | 1-2 weeks | Easy for users; pinned version | Licensing and packaging; per-platform binaries; supply-chain trust; still external code |
| C. Link z3 or cvc5 as a library | Rust bindings (`z3` crate, `cvc5-sys`) | 2-4 weeks | No process piping; faster; better errors | Needs a C++ toolchain; breaks the "serde only" dependency story; slower builds |
| D. Small in-repo solver | Decision procedure for quantifier-free linear integer/real arithmetic plus bounded enumeration for finite domains | 8-16 weeks | Works with nothing installed; auditable; can emit a checkable proof | Covers only a fragment; returns `unknown` outside it; ongoing maintenance |
| E. Full SMT solver | DPLL(T), simplex, E-matching for quantifiers, theory combination | 12-24+ months | Total control | Unrealistic; see below |
| F. Proof-checking only | z3 searches; bil checks its proof certificates | 6-12 weeks | Removes trust in z3's answer | Still needs z3; z3 proof output is awkward to consume |
| G. More external provers | Yices, Bitwuzla, Alt-Ergo | 1-3 days each | Cheap; cross-checking between provers | Same install problem as today |

## Why E would be worse than z3 at the end

This is an argument from how solvers are built. It is not a benchmark of anything in this repo.

1. **Engineering years, not features.** The core of an SMT solver (SAT search, simplex, theory combination, quantifier instantiation) is textbook material. Competitive performance is not. It comes from many heuristics (restarts, clause deletion, variable ordering, instantiation triggers), tuned over years against large benchmark sets. A new solver starts with none of that tuning.
2. **Quantifiers have no complete answer.** Quantified arithmetic with uninterpreted functions is undecidable in general. Every solver is a pile of heuristics there, and the ones that work are the result of long iteration on real failures. bil emits `forall`, so this is exactly the hard part.
3. **Soundness bugs.** A solver that wrongly answers `unsat` makes bil print PROVED for a false claim. Mature solvers have had many such bugs found and fixed through years of fuzzing and use. A new one has not. For a tool whose point is provable claims, a wrong PROVED is worse than a slow or unknown answer.
4. **Maintenance never ends.** New query shapes keep exposing slow or wrong cases. Someone has to keep fixing them, and that cost lands on this project.
5. **No opportunity cost paid back.** Even a perfect E would only match z3 on queries z3 already handles, so the 12-24 months would buy independence, not capability.

A narrow solver (D) avoids most of this because it declares a fragment it can decide, and says `unknown` outside it, instead of trying to compete everywhere.

## Recommendation

1. Fix the README "Requires z3" wording, and run `solve` and `model-check --bmc` with no solver to document what happens.
2. Measure: run the 14 domain examples and record which SMT features each query uses (about 1 day, no code changes to bil). This decides whether D covers most queries.
3. If it does, build D as a complement. z3 stays the default; D runs when no solver is found and labels results `PROVED (by bil-smt)`.
4. Consider F later.
5. Do not do E.
