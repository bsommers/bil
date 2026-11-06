# Solver measurement (Roadmap 8.1.1)

Measured 2026-10-30 on `bil` v0.7.1 with z3 from `~/.local/bin`. No change to `src/`. Companion to `docs/SOLVER-CONSIDERATIONS.md`.

## Method

- A logging shim set as `BIL_Z3_PATH` copied each SMT-LIB2 script from stdin to a file, then ran the real z3. It captured every script that `bil` sends.
- `bil verify <file> --allow-bounded` on each of the 14 `examples/domains/*.bil` files.
- `bil model-check <file> --bmc 3` on the same files.
- Features counted by regular expression over the captured text.

Not covered: `examples/domains/seeded_bugs`, queries made by `tests/`, and `solve --subsumes`.

## What `verify` sends (14 examples, 36 scripts, 149 `check-sat`)

All 14 examples verify with 0 obligations left bounded (exit 0).

| Feature | Occurrences | Scripts using it (of 36) |
|---|---|---|
| `Int` | 237 | 34 |
| `Bool` | 46 | 24 |
| `declare-sort` (always `Entity`) | 36 | 36 |
| `declare-fun` with arguments (field and predicate symbols) | 94 | 24 |
| `forall` | 29 | 13 |
| `ite` | 19 | 2 |
| `*` | 93 | 8 (every one has a numeric constant operand) |
| `div` / `mod` | 13 | 3 (only `div` by the constants 5 and 10) |
| `String` | 18 | 12 (only in `declare-fun` signatures; never asserted) |
| `Real`, `exists`, `Array`, `datatype`, `define-fun` | 0 | 0 |

- Every `forall` ranges over `Entity` (59 of 59 binders). They come from the ontology preamble (`subClassOf` reflexivity and transitivity) and from `axiom` clauses of the form `forall s. is_X(s) => ...`.
- No nonlinear multiplication was found.
- Scripts use `push`/`pop` (136 `push`): one script holds several obligations.

## What `model-check --bmc 3` does

- 4 of 14 examples get a BMC verdict for at least one system, all `PROVED SAFE (k=3)`: `control_antiwindup_pi`, `cybersecurity_zero_trust`, `medical_infusion_pump`, `process_safety_reactor`.
- The other 10 fail with `error: BMC not applicable to system ...: it has a state or expression outside the Int/Bool SMT subset`, exit 1. `cybersecurity_zero_trust` has two systems: one gets the verdict, the other gets this error. That is the encoder's limit, not the solver's.

## With no solver installed (`HOME=/nonexistent`, minimal `PATH`)

| Command | Output | Exit |
|---|---|---|
| `verify` | `[BOUNDED (6561 samples)] ... [SMT vampire: skipped]`, then `error: 2 obligation(s) were only checked on bounded samples` | 1 |
| `model-check --bmc 3` | `[BMC INCONCLUSIVE (k=3)] Prover vampire verdict: skipped.` | **0** |
| `solve` | `SMT Solver Result (vampire): vampire binary not found` | **0** |
| `solve --emit-smt2` | prints the script, no solver needed | 0 |

- Messages name `vampire` because `auto` falls through to it when nothing is found.
- `model-check --bmc` and `solve` exit 0 when no verdict was produced. `verify` exits 1 in the same situation (Milestone 5 made that strict). This is an inconsistency, listed below as a follow-up.

## Decision gate for 8.1.2

Result: **proceed**, with a narrow fragment. Every captured `verify` script falls in:

- linear integer arithmetic (constant multiplication, `div` by constants), Booleans, `ite`;
- uninterpreted functions over one uninterpreted sort `Entity`, with `Int`, `Bool` and (declared only) `String` results;
- universal quantifiers only over `Entity`, with no function returning `Entity`.

Candidate approach: replace each `forall` over `Entity` by its instances over the declared `Entity` constants, then decide quantifier-free linear integer arithmetic with uninterpreted functions. Whether that instantiation is complete for these scripts is the first thing 8.1.2 must prove or test against z3.

Limits of this evidence:
- 14 hand-written examples written to verify; other programs may use `Real`, `exists` or recursion that these do not.
- Feature counts say nothing about hardness. z3's time per script was not measured.
- The 10 BMC-not-applicable systems show the encoder, not a solver, is the limit for `--bmc`; an in-repo solver does not change that.

## Follow-ups found

1. `model-check --bmc` (INCONCLUSIVE) and `solve` (solver not found) exit 0 without a verdict. Decide whether they should exit non-zero like `verify`.
2. Messages say `vampire` when no solver is installed at all.
