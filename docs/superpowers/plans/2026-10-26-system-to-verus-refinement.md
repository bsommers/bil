# System → Verus refinement: implementation plan

Spec: `docs/superpowers/specs/2026-10-25-system-to-verus-refinement-design.md`. Scope and non-goals are there.

## Environment (verified 2026-10-26)
- Verus `0.2026.10.26.d17fbd0` at `~/tools/verus/verus-x86-linux/verus`; needs Rust toolchain `1.99.1` (installed via rustup).
- Run: `verus FILE.rs --crate-type=lib` (summary line: `verification results:: N verified, 0 errors`).
- Tests find Verus via `$VERUS`, then `PATH`; skip when absent (like the z3-gated tests).

## Baseline finding
`emit-verus` output verifies for 1 of 14 `examples/domains/*.bil` (`process_safety_reactor`: 3 verified). The rest fail to compile, mostly E0425: enum variants are emitted bare (`Soak`) instead of qualified (`Phase::Soak`). Fixing the baseline is Task 1, because step proofs are meaningless on code that does not compile.

## Tasks

### Task 1: Make existing emission compile and verify
**Files:** `src/verus.rs`, new `tests/verus_emit.rs`.
**Interface:** `emit_verus_rust(program, ontology) -> String` unchanged.
- [ ] Failing test: for every `examples/domains/*.bil` (not seeded_bugs), emit and run Verus; expect `0 errors`. Skips without Verus.
- [ ] Qualify variant references by their enum type (`verus_expr`, `verus_self_expr`); fix whatever the next error class is, one class per commit.
- [ ] Anything not expressible: emit `// unsupported: <reason>` and `assume`-free omission, never wrong code; record the list in the test as an explicit allowlist with a reason each.
- **Verify:** `cargo test --test verus_emit`; allowlist only shrinks.

### Task 2: Step functions per transition
**Files:** `src/verus.rs`, `tests/verus_emit.rs`, new `tests/snapshots/verus_*.rs`.
**Interface:** for system `S`, branch `i` (0-based, document order): `pub fn step_<i>(&mut self)` with
`requires old(self).invariant(), <guard over old(self)>` and `ensures self.invariant(), self.<v> == <update over old(self)>` for every updated state var, and `self.<w> == old(self).<w>` for the rest. Updates are simultaneous.
- [ ] Failing test: `examples/mutex_protocol.bil` (small) emits `step_0..` and Verus proves them.
- [ ] Body: assign updates computed from a snapshot of `*old(self)`.
- [ ] `choose`/nondeterministic updates: emit the step taking the chosen value as a parameter constrained by the `choose` predicate (resolves the spec's open question; `&mut self` style chosen).
- **Verify:** Verus proves all steps for domain examples outside the Task 1 allowlist.

### Task 3: `next` relation and timed systems
**Files:** `src/verus.rs`, `tests/verus_emit.rs`.
**Interface:** `pub open spec fn next(pre: S, post: S) -> bool` = disjunction over branches of (guard(pre) ∧ post == update(pre)).
- [ ] Failing test: `semiconductor_se_spe.bil` (timed) emits `Deadline_*`, `Latch_*`, `Stall_*` inside `invariant()` and its steps verify.
- [ ] Emit from the lowered program (`timed::lower_program` already runs in the driver; confirm `emit-verus` goes through it).
- **Verify:** SPE steps verify; `spe_late_cutoff.bil` is covered by Task 4.

### Task 4: Negative tests (the proof must be able to fail)
**Files:** `tests/verus_emit.rs`.
- [ ] For each seeded bug in `examples/domains/seeded_bugs/` whose violation is a safety invariant (`model-check` exit 1, not LTL), expect Verus to report an error on some `step_*`. LTL-only and runtime-axiom bugs are listed as out of scope with a reason.
- **Verify:** every in-scope seeded bug fails Verus; unmodified models pass.

### Task 5: CI, docs, honesty
**Files:** `scripts/ci.sh`, `README.md`, `CHANGELOG.md`, `docs/SEMANTICS.md`, `docs/ARCHITECTURE_AND_VERUS.md`.
- [ ] `scripts/ci.sh` runs the Verus tests when `verus` is found and prints `verus: skipped` otherwise; pin the version in a `scripts/VERUS_VERSION` file.
- [ ] Docs state exactly what is proved: safety invariants are inductive over the emitted steps; liveness (LTL) is not covered; hand-written Rust refinement of `next` is the user's follow-on.
- [ ] CHANGELOG entry. Domain numbers stay labelled illustrative; no new domain claims.
- **Verify:** `scripts/ci.sh` green with and without Verus; coverage stays at or above 82.5%.

## Rules in force
Ask before every push or tag. Never commit `docs/plans/`. No `cargo fmt`. Commit trailer `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Subagents get an explicit `model` (haiku for mechanical variant-qualification fixes, sonnet for multi-file steps).

## Risks
- Verus rejects constructs bil allows (strings, records with `with`, `match`): handled by the Task 1 allowlist; each entry must name its reason.
- Verus runtime is a few seconds per file; keep the test serial and skip-gated.
- Verus releases weekly; the pinned version is the contract, upgrades are deliberate.
