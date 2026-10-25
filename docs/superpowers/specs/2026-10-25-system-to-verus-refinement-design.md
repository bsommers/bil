# System → Verus refinement (intent brief)

Status: draft for review. Roadmap item 1; the continuous-plant layer is a later cycle that builds on this one.

## Intent
`bil emit-verus` turns a `system` block into a state struct, an `invariant()` predicate and `init()`. It emits nothing for the transitions, so Verus never checks that the model's invariants are inductive. Make the emitted Rust carry that proof, so a verified controller step in Rust is tied to the model that `model-check` explored.

## Scope (this cycle)
1. For each `transition` branch `i` of a system, emit `pub fn step_<i>(&mut self)` with
   `requires self.invariant(), <guard>` and `ensures self.invariant(), <each update as old/new equation>`.
   Updates are simultaneous, as in `docs/SEMANTICS.md`.
2. Emit `pub open spec fn next(pre, post) -> bool` as the disjunction of the branches' guard-and-update relations. This is the abstraction users hand-written Rust refines.
3. Timed systems: emit the post-`timed::lower_program` form, so `Deadline_*`, `Latch_*` and `Stall_*` are part of `invariant()`.
4. Support the expression subset `emit-verus` already handles. Anything outside it is a clean error (`// unsupported`), never silent wrong output.

Not in scope: user-written Rust checked against the model, continuous plants, LTL/liveness (the invariants are safety only; say so in the output header).

## Verification
- Verus installed by the user. Pin a version in `scripts/` and document it.
- `tests/verus_systems.rs`: run `verus` on emitted code for the domain examples. Skip when `verus` is not on PATH, like the z3-gated tests.
- Seeded bug: a system whose invariant is not inductive must make Verus fail (negative test).
- Snapshot tests of emitted text so unchanged output stays stable.
- `scripts/ci.sh` stays green; coverage must not drop below the current 82.5%.

## Open questions
- Nondeterministic `choose` in updates: emit as an existential or a `// choose` parameter.
- Whether `step_<i>` takes `&mut self` (Verus style) or returns a new state.

## Next
User installs Verus → write the implementation plan (`planning-with-contracts`) → build.
