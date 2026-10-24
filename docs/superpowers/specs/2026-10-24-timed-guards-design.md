# Timed guards in `system` blocks — design

Status: draft for approval (2026-10-24). Roadmap item, white paper §8.

## Intent

A `system` can today prove `P ~> Q` ("Q eventually follows P"). That is too weak
for a controller whose correctness depends on *how soon* it reacts. The motivating
case is a solid-phase-epitaxy (SPE) anneal: the in-situ spectroscopic ellipsometer
(SE) raises a detection signal, and the thermal controller must cut heating within
a phase-dependent bound so the layer stays solid (see
`examples/domains/semiconductor_se_spe.bil`, whose sources are in
`docs/whitepaper/CITATIONS.md`). bil should state that bound and either prove it or
return a counterexample trace.

## Decisions made with the user

- The controller is a **constant scan cycle**: it reads inputs every `period`, then
  decides and sets outputs. A reaction cannot occur before the next scan.
- The detection signal is **latched and synchronous**: it is held until a scan reads
  it. No signal loss is tolerated, so a missed pulse is not a case to model.
- The deadline is **per phase**: each phase of the system has its own bound.
- Surface syntax shape (user approved the shape, not the final spelling):

```
system Epi {
  clock scan period 1ms;
  phase growth { on detected => heater_off within 3ms; }
  phase anneal { on detected => heater_off within 20ms; }
}
```

## Goals

1. Declare one scan `period` per system and a deadline `within D` per phase.
2. Prove, for every reachable state, that once the trigger holds in a phase the
   response holds within `D`; otherwise print a counterexample trace.
3. Check that the latch is cleared only after the response was commanded, and that
   no path leaves the latch set without a reaction.
4. Reject (at check time) a deadline that is unachievable by construction, e.g.
   `D` smaller than `period`.
5. Extend `examples/domains/semiconductor_se_spe.bil` and add a seeded-bug variant
   that misses its deadline.

## Non-goals

- Dense real-time semantics (timed automata, clock zones). Time is discrete scans.
- Modelling the detector's or actuator's analog latency beyond a declared constant.
- Any process threshold or timing figure presented as fact. Numbers in examples are
  placeholders labelled illustrative unless cited (CITATIONS.md tiers A–D).
- Code generation of timers in Verus output (a later roadmap item).

## Anti-goals

- Passing a deadline check only because the model has too few states or got truncated.
  A truncated search must report the result as bounded, as today.
- Weakening untimed `~>` or any existing check. Systems without clocks behave as now.

## Constraints

- Match the existing pipeline: `lexer → parser → ast::SystemDecl → model_check`,
  and the SMT bounded model check in `model_check.rs`.
- `scripts/ci.sh` must stay green; docs (`SEMANTICS.md`, CHANGELOG, whitepaper §8,
  README feature lists) updated in the same change.
- Never run `cargo fmt`; never commit `docs/plans/`.

## Proposed semantics (the builder's starting point; my call, not the user's)

- One transition firing = one scan. Time is the integer count of scans, so `D` ms
  becomes `ceil(D / period)` scans. Units `ms`, `us`, `s` are accepted on literals.
- Lowering: a `within` clause desugars to a hidden counter state variable that resets
  when the trigger is first latched and increments each scan, plus a safety
  invariant `counter <= bound while response not yet true`. This reuses the existing
  `always` machinery, so explicit-state and SMT-BMC checks both work unchanged.
- Worst-case latency is one scan to observe the latch plus the actuation scans the
  transitions take, which the counter measures directly.

## Left to the builder

- Final keyword spelling and whether `phase` is a new block or a guard on the
  existing `phase` state variable of the example.
- Error messages, and the shape of the counterexample trace output.
- Test layout (follow existing `tests/` conventions).

## Calls made after the builder check (my calls, for the user to check)

- **Meaning of `within D`:** let `n = ceil(D / period)`. Scan 0 is the scan in which
  the latch is first true at the start of the scan. The response must hold in the
  state after scan `n - 1` at the latest. A controller that reacts in the very next
  scan therefore needs `n >= 1`, so `D == period` is achievable and `D < period`
  is rejected (goal 4). Tests must include a one-scan-late mutant that fails and the
  correct version that passes.
- **The latch is a user-declared `Bool` state variable**, named in the `on` clause.
  The environment may set it on any scan, including while already set; setting it
  again changes nothing, which matches "no signal loss". Goal 3 is then a check over
  user transitions: any transition clearing the latch must also set the response.
- **`phase` is a guard over the system's existing state variable**, not a new block
  that defines phases. This keeps the change a parser extension plus a lowering.
- **One timer per `on` clause.** A trigger arriving while the latch is already set is
  the same pending event.
- **Truncated searches** report as bounded, inherited from the existing checks. The
  builder should confirm this in the code.

## Decided by the user

- **Phase change while a timer is running:** the timer keeps running and the bound
  from the phase where the trigger was latched still applies. A controller must not
  escape a tight deadline by changing phase. Approved 2026-10-24, together with all
  the calls above.
