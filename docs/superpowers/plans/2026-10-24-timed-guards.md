# Timed Guards Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Let a `system` declare a scan `clock` and per-phase `deadline`s ("once the latch is set, the response holds within D"), proven or refuted by the existing model checkers.

**Architecture:** The parser records `clock` and `deadline` members on `SystemDecl`. A new pass `src/timed.rs` lowers them, right after parsing, into ordinary state variables, transition updates and `invariant`s, then clears them. Every later stage (types, hir, model_check, symbolic BMC, vm, verus) sees a plain system and needs no change.

**Tech Stack:** Rust; existing lexer/parser/AST; `tests/` integration tests that spawn the `bil` binary.

**Spec:** `docs/superpowers/specs/2026-10-24-timed-guards-design.md`

## Global Constraints

- One transition firing = one scan; `n = ceil(D / period)` scans; `D == period` is achievable, `D < period` is rejected at check time.
- The latch is a user-declared `Bool` state variable; setting it again while set changes nothing.
- A phase change while a timer runs does not stop it: the bound from the phase where the latch was set still applies.
- One timer per deadline clause. Systems without `clock`/`deadline` behave exactly as before.
- Truncated searches report as bounded, as today.
- Example numbers are placeholders labelled "illustrative"; no domain figure without a CITATIONS.md source.
- Never run `cargo fmt`; never commit `docs/plans/`; run `scripts/ci.sh` before any push; ask before every push.
- Commit trailer: `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.

## Review Focus

- `within` not a multiple of `period` (e.g. 5 ms on 2 ms) rounds up to 3 scans, never down.
- A response that holds exactly at the last allowed scan passes; one scan later fails (off-by-one both ways).
- The latch cleared before the response was commanded is reported as a violation, not silently accepted.
- `deadline` without any `clock`, two `clock`s, or a duplicate deadline name give a clear error with a span.
- A time unit typo (`3mss`) or a zero/negative duration is rejected, not read as seconds.
- Phase change while pending keeps the original bound (the escape hatch the spec forbids).

## Syntax (builder's spelling; the approved block shape is flattened so spans stay simple)

```
clock scan period 1ms
deadline Cut: detected => heater_off within 3ms in phase == Growth
```

`in <expr>` is the phase guard and is optional (omitted = always). Units `us`, `ms`, `s`. Stored as microseconds (`i64`).

## File Structure

- Modify `src/lexer.rs`: tokens `Clock`, `Deadline`, `Within`, `Period` (keywords). `in` already exists as a token; reuse it.
- Modify `src/ast.rs`: `ClockDecl`, `DeadlineDecl`, two new `SystemDecl` fields.
- Modify `src/parser.rs`: parse the two members in `parse_system` (~line 353).
- Create `src/timed.rs`: validation and lowering.
- Modify `src/driver.rs`: run the pass after parsing.
- Create `tests/timed_guards.rs`; create `examples/domains/seeded_bugs/spe_late_cutoff.bil`; extend `examples/domains/semiconductor_se_spe.bil`; update `tests/domain_examples.rs` `SEEDED`.
- Docs: `docs/SEMANTICS.md` new §4.4, `CHANGELOG.md`, white paper §8.

---

### Task 1: Syntax and AST

**Files:** Modify `src/lexer.rs`, `src/ast.rs`, `src/parser.rs`, every place that builds `SystemDecl` (compiler will list them). Test: `tests/timed_guards.rs`.

**Interfaces:**
- Produces in `src/ast.rs`:
  `pub struct ClockDecl { pub name: String, pub period_us: i64, pub span: Span }`
  `pub struct DeadlineDecl { pub name: String, pub latch: Expr, pub response: Expr, pub within_us: i64, pub phase: Option<Expr>, pub span: Span }`
  `SystemDecl` gains `pub clocks: Vec<ClockDecl>` and `pub deadlines: Vec<DeadlineDecl>`.
- Produces in `src/parser.rs`: `fn parse_duration_us(&mut self) -> Result<i64, ParseError>` (Int literal followed by identifier `us|ms|s`; errors on any other unit or a value `<= 0`).

- [ ] **Step 1: Write failing tests** in `tests/timed_guards.rs`, using a helper `run(args, src)` that writes `src` to a temp `.bil` file and spawns `bil` (copy the `bil`/`text` helpers from `tests/domain_examples.rs`): `parses_clock_and_deadline` (`bil check` exits 0 on a minimal system using the syntax above), `rejects_unknown_unit` (`3mss` → exit non-zero, message contains `unit`), `rejects_zero_duration` (`0ms`).
- [ ] **Step 2: Run** `cargo test --test timed_guards` — Expected: FAIL (unexpected token in system block).
- [ ] **Step 3: Implement** the tokens, AST types and parser arms. Spans: parse each deadline's expressions via `parse_root_expr` and collect their spans into a new group appended in field order, exactly as the existing groups are, and extend `Program::for_each_expr_postorder` (`src/ast.rs:37`) to visit the new fields in the same order.
- [ ] **Step 4: Run** the three tests plus `cargo test --test expr_spans` — Expected: PASS.
- [ ] **Step 5: Commit** `feat(parser): clock and deadline members in system blocks`.

### Task 2: Lowering pass

**Files:** Create `src/timed.rs`; modify `src/lib.rs` (`pub mod timed;`), `src/driver.rs` (call after parse, before type checking). Test: `tests/timed_guards.rs`.

**Interfaces:**
- Consumes: Task 1 AST.
- Produces: `pub fn lower_program(p: &mut Program) -> Result<(), TimedError>` and `pub struct TimedError { pub message: String, pub span: Span }` (convert into the driver's existing error type the same way parse errors are).

Lowering contract per deadline clause `k` with `n = ceil(within_us / period_us)`, latch `L`, response `R`, phase guard `G` (default `true`):

- Adds state `__run_k: Bool = false` and `__t_k: Int = 0`.
- Appends to every transition's updates (updates read the pre-state, as `model_check.rs:360` does) a rule so that: the timer starts when `L && G && !R` holds at the start of a scan, keeps running while `!R`, and counts scans; it resets when `R` holds. The phase guard is only read at start, so a later phase change does not stop it.
- Adds invariants `Deadline_<name>: __t_k >= n => R` and `Latch_<name>: __run_k => (L || R)` (the second reports a latch cleared before the response).
- Generated expressions take the system's span (they have none of their own); keep `node_spans` aligned for `for_each_expr_postorder`.
- Errors with span: no `clock` or more than one, duplicate deadline name, `within_us < period_us`, `latch`/`response` not a declared state variable of type `Bool` (check the response only if it is a bare variable; otherwise it is type-checked later as an ordinary expression).
- After lowering, `clocks` and `deadlines` are empty.

- [ ] **Step 1: Write failing tests** (each builds a small system: `phase` enum state, `detected` and `heater_off` Bool, a controller reacting after `r` extra scans):
  - `deadline_met_exactly_at_bound_passes`: period 1ms, within 3ms, reaction in 3 scans → `bil model-check` exit 0.
  - `deadline_missed_by_one_scan_fails`: same, reaction in 4 scans → exit 1, output contains `Deadline_Cut`.
  - `non_multiple_rounds_up`: period 2ms, within 5ms (n = 3); reaction in 3 scans passes, in 4 fails.
  - `latch_cleared_before_response_fails`: a transition clears `detected` with `heater_off` false → output contains `Latch_Cut`.
  - `phase_change_keeps_original_bound`: bound 2 ms in `Growth`, 20 ms in `Anneal`; latch set in `Growth`, a transition moves to `Anneal`, reaction at scan 3 → fails.
  - `deadline_shorter_than_period_rejected`, `deadline_without_clock_rejected`.
  - `symbolic_bmc_agrees`: the missed-by-one system also fails under `bil model-check --bmc` (use the flag the CLI exposes for `symbolic_bmc_program`; check `src/cli.rs`).
- [ ] **Step 2: Run** — Expected: FAIL.
- [ ] **Step 3: Implement** `lower_program` per the contract above. Settle the exact update expression with the boundary tests, not by reasoning alone; they pin the semantics.
- [ ] **Step 4: Run** `cargo test --test timed_guards` and `cargo test` — Expected: PASS, no existing test changes.
- [ ] **Step 5: Commit** `feat(timed): lower clock/deadline into counters and invariants`.

### Task 3: Domain example and seeded bug

**Files:** Modify `examples/domains/semiconductor_se_spe.bil`; create `examples/domains/seeded_bugs/spe_late_cutoff.bil`; modify `tests/domain_examples.rs`.

**Interfaces:** Consumes Task 2. `SEEDED` entries are `(file, command, exit_code, needle)`.

- [ ] **Step 1: Write the failing test**: add `("spe_late_cutoff.bil", "model-check", 1, "Deadline_")` to `SEEDED`, matching the file's name in sorted order; the existing test also checks every file in the dir is listed.
- [ ] **Step 2: Run** `cargo test --test domain_examples` — Expected: FAIL (file missing).
- [ ] **Step 3: Implement** in `SpeAnneal`: add `state detected: Bool = false`, `clock scan period 1ms`, `deadline CutOnDetect: detected => !lamp within 3ms in phase == Soak`, plus a transition that raises `detected` and one that turns the lamp off. Comment the numbers "illustrative placeholder, not a process figure". The seeded variant adds one extra scan before the lamp turns off.
- [ ] **Step 4: Run** `cargo test --test domain_examples` — Expected: PASS (all models still pass the five commands).
- [ ] **Step 5: Commit** `feat(examples): detect-to-cutoff deadline in the SPE anneal`.

### Task 4: Docs and gate

**Files:** `docs/SEMANTICS.md` (§4.4 "Timed guards": the counter semantics, rounding, latch rule, phase rule), `CHANGELOG.md`, `docs/whitepaper/` §8 (move the item from roadmap to done; no new domain claims), README feature list if it names system features.

- [ ] **Step 1:** Write the docs; every number in them comes from the tests.
- [ ] **Step 2: Run** `scripts/ci.sh` — Expected: `all checks passed`.
- [ ] **Step 3: Commit** `docs: timed guards`. Do not push; ask first.
