# `bil` Formal Semantics Reference

This document specifies the operational, axiomatic, and model-theoretic semantics of **Bounded Invariant Logic (`bil`)** across its four execution and verification backends:

1. **Tree-Walk Evaluator (`src/eval.rs`)**
2. **Register/Stack Bytecode Virtual Machine (`src/vm.rs`)**
3. **Standalone Native ELF AOT Compiler (`src/codegen.rs`)**
4. **Dijkstra Weakest-Precondition (`src/wp.rs`) & SMT-LIB2 Bridge (`src/smt.rs`)**

---

## 1. Integer Arithmetic & Overflow Semantics (`src/semantics.rs`)

### 1.1 Runtime Execution (`eval`, `vm`, Native AOT)
All three executable backends enforce identical **64-bit signed two's-complement (`i64`) checked arithmetic** paired with **SMT-LIB2 Euclidean division and modulus**:

- **Checked Addition, Subtraction, Multiplication, and Negation**:
  - `a + b`, `a - b`, `a * b`, and `-a` use `i64::checked_add`, `i64::checked_sub`, `i64::checked_mul`, and `i64::checked_neg`.
  - Any signed 64-bit overflow (including `i64::MIN / -1` and `-i64::MIN`) immediately raises a deterministic `RuntimeError` (`Integer overflow in ...`) rather than wrapping or panicking differently across debug/release profiles.
- **Euclidean Division (`div_euclid_i64`) and Modulus (`mod_euclid_i64`)**:
  - For any $a \in \mathbb{Z}$ and $b \in \mathbb{Z} \setminus \{0\}$, Euclidean division $(q, r) = (a \;\text{div}\; b, a \;\text{mod}\; b)$ satisfies:
    $$a = b \cdot q + r \quad \text{and} \quad 0 \le r < |b|$$
  - Example: `(-7) / 3 == -3` and `(-7) % 3 == 2` (matching SMT-LIB2 `(div (- 7) 3)` and `(mod (- 7) 3)`).

### 1.2 Unbounded SMT-LIB2 `Int` vs. Runtime `i64`
- In SMT-LIB2 (`src/smt.rs`), `Int` denotes mathematical integers $\mathbb{Z}$ without 64-bit upper/lower bounds.
- In bounded counterexample search (`src/wp.rs`), any expression that triggers an `i64` arithmetic overflow or division-by-zero is treated as a **refutation (`Status::Refuted`)** of the verification condition unless precluded by the function's `requires` precondition.

---

## 2. Open-World vs. Closed-World Concept Quantification

`bil` supports First-Order Logic (FOL) quantification over OntoLogic concepts (`forall x in Concept : P(x)` and `exists x in Concept : P(x)`):

| Backend | Semantic Interpretation | Domain of Quantification |
| :--- | :--- | :--- |
| **`bil solve` / `bil verify` (SMT-LIB2)** | **Open-World Assumption (OWA)** | Guarded quantifier relativization over an uninterpreted sort `Entity`: `(forall ((x Entity)) (=> (is_Concept x) P(x)))`. Holds across all possible models of the ontology. |
| **`bil verify` (Bounded Counterexample Finder)** | **Finite Herbrand / Skewed Witness Sampling** | Probes boundary integer constants ($c-1, c, c+1$), homogeneous and skewed multi-field `ConceptInstance` combinations, ADT variants, and subconcepts. |
| **`bil run` / `bil vm` / `bil build` (Runtime)** | **Closed-World Assumption (CWA)** | Quantifies strictly over the finite set of `ConceptInstance` values materialized in the current runtime environment (respecting transitive `<:` subconcept inheritance). |

---

## 3. Guarded Command Language (GCL) & Nondeterminism

### 3.1 Alternative Construct (`if ... fi`)
Given guarded branches $G_1 \rightarrow S_1 \;\talloblong\; \dots \;\talloblong\; G_n \rightarrow S_n$:
- **Guard Totality ($BB$)**: $BB \equiv \bigvee_{i=1}^n G_i$.
- **Operational Semantics**: All guards $G_i$ are evaluated in the pre-state. The set of enabled branches $E = \{i \mid \llbracket G_i \rrbracket = \text{true}\}$ is collected:
  - If $E = \emptyset$, execution **aborts** immediately (`if..fi aborted: no guard satisfied (¬BB)`).
  - If $|E| = 1$, the unique enabled branch executes deterministically.
  - If $|E| > 1$, a branch is selected using the deterministic SplitMix64 PRNG seeded by `--seed <N>`.
- **Weakest Precondition (`wp`)**:
  $$\text{wp}(\texttt{if } \talloblong G_i \rightarrow S_i \texttt{ fi}, Q) \equiv \left(\bigvee_{i=1}^n G_i\right) \wedge \bigwedge_{i=1}^n \left(G_i \Rightarrow \text{wp}(S_i, Q)\right)$$

### 3.2 Repetitive Construct (`do ... od`)
Given loop state initializers $\vec{v} := \vec{e}_0$, invariant $I$, variant $V$, and guarded branches $G_i \rightarrow S_i$:
- **Operational Semantics**: While $BB$ holds, an enabled branch is chosen via the seeded PRNG, the variant $V$ is checked for non-negativity ($V \ge 0$) and strict decrease ($V_{\text{next}} < V_{\text{prev}}$), and state variables $\vec{v}$ are updated simultaneously.
- **Five-Point Total Correctness Proof Obligations**:
  1. **Initialization**: $\text{Pre} \Rightarrow I[\vec{v} \mapsto \vec{e}_0]$
  2. **Preservation**: $\forall i.\; (I \wedge G_i) \Rightarrow \text{wp}(S_i, I)$
  3. **Variant Non-Negativity**: $\forall i.\; (I \wedge G_i) \Rightarrow V \ge 0$
  4. **Variant Strict Decrease**: $\forall i.\; (I \wedge G_i) \Rightarrow \text{wp}(S_i, V < V_0)$
  5. **Exit Postcondition**: $(I \wedge \neg BB) \Rightarrow \text{Post}[\texttt{result} \mapsto e_{\text{then}}]$


### 3.3 Recursive Functions (`fn … variant V`)
A function $f$ with precondition $P$, postcondition $Q$ and variant $V$ is verified modularly. In a Verification Condition, a call $f(\vec{a})$ outside any activation of $f$ is unfolded into $f$'s body. A call $f(\vec{b})$ inside an unfolded activation $f(\vec{a})$ is replaced by a fresh value $r$, with:
- **Checked at the call**: $P[\vec{x} \mapsto \vec{b}] \wedge 0 \le V[\vec{x} \mapsto \vec{a}] \wedge V[\vec{x} \mapsto \vec{b}] < V[\vec{x} \mapsto \vec{a}]$
- **Assumed for $r$**: that check $\Rightarrow Q[\vec{x} \mapsto \vec{b}, \texttt{result} \mapsto r]$

The variant bounds every chain of recursive calls, so the assumption is the induction hypothesis that $f$'s own contract obligation discharges. Without a `variant`, a recursive call is not encoded and its obligation is only bounded-checked. An `if … fi` in a function body gets a fresh value $r$ with $\bigvee_i G_i$ checked and $\bigvee_i G_i \Rightarrow \bigvee_i (G_i \wedge r = E_i)$ assumed, so the obligation must hold for every enabled branch. Every assumption is guarded by the check that makes it satisfiable, so a failed check cannot be hidden by a false hypothesis.

---

## 4. Explicit-State & LTL Model Checking (`src/model_check.rs`)

### 4.1 Canonical State Hashing & Completeness
- States $\sigma : \text{Var} \rightarrow \text{Value}$ are hashed using an injective length-prefixed canonical encoding (`encode_value_canonical`), preventing collisions across strings containing delimiters (`;`, `=`), nested lists, and `ConceptInstance` records.
- If the state space exceeds `--max-states N`, exploration halts and sets `report.complete = false` (`truncated_at = Some(N)`). Frontier states whose outgoing transitions were not expanded are recorded in `truncated_frontier` and are **never** misclassified as terminal deadlocks or liveness violations.

### 4.2 Temporal Logic & Weak Fairness (Justice)
- **`always P` ($\Box P$)**: Verified across all reachable states.
- **`eventually Q` ($\Diamond Q$) and `P ~> Q` ($\Box(P \Rightarrow \Diamond Q)$)**:
  - Verified via **Tarjan Strongly Connected Component (SCC)** decomposition of the $\neg Q$ reachable subgraph combined with **Weak Fairness (Justice)**.
  - A $\neg Q$ cycle $C$ is a genuine liveness violation (lasso counterexample) if and only if no transition $t$ that exits $C$ is continuously enabled across every state $s \in C$.

### 4.3 Timed Guards (`clock` / `deadline`, `src/timed.rs`)
Time is discrete: one transition firing is one scan of the controller. `clock scan period P` declares the scan period, and `deadline D: L => R within W [in G]` requires that once the latch `L` is seen (while the phase guard `G` holds, default always), the response `R` holds within `W`. With $n = \lceil W / P \rceil$ scans, the response must hold in the state after the $n$-th scan counted from the first scan that starts with $L$ true. So $W = P$ is achievable (the very next scan may respond), $W < P$ is rejected, and a $W$ that is not a multiple of $P$ rounds up.

The pass runs right after parsing and lowers each deadline $D$ into ordinary state, so every checker sees a plain system. Reading the pre-state of each scan:
- `__run_D` $\leftarrow (\texttt{run} \vee (G \wedge L)) \wedge \neg R$ — the timer is pending. $G$ is read only to *start* it, so a phase change does not stop a running timer and the bound of the phase that saw the latch keeps applying.
- `__t_D` $\leftarrow$ `__t_D + 1` if pending, else $0$ — consecutive pending scans.
- Invariant `Deadline_D`: `__t_D >= n => R`. Invariant `Latch_D`: `__run_D => (L || R)`, so a latch cleared before the response is a violation.
- Invariant `Stall_D`: pending $\Rightarrow$ some transition guard is enabled. The counter only advances when a transition fires, so a terminal or deadlocked state with the latch set and no response would otherwise freeze it below $n$ and pass.

The `__` prefix is reserved in a system that declares a deadline (no state or update may use it), and a user invariant may not be named `Deadline_D`, `Latch_D` or `Stall_D`.

The latch is a `Bool` state variable declared by the user; setting it while already set changes nothing, which models a latched, synchronous signal that is never lost. Both the explicit-state search and `model-check --bmc` check the lowered invariants. For `--bmc`, the two-branch `if g -> a [] !g -> b fi` that the counter uses is encoded as `ite`; any other `if … fi` is still not encoded. `--bmc` reports `BMC not applicable to system …` and exits 1 for a system it cannot encode, rather than staying silent.
