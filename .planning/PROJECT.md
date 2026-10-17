# Project: `bil` (Bounded Invariant Logic)

## Mission
`bil` is a mathematically grounded, statically typed formal verification, ontology, and functional data language written in Rust. It eliminates the specification-implementation split by uniting **OntoLogic** (Basic Formal Ontology + First-Order Logic), **Dijkstra's Guarded Command Language (GCL)**, **Refinement Calculus**, **SPIN/Promela-style Explicit-State Model Checking**, **Verus-compatible Deductive Rust Verification**, and **Hindley-Milner Functional Data Pipelines**.

## Core Pillars
1. **Programs Correct by Construction**: Weakest Precondition (`wp`) predicate transformer calculus and Refinement Calculus (`refines` / `⊑`) prove loop invariants, variant termination bounds, guard totality ($BB = \bigvee G_i$), and postconditions alongside code.
2. **Embracing True Nondeterminism**: Guarded choices (`[]` / `▯`) and nondeterministic selection (`choose x in S : P(x)`) defer implementation details and model concurrent/asynchronous hardware and distributed protocols cleanly.
3. **Foundation for Formal Methods**: Reactive `system` blocks verified via explicit-state BFS model checking (`bil model-check`) and compiled to Verus Rust (`bil emit-verus`) or native binaries via a 3-level IR (`HIR` $\to$ `VIR` $\to$ `LIR`).

## Target Domains & Practical Applications
1. **Industrial IoT, SCADA & Smart Energy** (`examples/smart_grid.bil`)
2. **Distributed Systems & Network Protocols** (`examples/mutex_protocol.bil`)
3. **Hardware, Hypervisors & Asynchronous Arbiters** (`examples/arbiter_controller.bil`)
4. **Safety-Critical Verified Algorithms** (`examples/gcd_refinement.bil`)
5. **Zero-Trust Cloud & Certificate Policy Auditing** (`examples/security_policy.bil`)
