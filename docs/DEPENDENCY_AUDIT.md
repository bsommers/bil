# Dependency Security & Supply Chain Audit Report

**Date:** `2026-10-17`  
**Ecosystem:** `Rust (Cargo.toml / Cargo.lock v4)`  
**Total Dependencies Audited:** `11` (`2` direct, `9` transitive)  
**Security Status:** `Clean (0 Vulnerabilities Detected)`

---

## 1. 🚨 Vulnerability Summary (CVEs)

No known CVEs or RustSec advisories were detected across any direct or transitive crate in [Cargo.toml](file:///home/bill/src/lang/bil/Cargo.toml) or [Cargo.lock](file:///home/bill/src/lang/bil/Cargo.lock).

| Severity | Count | Status |
| :--- | :---: | :--- |
| **🚨 CRITICAL (9.0–10.0)** | `0` | Clean |
| **⚠️ HIGH (7.0–8.9)** | `0` | Clean |
| **⚡ MEDIUM (4.0–6.9)** | `0` | Clean |
| **ℹ️ LOW (0.1–3.9)** | `0` | Clean |

---

## 2. 📦 Dependency Inventory, Maintenance & Version Health

`bil` intentionally maintains an ultra-minimal dependency footprint (`2` direct crates) to minimize supply-chain exposure. All core compiler passes—lexing, Pratt parsing, OntoLogic DAG subsumption, Hindley-Milner type inference, Dijkstra `wp` verification, SMT-LIB2 emission, explicit-state & LTL model checking, 3-level IR (`HIR` $\rightarrow$ `VIR` $\rightarrow$ `LIR`), bytecode VM, and Native AOT Rust codegen—are implemented in-tree with zero third-party runtime dependencies beyond JSON serialization (`--format json`).

| Package | Kind | Installed (`Cargo.lock`) | Latest Track | SemVer Gap | Maintenance Status | Recommendation |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| `serde` | Direct | `1.0.229` | `1.0.x` | Current | Active (`serde-rs`) | Retain |
| `serde_json` | Direct | `1.0.154` | `1.0.x` | Current | Active (`serde-rs`) | Retain |
| `serde_core` | Transitive | `1.0.229` | `1.0.x` | Current | Active (`serde-rs`) | Retain |
| `serde_derive` | Transitive (proc-macro) | `1.0.229` | `1.0.x` | Current | Active (`serde-rs`) | Retain |
| `proc-macro2` | Transitive (build) | `1.0.107` | `1.0.x` | Current | Active (`dtolnay`) | Retain |
| `quote` | Transitive (build) | `1.0.47` | `1.0.x` | Current | Active (`dtolnay`) | Retain |
| `syn` | Transitive (build) | `3.0.9` | `3.0.x` | Current | Active (`dtolnay`) | Retain |
| `unicode-ident` | Transitive (build) | `1.0.27` | `1.0.x` | Current | Active (`dtolnay`) | Retain |
| `itoa` | Transitive | `1.0.18` | `1.0.x` | Current | Active (`dtolnay`) | Retain |
| `memchr` | Transitive | `2.8.3` | `2.8.x` | Current | Active (`BurntSushi`) | Retain |
| `zmij` | Transitive | `1.0.23` | `1.0.x` | Current | Active (`dtolnay`) | Retain |

### Supply-Chain Architecture Observations
1. **Zero Network or TLS Crates**: `bil` has zero HTTP, socket, or OpenSSL/ring dependencies, eliminating network parser CVEs.
2. **Zero Transitive Runtime Dependencies in Native AOT Output**: Binaries produced by `bil build` compile standalone Rust code (`src/runtime_prelude.rs`) using only the Rust standard library (`std`), carrying **0 external crates** at runtime.
3. **Optional External Tooling (`z3`, `cvc5`, `vampire`, `rustc`)**: Invoked out-of-process via parameterized `std::process::Command` arrays with wall-clock timeouts (`SEC.3`) and environment override validation (`SEC.5`).

---

## 3. 📜 License Compliance Scorecard

All `11` dependencies in `Cargo.lock` use permissive, OSI-approved licenses compatible with `bil`'s `MIT` license ([Cargo.toml](file:///home/bill/src/lang/bil/Cargo.toml#L6)). Zero copyleft (`GPL`, `LGPL`, `AGPL`, `MPL`) or non-commercial licenses are present.

| Crate | SPDX License Expression | Category | Compliance Verdict |
| :--- | :--- | :--- | :--- |
| `bil` (root) | `MIT` | Permissive | ✅ Compliant |
| `serde` (`1.0.229`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `serde_json` (`1.0.154`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `serde_core` (`1.0.229`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `serde_derive` (`1.0.229`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `proc-macro2` (`1.0.107`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `quote` (`1.0.47`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `syn` (`3.0.9`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `unicode-ident` (`1.0.27`) | `(MIT OR Apache-2.0) AND Unicode-3.0` | Permissive | ✅ Compliant |
| `itoa` (`1.0.18`) | `MIT OR Apache-2.0` | Permissive | ✅ Compliant |
| `memchr` (`2.8.3`) | `Unlicense OR MIT` | Permissive | ✅ Compliant |
| `zmij` (`1.0.23`) | `MIT` | Permissive | ✅ Compliant |

---

## 4. 🛡️ Supply Chain Recommendations

1. **Keep `Cargo.lock` Committed & Pinned**: Continue committing [Cargo.lock](file:///home/bill/src/lang/bil/Cargo.lock) with SHA-256 registry checksums for reproducible binary builds (`--locked` in CI).
2. **Preserve Zero-Dependency Native AOT Prelude**: Keep [src/runtime_prelude.rs](file:///home/bill/src/lang/bil/src/runtime_prelude.rs) strictly `std`-only so AOT-compiled `.bil` binaries remain 100% self-contained.
