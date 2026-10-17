# Conventions (`bil`)

- **Rust Style**: Standard `rustfmt` / Edition 2021 idioms; zero compiler warnings (`cargo check`, `cargo test`).
- **Error Diagnostics**: All frontend/static errors (`LexError`, `ParseError`, `OntologyError`, `TypeError`) carry `Span { line, col }` coordinates.
- **Dual Syntax Parity**: Every logical and GCL operator must support both ASCII (`forall`, `exists`, `=>`, `<=>`, `&&`, `||`, `!`, `[]`, `->`, `<:`, `|>`) and Unicode (`∀`, `∃`, `⇒`, `⇔`, `∧`, `∨`, `¬`, `▯`, `→`, `⊑`, `▷`).
- **Verification First**: Every example in `examples/*.bil` must pass `bil all` (`check` + `verify` + `model-check` + `run`) and `bil emit-verus` in integration tests.
