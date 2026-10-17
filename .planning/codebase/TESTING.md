# Testing (`bil`)

## Local Verification Commands
```bash
# Run full unit & integration test suite (8 tests covering DAG linting, HM subtyping, WP, Model Checking, Verus codegen, and all 5 examples)
cargo test

# Run full verification & execution pipeline on an example
cargo run -- all examples/smart_grid.bil --trace

# Emit Verus Rust verification code
cargo run -- emit-verus examples/gcd_refinement.bil
```
