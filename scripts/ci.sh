#!/usr/bin/env bash
# Local CI gate for bil. There is no hosted CI: run this before pushing.
#
#   scripts/ci.sh                 clippy, tests under coverage (78% line floor), cargo audit,
#                                 and the Verus emit tests when verus is found (else "verus: skipped")
#   scripts/ci.sh --fuzz [SECS]   also fuzz lex/parse/check for SECS seconds each (default 300)
#
# Needs: cargo-llvm-cov, cargo-audit, z3 on PATH or in ~/.local/bin;
# optionally verus (version pinned in scripts/VERUS_VERSION; $VERUS or PATH);
# for --fuzz, a nightly toolchain and cargo-fuzz.
set -euo pipefail
cd "$(dirname "$0")/.."

COVERAGE_FLOOR=78 # 80.7% lines on 2026-10-23 (76.2% on 2026-10-21); raise as coverage improves
fuzz_secs=0
while (($#)); do
  case "$1" in
    --fuzz)
      fuzz_secs=300
      if [[ ${2:-} =~ ^[0-9]+$ ]]; then fuzz_secs=$2; shift; fi
      ;;
    -h | --help)
      sed -n '2,10p' "$0"
      exit 0
      ;;
    *)
      echo "ci.sh: unknown option '$1'" >&2
      exit 2
      ;;
  esac
  shift
done

step() { printf '\n==> %s\n' "$*"; }
need() { command -v "$1" >/dev/null || { echo "ci.sh: missing $1 ($2)" >&2; exit 1; }; }

need cargo-llvm-cov "cargo install --locked cargo-llvm-cov"
need cargo-audit "cargo install --locked cargo-audit"
if ! command -v z3 >/dev/null && [[ ! -x $HOME/.local/bin/z3 ]]; then
  echo "ci.sh: z3 not found on PATH or in ~/.local/bin; solver-dependent tests would not be meaningful" >&2
  exit 1
fi

step "clippy"
cargo clippy --all-targets -- -D warnings

step "tests under coverage (floor ${COVERAGE_FLOOR}% lines)"
# A dedicated target dir keeps profiles from other (e.g. nightly --branch) runs out of the totals.
CARGO_LLVM_COV_TARGET_DIR=target/ci-cov \
  cargo llvm-cov --lcov --output-path target/ci-cov/lcov.info --fail-under-lines "$COVERAGE_FLOOR"
CARGO_LLVM_COV_TARGET_DIR=target/ci-cov cargo llvm-cov report --summary-only | tail -n1

step "verus (emitted code must verify; seeded safety bugs must be rejected)"
verus_bin=${VERUS:-$(command -v verus || true)}
if [[ -z $verus_bin || ! -x $verus_bin ]]; then
  echo "verus: skipped (not found; set VERUS or put verus on PATH; pinned $(cat scripts/VERUS_VERSION))"
else
  verus_want=$(cat scripts/VERUS_VERSION)
  verus_have=$("$verus_bin" --version | sed -n 's/^ *Version: *//p' | head -n1)
  if [[ $verus_have != *"$verus_want"* ]]; then
    echo "ci.sh: verus version '${verus_have:-unknown}' differs from pinned $verus_want" >&2
    exit 1
  fi
  VERUS=$verus_bin cargo test -q --test verus_emit
fi

step "cargo audit"
cargo audit

if ((fuzz_secs > 0)); then
  need cargo-fuzz "cargo install --locked cargo-fuzz"
  for target in lex parse check; do
    step "fuzz $target (${fuzz_secs}s)"
    mkdir -p "fuzz/corpus/$target"
    cp examples/*.bil "fuzz/corpus/$target/"
    cargo +nightly fuzz run "$target" -- \
      -max_total_time="$fuzz_secs" -max_len=4096 -timeout=10 -rss_limit_mb=2048
  done
fi

step "all checks passed"
