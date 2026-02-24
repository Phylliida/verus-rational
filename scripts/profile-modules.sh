#!/usr/bin/env bash
set -euo pipefail

# Strip leaked ghost cfg flags that break stable cargo flows
unset RUSTFLAGS
unset CARGO_ENCODED_RUSTFLAGS
if [[ -z "${TMPDIR:-}" || ! -d "${TMPDIR:-/nonexistent}" || ! -w "${TMPDIR:-/nonexistent}" ]]; then
  export TMPDIR="/tmp"
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
usage: ./scripts/profile-modules.sh [--raw]

Run full crate verification with per-function timing enabled and print a
sorted breakdown showing where verification time is spent.

options:
  --raw   print raw Verus output instead of the sorted summary
  -h      show this help
EOF
  exit 0
fi

RAW=0
if [[ "${1:-}" == "--raw" ]]; then
  RAW=1
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  echo "error: cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 1
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "error: expected patched z3 at $VERUS_SOURCE/z3"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 1
fi

LOG_FILE="$(mktemp)"
trap 'rm -f "$LOG_FILE"' EXIT

run_cargo_verus() {
  if command -v rustup >/dev/null 2>&1; then
    export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
    export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
    export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
    cd "$ROOT_DIR"
    cargo verus verify --manifest-path Cargo.toml -p verus-rational \
      -- --time-expanded --triggers-mode silent 2>&1 | tee "$LOG_FILE"
  elif command -v nix-shell >/dev/null 2>&1; then
    nix-shell -p rustup --run "
      set -euo pipefail
      export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
      export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
      export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
      cd '$ROOT_DIR'
      cargo verus verify --manifest-path Cargo.toml -p verus-rational \
        -- --time-expanded --triggers-mode silent 2>&1 | tee '$LOG_FILE'
    "
  else
    echo "error: neither rustup nor nix-shell found in PATH"
    exit 1
  fi
}

echo "=== verus-rational function profile ==="
echo ""

WALL_START="$(date +%s)"
set +e
run_cargo_verus
VERUS_STATUS=$?
set -e
WALL_END="$(date +%s)"
WALL_ELAPSED=$((WALL_END - WALL_START))

if [[ $RAW -eq 1 ]]; then
  exit $VERUS_STATUS
fi

echo ""
echo "=== sorted by time (descending) ==="
echo ""

# Extract timing lines from Verus --time-expanded output and sort them.
# Verus typically emits lines like:
#   <time>s   <module>::<function>
# We try several common patterns and print whatever we find, sorted.
if command -v rg >/dev/null 2>&1; then
  rg -No '^\s*([0-9]+\.[0-9]+)s\s+(.+)$' -r '$1 $2' "$LOG_FILE" \
    | sort -t' ' -k1 -rn \
    | while IFS=' ' read -r secs rest; do
        printf "  %8ss  %s\n" "$secs" "$rest"
      done
else
  grep -oP '^\s*\K[0-9]+\.[0-9]+s\s+.+' "$LOG_FILE" \
    | sort -t's' -k1 -rn
fi

echo ""
echo "  wall clock: ${WALL_ELAPSED}s"
echo ""

# Print verification summary line if present
rg -o 'verification results::.*' "$LOG_FILE" 2>/dev/null || true

exit $VERUS_STATUS
