# verus-rational
Exact rational numbers in verus (formally verified rust), using verus-bigint

## Checking

- Run all checks:
  - `./scripts/check.sh`
- Run strict checks (fail if Verus tools are unavailable, fail on trusted-escape patterns in non-test `src/` files including `#[verifier::exec_allows_no_decreases_clause]` and `unsafe`, and gate against verification-count regressions):
  - `./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 689`
- Run the CI-equivalent strict gate locally (kept aligned with `.github/workflows/check.yml` by `check.sh`, including strict command flags and Verus toolchain pin):
  - `./scripts/check.sh --require-verus --forbid-trusted-escapes --min-verified 689`
  - It also preflights CI trigger coverage so strict checks remain wired to both `pull_request` and `push` on `main`, and rejects trigger filters (`paths*`, `branches-ignore`) that could silently skip enforcement.
  - It also preflights the CI `verify` job execution contract (no job-level `if:` gating, no job-level `continue-on-error`, and explicit `timeout-minutes`).
  - It also preflights CI runner posture for `verify`: `runs-on` must stay pinned to `ubuntu-22.04`, with no dynamic runner expressions and no `self-hosted` labels.
  - It also preflights CI toolchain-install wiring so `Install required Rust toolchain` remains fail-fast, runs before build/strict steps, installs the pinned toolchain with `--profile minimal` plus required components (`rustfmt`, `rustc-dev`, `llvm-tools`), and sets `rustup default` to that same pin.
  - This also preflights workflow checkout + structure wiring so CI keeps the required end-to-end setup (`Checkout verus-rational` path, `Checkout Verus` repository/path, `Checkout verus-bigint` repository/path, all three checkout steps pinned to `actions/checkout@v4.2.2`, `Build Verus tools` before strict checks, expected working directories, and `VERUS_ROOT` env wiring) and enforces fail-fast step behavior (`set -euo pipefail`, no step-level `if:` gating, no `continue-on-error: true`, no `|| true` masking).
  - It also preflights CI workflow permission hardening (`permissions: contents: read`) and checkout credential hygiene (`persist-credentials: false` on all three checkout steps).
- Run checks in offline mode where possible:
  - `./scripts/check.sh --offline`
