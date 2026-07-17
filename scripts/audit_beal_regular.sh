#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export ELAN_HOME="/Users/mark/beal-lean/.elan"
export PATH="/Users/mark/beal-lean/.git-env/bin:$ELAN_HOME/bin:$PATH"

echo "build: BealRegular"
lake -Kjobs=1 build BealRegular

while IFS= read -r audit; do
  echo "audit: $audit"
  output="$(lake env lean "$audit" 2>&1)" || {
    printf '%s\n' "$output"
    exit 1
  }
  printf '%s\n' "$output"
  if ! node scripts/check_lean_axioms.mjs <<<"$output"; then
    echo "axiom policy violation in $audit" >&2
    exit 1
  fi
done < <(
  {
    printf '%s\n' BealRegularAudit.lean
    rg --files BealRegular | rg 'Audit\.lean$' | sort
  }
)

if rg -n '\b(sorry|admit)\b|\bnative_decide\b|Lean\.ofReduceBool|^[[:space:]]*axiom\b|^[[:space:]]*unsafe\b' \
    --glob '*.lean' BealRegular BealRegular.lean BealRegularAudit.lean; then
  echo "forbidden declaration or proof hook found in source" >&2
  exit 1
fi

node scripts/validate_17_certificates.mjs
node scripts/validate_19_certificates.mjs
node scripts/validate_23_prime2_cube_certificate.mjs
node scripts/validate_23_prime3_cube_certificate.mjs
node scripts/TwentyThreeDesignCount.mjs
node scripts/TwentyThreeRelativeClassNumber.mjs

if [[ -x /opt/homebrew/bin/python3.11 ]]; then
  generated_two="$(mktemp)"
  generated_three="$(mktemp)"
  trap 'rm -f "$generated_two" "$generated_three"' EXIT
  /opt/homebrew/bin/python3.11 scripts/discover_23_prime2_cube_certificate.py >"$generated_two"
  node - "$generated_two" scripts/certificate_23_prime2_cube.json <<'NODE' || {
const assert = require("node:assert/strict");
const fs = require("node:fs");
assert.deepStrictEqual(
  JSON.parse(fs.readFileSync(process.argv[2], "utf8")),
  JSON.parse(fs.readFileSync(process.argv[3], "utf8")),
);
NODE
    echo "p=23 q=2 witness finder did not reproduce its checked JSON" >&2
    exit 1
  }
  /opt/homebrew/bin/python3.11 scripts/discover_23_prime3_cube_certificate.py >"$generated_three"
  node - "$generated_three" scripts/certificate_23_prime3_cube.json <<'NODE' || {
const assert = require("node:assert/strict");
const fs = require("node:fs");
assert.deepStrictEqual(
  JSON.parse(fs.readFileSync(process.argv[2], "utf8")),
  JSON.parse(fs.readFileSync(process.argv[3], "utf8")),
);
NODE
    echo "p=23 q=3 witness finder did not reproduce its checked JSON" >&2
    exit 1
  }
fi

echo "all BealRegular builds, axiom audits, source scans, and validators passed"
