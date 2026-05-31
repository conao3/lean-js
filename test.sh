#!/usr/bin/env bash
# Diff-test: regenerate out.ts, run Lean reference vs generated TS via node.
# Usage: nix develop . --command bash -c "./test.sh"
set -euo pipefail
lake build
lake exe lean-js out.ts prelude.ts out-io.mjs
lake env lean --run expected.lean > /tmp/lean.out
node test.mjs > /tmp/ts.out
echo "=== LEAN (expected) ==="; cat /tmp/lean.out
echo "=== TS (node) ===";      cat /tmp/ts.out
if diff -q /tmp/lean.out /tmp/ts.out >/dev/null; then
  echo "DIFF-TEST PASS: outputs identical"
else
  echo "DIFF-TEST FAIL"; diff /tmp/lean.out /tmp/ts.out; exit 1
fi

# Deep mutual/cross-function TCO: node-side no-stack-overflow check at large N.
node test-tco.mjs
echo "--- TCO deep check done ---"

# Fail-loud extern link check (negative test): an unmapped extern must be a hard
# extraction error, not a dangling runtime call.
lake env lean --run test-extern.lean
echo "--- extern link check done ---"

# Runnable IO program: run the same Lean `main` under `lean --run` and under
# node (generated out-io.mjs), diffing stdout and stderr separately.
lake env lean --run expected-io.lean > /tmp/lean-io.out 2> /tmp/lean-io.err
node out-io.mjs > /tmp/ts-io.out 2> /tmp/ts-io.err
echo "=== IO LEAN stdout ==="; cat /tmp/lean-io.out
echo "=== IO node stdout ===";  cat /tmp/ts-io.out
if diff -q /tmp/lean-io.out /tmp/ts-io.out >/dev/null && diff -q /tmp/lean-io.err /tmp/ts-io.err >/dev/null; then
  echo "IO-DIFF-TEST PASS: stdout+stderr identical"
else
  echo "IO-DIFF-TEST FAIL"
  echo "--- stdout diff ---"; diff /tmp/lean-io.out /tmp/ts-io.out || true
  echo "--- stderr diff ---"; diff /tmp/lean-io.err /tmp/ts-io.err || true
  exit 1
fi
