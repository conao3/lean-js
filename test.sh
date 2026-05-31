#!/usr/bin/env bash
# Diff-test: regenerate out.ts, run Lean #eval vs generated TS via node.
# Usage: nix develop ../lean-todo-app --command bash -c "cd $(pwd) && ./test.sh"
set -euo pipefail
lake build
lake exe lean-js out.ts
lake env lean --run expected.lean | grep -E 'double|mkShifted' > /tmp/lean.out
node test.mjs > /tmp/ts.out
echo "=== LEAN (expected) ==="; cat /tmp/lean.out
echo "=== TS (node) ===";      cat /tmp/ts.out
if diff -q /tmp/lean.out /tmp/ts.out >/dev/null; then
  echo "DIFF-TEST PASS: outputs identical"
else
  echo "DIFF-TEST FAIL"; diff /tmp/lean.out /tmp/ts.out; exit 1
fi
