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

# Stdin program: feed the same input to `lean --run` and to node (out-stdin.mjs),
# diffing stdout. Exercises IO.getStdin / Stream.getLine over a piped fd 0.
printf 'alpha\nbeta\ngamma\n' > /tmp/stdin-in.txt
lake env lean --run expected-stdin.lean < /tmp/stdin-in.txt > /tmp/lean-stdin.out 2>&1
node out-stdin.mjs < /tmp/stdin-in.txt > /tmp/ts-stdin.out 2>&1
echo "=== STDIN LEAN ==="; cat /tmp/lean-stdin.out
echo "=== STDIN node ===";  cat /tmp/ts-stdin.out
if diff -q /tmp/lean-stdin.out /tmp/ts-stdin.out >/dev/null; then
  echo "STDIN-DIFF-TEST PASS: stdout identical"
else
  echo "STDIN-DIFF-TEST FAIL"; diff /tmp/lean-stdin.out /tmp/ts-stdin.out || true; exit 1
fi

# Error program: a userError throw must print the same Lean-format stderr
# ("uncaught exception: ...") and exit 1 under both `lean --run` and node.
LEAN_EC=0; lake env lean --run expected-err.lean > /tmp/lean-err.out 2> /tmp/lean-err.err || LEAN_EC=$?
NODE_EC=0; node out-err.mjs > /tmp/ts-err.out 2> /tmp/ts-err.err || NODE_EC=$?
echo "=== ERR LEAN stderr ==="; cat /tmp/lean-err.err
echo "=== ERR node stderr ===";  cat /tmp/ts-err.err
if diff -q /tmp/lean-err.out /tmp/ts-err.out >/dev/null \
   && diff -q /tmp/lean-err.err /tmp/ts-err.err >/dev/null \
   && [ "$LEAN_EC" = "$NODE_EC" ]; then
  echo "ERR-DIFF-TEST PASS: stdout+stderr+exit($LEAN_EC) identical"
else
  echo "ERR-DIFF-TEST FAIL (lean exit=$LEAN_EC node exit=$NODE_EC)"
  echo "--- stdout diff ---"; diff /tmp/lean-err.out /tmp/ts-err.out || true
  echo "--- stderr diff ---"; diff /tmp/lean-err.err /tmp/ts-err.err || true
  exit 1
fi

# Panic program: compiled `panic!`/`List.head!` must print the PANIC message to
# stderr, return the Inhabited default, and CONTINUE (no abort, exit 0), exactly
# like Lean. `LEAN_BACKTRACE=0` suppresses Lean's synthetic backtrace so only the
# PANIC lines remain (node emits no backtrace); stdout+stderr+exit are diffed.
LEAN_EC=0; LEAN_BACKTRACE=0 lake env lean --run expected-panic.lean > /tmp/lean-panic.out 2> /tmp/lean-panic.err || LEAN_EC=$?
NODE_EC=0; LEAN_BACKTRACE=0 node out-panic.mjs > /tmp/ts-panic.out 2> /tmp/ts-panic.err || NODE_EC=$?
echo "=== PANIC LEAN stdout ==="; cat /tmp/lean-panic.out
echo "=== PANIC LEAN stderr ==="; cat /tmp/lean-panic.err
echo "=== PANIC node stdout ===";  cat /tmp/ts-panic.out
echo "=== PANIC node stderr ===";  cat /tmp/ts-panic.err
if diff -q /tmp/lean-panic.out /tmp/ts-panic.out >/dev/null \
   && diff -q /tmp/lean-panic.err /tmp/ts-panic.err >/dev/null \
   && [ "$LEAN_EC" = "$NODE_EC" ]; then
  echo "PANIC-DIFF-TEST PASS: stdout+stderr+exit($LEAN_EC) identical"
else
  echo "PANIC-DIFF-TEST FAIL (lean exit=$LEAN_EC node exit=$NODE_EC)"
  echo "--- stdout diff ---"; diff /tmp/lean-panic.out /tmp/ts-panic.out || true
  echo "--- stderr diff ---"; diff /tmp/lean-panic.err /tmp/ts-panic.err || true
  exit 1
fi
