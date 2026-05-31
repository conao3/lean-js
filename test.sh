#!/usr/bin/env bash
# Diff-test: regenerate out.ts, run the NATIVE C-backend oracle vs generated TS
# via node. The oracle is each test program compiled through `lake build` (leanc
# => .lake/build/bin/<name>), i.e. the real production backend with compiled TCO,
# bignum, and libm semantics -- NOT `lean --run`, which is the interpreter and
# overflows the same way naive JS does, masking divergences vs the C backend.
# Usage: nix develop . --command bash -c "./test.sh"
set -euo pipefail
lake build
lake exe lean-js out.ts prelude.ts out-io.mjs
# Compile every oracle program natively once; subsequent runs are lake-cached.
lake build oracle-fns oracle-io oracle-stdin oracle-err oracle-panic oracle-init oracle-stress
ORACLE=.lake/build/bin

# Function-level value equivalence: the native oracle prints every function
# result (same `main` as expected.lean), diffed against node test.mjs.
"$ORACLE/oracle-fns" > /tmp/lean.out
node test.mjs > /tmp/ts.out
echo "=== ORACLE (native) ==="; cat /tmp/lean.out
echo "=== TS (node) ===";      cat /tmp/ts.out
if diff -q /tmp/lean.out /tmp/ts.out >/dev/null; then
  echo "DIFF-TEST PASS: outputs identical"
else
  echo "DIFF-TEST FAIL"; diff /tmp/lean.out /tmp/ts.out; exit 1
fi

# Deep mutual/cross-function TCO: node-side no-stack-overflow check at large N.
node test-tco.mjs
echo "--- TCO deep check done ---"

# 32-bit USize profile: flip WORD_BITS=32 in the generated source and assert the
# usize wrap (2^32) and getNumBits (32). Checked against hand-computed literals
# (a 64-bit host cannot natively produce a 32-bit reference); the 64-bit profile
# is the one the native oracle covers.
node test-usize32.mjs
echo "--- 32-bit USize profile check done ---"

# Fail-loud extern link check (negative test): an unmapped extern must be a hard
# extraction error, not a dangling runtime call. This is an extraction-time check
# (no program to compile), so it stays on the interpreter.
lake env lean --run test-extern.lean
echo "--- extern link check done ---"

# Runnable IO program: run the native oracle binary and node (generated
# out-io.mjs), diffing stdout and stderr separately.
"$ORACLE/oracle-io" > /tmp/lean-io.out 2> /tmp/lean-io.err
node out-io.mjs > /tmp/ts-io.out 2> /tmp/ts-io.err
echo "=== IO ORACLE stdout ==="; cat /tmp/lean-io.out
echo "=== IO node stdout ===";    cat /tmp/ts-io.out
if diff -q /tmp/lean-io.out /tmp/ts-io.out >/dev/null && diff -q /tmp/lean-io.err /tmp/ts-io.err >/dev/null; then
  echo "IO-DIFF-TEST PASS: stdout+stderr identical"
else
  echo "IO-DIFF-TEST FAIL"
  echo "--- stdout diff ---"; diff /tmp/lean-io.out /tmp/ts-io.out || true
  echo "--- stderr diff ---"; diff /tmp/lean-io.err /tmp/ts-io.err || true
  exit 1
fi

# Stdin program: feed the same input to the native oracle and to node
# (out-stdin.mjs), diffing stdout. Exercises IO.getStdin / Stream.getLine.
printf 'alpha\nbeta\ngamma\n' > /tmp/stdin-in.txt
"$ORACLE/oracle-stdin" < /tmp/stdin-in.txt > /tmp/lean-stdin.out 2>&1
node out-stdin.mjs < /tmp/stdin-in.txt > /tmp/ts-stdin.out 2>&1
echo "=== STDIN ORACLE ==="; cat /tmp/lean-stdin.out
echo "=== STDIN node ===";    cat /tmp/ts-stdin.out
if diff -q /tmp/lean-stdin.out /tmp/ts-stdin.out >/dev/null; then
  echo "STDIN-DIFF-TEST PASS: stdout identical"
else
  echo "STDIN-DIFF-TEST FAIL"; diff /tmp/lean-stdin.out /tmp/ts-stdin.out || true; exit 1
fi

# Error program: a userError throw must print the same Lean-format stderr
# ("uncaught exception: ...") and exit 1 under both the native oracle and node.
LEAN_EC=0; "$ORACLE/oracle-err" > /tmp/lean-err.out 2> /tmp/lean-err.err || LEAN_EC=$?
NODE_EC=0; node out-err.mjs > /tmp/ts-err.out 2> /tmp/ts-err.err || NODE_EC=$?
echo "=== ERR ORACLE stderr ==="; cat /tmp/lean-err.err
echo "=== ERR node stderr ===";    cat /tmp/ts-err.err
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
LEAN_EC=0; LEAN_BACKTRACE=0 "$ORACLE/oracle-panic" > /tmp/lean-panic.out 2> /tmp/lean-panic.err || LEAN_EC=$?
NODE_EC=0; LEAN_BACKTRACE=0 node out-panic.mjs > /tmp/ts-panic.out 2> /tmp/ts-panic.err || NODE_EC=$?
echo "=== PANIC ORACLE stdout ==="; cat /tmp/lean-panic.out
echo "=== PANIC ORACLE stderr ==="; cat /tmp/lean-panic.err
echo "=== PANIC node stdout ===";    cat /tmp/ts-panic.out
echo "=== PANIC node stderr ===";    cat /tmp/ts-panic.err
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

# Init program: an `@[init]` action chain (banners, run before main in decl
# order) plus an `initialize` value global (bound at startup, read/mutated by
# main). Diff stdout against the native oracle to prove the module-init chain runs.
"$ORACLE/oracle-init" > /tmp/lean-init.out 2>&1
node out-init.mjs > /tmp/ts-init.out 2>&1
echo "=== INIT ORACLE ==="; cat /tmp/lean-init.out
echo "=== INIT node ===";    cat /tmp/ts-init.out
if diff -q /tmp/lean-init.out /tmp/ts-init.out >/dev/null; then
  echo "INIT-DIFF-TEST PASS: stdout identical"
else
  echo "INIT-DIFF-TEST FAIL"; diff /tmp/lean-init.out /tmp/ts-init.out || true; exit 1
fi

# Stress program: six realistic self-contained programs (recursive-descent
# parser, sorting/BST/HashMap/TreeMap, String processing, numeric algorithms
# incl. bignum factorial and prime sieve, StateM/ExceptT/Option/Except monadic
# code, List/Array combinators). Diff stdout against the native oracle.
"$ORACLE/oracle-stress" > /tmp/lean-stress.out 2>&1
node out-stress.mjs > /tmp/ts-stress.out 2>&1
echo "=== STRESS ORACLE ==="; cat /tmp/lean-stress.out
echo "=== STRESS node ===";    cat /tmp/ts-stress.out
if diff -q /tmp/lean-stress.out /tmp/ts-stress.out >/dev/null; then
  echo "STRESS-DIFF-TEST PASS: stdout identical"
else
  echo "STRESS-DIFF-TEST FAIL"; diff /tmp/lean-stress.out /tmp/ts-stress.out || true; exit 1
fi
