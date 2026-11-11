#!/usr/bin/env bash
# Diff-test: generate the LeanTsTest modules with lean-typescript and compare the
# generated TypeScript (run by node) against the same Lean code compiled by the
# native C backend (the oracle-* executables): function values, stdout, stderr
# and exit codes. The oracle is the real production backend with compiled TCO,
# bignum and libm semantics, not the `lean --run` interpreter.
set -euo pipefail
ulimit -s 65536
export LEAN_BACKTRACE=0
lake build lean-typescript LeanTsTest oracle-vectors oracle-io oracle-stdin oracle-err oracle-panic oracle-init oracle-stress oracle-stress2 oracle-stress3 oracle-stress4 oracle-verify
mkdir -p test-out
ORACLE=.lake/build/bin
generate() {
  local out=$1
  shift
  "$ORACLE/lean-typescript" module generate \
    --search-path .lake/build/lib/lean --runtime-path ../src/runtime/index.ts \
    --output-file "test-out/$out" --output text --internal-only "$@"
}
generate vectors.ts --module-name LeanTsTest.Vectors
generate higher-order.ts --module-name LeanTsTest.HigherOrder
generate fuzz.ts --module-name LeanTsTest.Fuzz
generate io.ts --module-name LeanTsTest.Io --main LeanTsTest.Io.main
generate stdin.ts --module-name LeanTsTest.Io --main LeanTsTest.Io.stdinEcho
generate err.ts --module-name LeanTsTest.Io --main LeanTsTest.Io.errMain
generate panic.ts --module-name LeanTsTest.Io --main LeanTsTest.Io.panicMain
generate init.ts --module-name LeanTsTest.Init --main LeanTsTest.Init.main
generate stress.ts --module-name LeanTsTest.Stress --main LeanTsTest.Stress.stressMain
generate stress2.ts --module-name LeanTsTest.Stress2 --main LeanTsTest.Stress2.stress2Main
generate stress3.ts --module-name LeanTsTest.Stress3 --main LeanTsTest.Stress3.stress3Main
generate stress4.ts --module-name LeanTsTest.Stress4 --main LeanTsTest.Stress4.stress4Main
generate verify.ts --module-name LeanTsTest.Verify --main LeanTsTest.Verify.verifyMain

# compare <name> <oracle> <node args...>: stdout, stderr and the exit code must match.
compare() {
  local name=$1 oracle=$2
  shift 2
  local in=/dev/null
  [ -f "test-out/$name.in" ] && in="test-out/$name.in"
  local lean_ec=0 node_ec=0
  "$ORACLE/$oracle" < "$in" > "test-out/$name.oracle.out" 2> "test-out/$name.oracle.err" || lean_ec=$?
  node "$@" < "$in" > "test-out/$name.node.out" 2> "test-out/$name.node.err" || node_ec=$?
  diff -u "test-out/$name.oracle.out" "test-out/$name.node.out"
  diff -u "test-out/$name.oracle.err" "test-out/$name.node.err"
  if [ "$lean_ec" != "$node_ec" ]; then
    echo "$name: exit code $lean_ec (oracle) != $node_ec (node)"
    exit 1
  fi
  echo "$name: $(wc -l < "test-out/$name.oracle.out") lines, exit $lean_ec match"
}

# Function-level values: the oracle prints every function result, the harness
# calls the generated functions with the same inputs.
compare vectors oracle-vectors test/difftest/vectors.mjs
# Programs: IO, stdin echo, an uncaught error (exit 1), panics (continue, exit
# 0), the @[init] chain, realistic programs (parser, containers, monads,
# ByteArray/UTF-8, HashMap order, FloatArray, dbgTrace) and a verifier-authored one.
compare io oracle-io test-out/io.ts
printf 'alpha\nbeta\ngamma\n' > test-out/stdin.in
compare stdin oracle-stdin test-out/stdin.ts
compare err oracle-err test-out/err.ts
compare panic oracle-panic test-out/panic.ts
compare init oracle-init test-out/init.ts
compare stress oracle-stress test-out/stress.ts
compare stress2 oracle-stress2 test-out/stress2.ts
compare stress3 oracle-stress3 test-out/stress3.ts
compare stress4 oracle-stress4 test-out/stress4.ts
compare verify oracle-verify test-out/verify.ts

# Deep mutual/cross-function TCO: node-side no-stack-overflow check at large N
# (the native backend overflows on closure-boundary tail calls at these N).
node test/difftest/tco.mjs
# 32-bit USize profile: WORD_BITS=32 in a copy of the runtime, checked against
# hand-computed literals (a 64-bit host cannot produce a 32-bit native reference).
node test/difftest/usize32.mjs

# Extern link check: an extern the runtime does not provide is a hard error
# (exit 254 naming the symbol), not a dangling call; a mapped root generates.
link_ec=0
"$ORACLE/lean-typescript" module generate --module-name Init --roots IO.getRandomBytes > /dev/null 2> test-out/link.err || link_ec=$?
if [ "$link_ec" != 254 ] || ! grep -q lean_io_get_random_bytes test-out/link.err; then
  echo "extern link check: expected exit 254 naming lean_io_get_random_bytes, got $link_ec"
  cat test-out/link.err
  exit 1
fi
"$ORACLE/lean-typescript" module generate --module-name Init --roots String.splitOn > /dev/null 2>&1
echo "extern link check: unmapped extern rejected, mapped root generated"

echo "DIFF-TEST PASS"
