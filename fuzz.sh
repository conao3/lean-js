#!/usr/bin/env bash
# Property-based fuzz: generate seeded-reproducible input vectors and diff the
# NATIVE C-backend oracle (oracle-fuzz) against the generated TS run by node
# (test/difftest/fuzz.mjs). Both consumers read the IDENTICAL input file, so a
# failure reproduces from the seed alone. A fixed edge block is always prepended
# (numeric wrap, large Nats, multibyte strings, empty/large lists).
# Usage: ./fuzz.sh [SEED] [N]
set -euo pipefail
SEED="${1:-1}"
N="${2:-2000}"
lake build lean-typescript LeanTsTest oracle-fuzz
ORACLE=.lake/build/bin
mkdir -p test-out
"$ORACLE/lean-typescript" module generate --module-name LeanTsTest.Fuzz \
  --search-path .lake/build/lib/lean --runtime-path ../src/runtime/index.ts \
  --output-file test-out/fuzz.ts --output text --internal-only

IN=test-out/fuzz.in
node test/difftest/fuzz-gen.mjs "$SEED" "$N" > "$IN"
"$ORACLE/oracle-fuzz" < "$IN" > test-out/fuzz.oracle.out
node test/difftest/fuzz.mjs < "$IN" > test-out/fuzz.node.out
if diff -q test-out/fuzz.oracle.out test-out/fuzz.node.out >/dev/null; then
  echo "FUZZ PASS (seed=$SEED N=$N, $(wc -l < "$IN" | tr -d ' ') vectors)"
else
  echo "FUZZ FAIL (seed=$SEED) -- reproduce with: ./fuzz.sh $SEED $N"
  echo "--- first divergences ---"
  diff test-out/fuzz.oracle.out test-out/fuzz.node.out | head -20
  L=$(diff test-out/fuzz.oracle.out test-out/fuzz.node.out | grep -oE '^[0-9]+' | head -1)
  if [ -n "${L:-}" ]; then echo "offending input line $L:"; sed -n "${L}p" "$IN"; fi
  exit 1
fi
