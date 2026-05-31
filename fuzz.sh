#!/usr/bin/env bash
# Property-based fuzz: generate seeded-reproducible input vectors and diff the
# NATIVE C-backend oracle (oracle-fuzz) against node-run generated TS (fuzz.mjs).
# Both consumers read the IDENTICAL input file, so a failure reproduces from the
# seed alone. A fixed edge block is always prepended (numeric wrap, large Nats,
# multibyte strings, empty/large lists). Usage: ./fuzz.sh [SEED] [N]
set -euo pipefail
SEED="${1:-1}"
N="${2:-2000}"
lake build oracle-fuzz
lake exe lean-js out.ts prelude.ts out-io.mjs >/dev/null
ORACLE=.lake/build/bin

IN=$(mktemp)
node fuzz-gen.mjs "$SEED" "$N" > "$IN"
"$ORACLE/oracle-fuzz" < "$IN" > /tmp/fuzz-lean.out
node fuzz.mjs < "$IN" > /tmp/fuzz-ts.out
if diff -q /tmp/fuzz-lean.out /tmp/fuzz-ts.out >/dev/null; then
  echo "FUZZ PASS (seed=$SEED N=$N, $(wc -l < "$IN" | tr -d ' ') vectors)"
else
  echo "FUZZ FAIL (seed=$SEED) -- reproduce with: ./fuzz.sh $SEED $N"
  echo "--- first divergences ---"
  diff /tmp/fuzz-lean.out /tmp/fuzz-ts.out | head -20
  L=$(diff /tmp/fuzz-lean.out /tmp/fuzz-ts.out | grep -oE '^[0-9]+' | head -1)
  if [ -n "${L:-}" ]; then echo "offending input line $L:"; sed -n "${L}p" "$IN"; fi
  rm -f "$IN"; exit 1
fi
rm -f "$IN"
