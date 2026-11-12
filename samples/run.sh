#!/usr/bin/env bash
set -euo pipefail
dir=$(cd "$1" && pwd)
cd "$dir"
lts=(node node_modules/lean-ts/dist/cli.js)
if [ -f lean/lakefile.toml ]; then
  "${lts[@]}" generate --lake-dir lean --output-dir src/_lean > sync.log 2>&1 || { cat sync.log; exit 1; }
else
  "${lts[@]}" sync --package . > sync.log 2>&1 || { cat sync.log; exit 1; }
fi
node src/main.ts > out.txt 2> err.txt || { cat err.txt; exit 1; }
diff -u expected.txt out.txt
rm -f out.txt err.txt sync.log
echo "$(basename "$dir"): output matches expected.txt"
