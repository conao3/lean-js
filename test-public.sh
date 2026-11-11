#!/usr/bin/env bash
set -euo pipefail
lake build lean-typescript LeanTsTest
mkdir -p test-out
.lake/build/bin/lean-typescript module generate --module-name LeanTsTest.Public \
  --search-path .lake/build/lib/lean --runtime-path ../src/runtime/index.ts \
  --output-file test-out/public.ts --output json > test-out/public.summary.json
vp test test/public.test.ts
echo "PUBLIC PASS"
