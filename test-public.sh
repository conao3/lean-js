#!/usr/bin/env bash
set -euo pipefail
lake build lean-typescript LeanTsTest oracle-json
mkdir -p test-out
gen=(.lake/build/bin/lean-typescript module generate --module-name LeanTsTest.Public
  --search-path .lake/build/lib/lean --runtime-path ../src/runtime/index.ts --output json)
"${gen[@]}" --output-file test-out/public.ts > test-out/public.summary.json
"${gen[@]}" --output-file test-out/public-alt.ts --tag-key _tag --option undefined > test-out/public-alt.summary.json
.lake/build/bin/lean-typescript module generate --module-name LeanTsTest.Json --search-path .lake/build/lib/lean \
  --runtime-path ../src/runtime/index.ts --output-file test-out/json.ts --output json > test-out/json.summary.json
.lake/build/bin/oracle-json > test-out/json.oracle.txt
.lake/build/bin/lean-typescript module generate --module-name LeanTsTest.TsModel --search-path .lake/build/lib/lean \
  --runtime-path ../src/runtime/index.ts --output-file test-out/ts-model.ts --output json > test-out/ts-model.summary.json
set +e
"${gen[@]}" --output-file test-out/public-clash.ts --tag-key amount 2> test-out/public-clash.stderr
echo $? > test-out/public-clash.status
"${gen[@]}" --output-file test-out/public-badkey.ts --tag-key not-an-identifier 2> test-out/public-badkey.stderr
echo $? > test-out/public-badkey.status
"${gen[@]}" --output-file test-out/public-badopt.ts --option none 2> test-out/public-badopt.stderr
echo $? > test-out/public-badopt.status
set -e
vp test test/public.test.ts test/json.test.ts test/verify/ts-model.test.ts
echo "PUBLIC PASS"
