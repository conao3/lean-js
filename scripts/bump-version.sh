#!/usr/bin/env bash
set -euo pipefail
v=$1
cd "$(dirname "$0")/.."
node --input-type=module -e '
import { readFileSync, writeFileSync } from "node:fs"
const p = JSON.parse(readFileSync("package.json", "utf8"))
p.version = process.argv[1]
writeFileSync("package.json", JSON.stringify(p, null, 2) + "\n")
' "$v"
sed -i "s/^def version : String := \".*\"/def version : String := \"$v\"/" Main.lean
sed -i "s/version = \"[0-9.]*\";/version = \"$v\";/" flake.nix
grep -q "\"version\": \"$v\"" package.json
grep -q "def version : String := \"$v\"" Main.lean
grep -q "version = \"$v\";" flake.nix
