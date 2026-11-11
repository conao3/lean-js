#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
out="$root/test-out/verify"
cli="$root/.lake/build/bin/lean-typescript"
lts=(node "$root/src/cli.ts")

fail() {
  printf 'test/verify: %s\n' "$*" >&2
  exit 1
}

scene() {
  local name="$1" from="$2"
  rm -rf "${out:?}/$name"
  mkdir -p "$out"
  cp -r "$from" "$out/$name"
  mkdir -p "$out/$name/node_modules"
  ln -sfn ../../../.. "$out/$name/node_modules/lean-ts"
}

expect_rows() {
  local got="$1" want="$2" what="$3"
  if ! diff <(printf '%s\n' "$want") <(printf '%s\n' "$got" | grep -v '^fresh ' | sed -E 's/ +/ /'); then
    fail "$what: unexpected obligation states"
  fi
}

base_rows="proved src/calc.ts:clamp refines
proved src/calc.ts:clamp inRange
proved src/calc.ts:firstOr refines
sorry src/calc.ts:sumTo refines
missing src/calc.ts:sumTo returnsNat
proved src/calc.ts:sumAbs nonneg
axioms src/calc.ts:twice refines"

scene base "$root/test/verify/app"
rm -rf "$out/base/node_modules/lean-ts" "$out/base/src/_lean" "$out/base/.lean-ts" "$out/base/lean-ts.lock"
ln -sfn ../../../.. "$out/base/node_modules/lean-ts"
rows="$(cd "$out/base" && "${lts[@]}" check --package . --lean-typescript "$cli")"
expect_rows "$rows" "$base_rows" "check"
[[ -f "$out/base/lean-ts.lock" ]] || fail "check did not write lean-ts.lock"
grep -q '"spec_hash"' "$out/base/lean-ts.lock" || fail "the lock has no spec_hash"

set +e
(cd "$out/base" && "${lts[@]}" check --package . --lean-typescript "$cli" --require proved >/dev/null 2>&1)
code=$?
set -e
[[ $code -eq 254 ]] || fail "check --require proved exited with $code, expected 254"

rows="$(cd "$out/base" && "${lts[@]}" status --package .)"
expect_rows "$rows" "$base_rows" "status"

scene stale "$out/base"
sed -i 's/  if (x > hi) return hi/  if (x >= hi) return hi/' "$out/stale/src/calc.ts"
sed -i 's/^export function clamp/\/\/ moved down by a line\nexport function clamp/' "$out/stale/src/calc.ts"
set +e
rows="$(cd "$out/stale" && "${lts[@]}" status --package .)"
code=$?
set -e
[[ $code -eq 254 ]] || fail "status of a changed function exited with $code, expected 254"
expect_rows "$rows" "stale src/calc.ts:clamp refines
stale src/calc.ts:clamp inRange
proved src/calc.ts:firstOr refines
sorry src/calc.ts:sumTo refines
missing src/calc.ts:sumTo returnsNat
proved src/calc.ts:sumAbs nonneg
axioms src/calc.ts:twice refines" "status after a change"

scene moved "$out/base"
sed -i 's/^export function clamp/\/\/ a comment above the function\nexport function clamp/' "$out/moved/src/calc.ts"
rows="$(cd "$out/moved" && "${lts[@]}" status --package .)"
expect_rows "$rows" "$base_rows" "status after moving a function"

scene wrong-proof "$out/base"
proofs="$out/wrong-proof/lean/Proofs/Calc.lean"
sed -i 's/^theorem firstOr.proof.refines : firstOr.obligation.refines := by$/theorem firstOr.proof.refines : True := trivial\n\ntheorem firstOr.unused : firstOr.obligation.refines := by/' "$proofs"
cat >"$out/wrong-proof/lean/Proofs/Broken.lean" <<'EOF'
import LeanTsModel.calc

theorem LeanTsModel.calc.sumTo.proof.returnsNat : LeanTsModel.calc.sumTo.obligation.returnsNat := by
  intro n
  rfl
EOF
rows="$(cd "$out/wrong-proof" && "${lts[@]}" check --package . --lean-typescript "$cli" 2>/dev/null)"
expect_rows "$rows" "proved src/calc.ts:clamp refines
proved src/calc.ts:clamp inRange
mismatch src/calc.ts:firstOr refines
sorry src/calc.ts:sumTo refines
failed src/calc.ts:sumTo returnsNat
proved src/calc.ts:sumAbs nonneg
axioms src/calc.ts:twice refines" "check with a wrong statement and a failing proof"

scene outside "$out/base"
cat >>"$out/outside/src/calc.ts" <<'EOF'

export function loose(x: number): boolean {
  return x == 1
}

model(loose, { ensures: { nonneg: spec.nonneg } })
EOF
set +e
msg="$(cd "$out/outside" && "${lts[@]}" check --package . --lean-typescript "$cli" 2>&1 >/dev/null)"
code=$?
set -e
[[ $code -eq 254 ]] || fail "check of a function outside the subset exited with $code, expected 254"
grep -q 'src/calc.ts:[0-9]*:[0-9]*: loose: == is outside the subset' <<<"$msg" || fail "no position for the untranslatable function: $msg"

scene wrong-impl "$out/base"
cat >"$out/wrong-impl/wrong.ts" <<'EOF'
import { checkModel, model, PropertyFailure } from "lean-ts/verify"
import * as spec from "./src/_lean/calc.ts"

function badClamp(x: number, lo: number, _hi: number): number {
  if (x < lo) return lo
  return x
}

model(badClamp, { refines: spec.clampSpec, requires: spec.ordered })

try {
  await checkModel(badClamp)
  console.log("no counterexample")
} catch (e) {
  if (!(e instanceof PropertyFailure)) throw e
  console.log(e.message.includes("Counterexample") && e.message.includes("the spec gives") ? "counterexample" : e.message)
}
EOF
got="$(cd "$out/wrong-impl" && node wrong.ts)"
[[ "$got" == counterexample ]] || fail "checkModel of a wrong implementation printed: $got"

printf 'test/verify: ok\n'
