import { lean } from "lean-ts"
import type { Nat } from "lean-ts/schema"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/sums.ts"

export const block = lean(
  "spec",
  String.raw`
def square (n : Nat) : Nat := n * n

def nonneg (_xs : List Int) (r : Int) : Bool := 0 ≤ r
`,
)

export function sumOdd(n: Nat): Nat {
  let total = 0n
  for (let i = 0n; i < n; i++) total += 2n * i + 1n
  return total
}

model(sumOdd, { refines: spec.square })

export function sumAbs(xs: readonly number[]): number {
  let total = 0
  for (const x of xs) total += Math.abs(x)
  return total
}

model(sumAbs, { ensures: { nonneg: spec.nonneg } })
