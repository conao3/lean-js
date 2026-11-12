import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/dist.ts"

export const block = lean(
  "spec",
  String.raw`
def nonneg (_a _b : Int) (r : Int) : Bool := 0 ≤ r

def symmetric (a b : Int) (r : Int) : Bool := r == (if a > b then a - b else b - a)
`,
)

export function distance(a: number, b: number): number {
  if (a > b) return a - b
  return b - a
}

model(distance, { ensures: { nonneg: spec.nonneg, symmetric: spec.symmetric } })
