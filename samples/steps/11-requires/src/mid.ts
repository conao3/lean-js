import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/mid.ts"

export const block = lean(
  "spec",
  String.raw`
def ordered (lo hi : Int) : Bool := lo ≤ hi

def between (lo hi : Int) (r : Int) : Bool := lo ≤ r && r ≤ hi
`,
)

export function midpoint(lo: number, hi: number): number {
  return lo + Math.floor((hi - lo) / 2)
}

model(midpoint, { requires: spec.ordered, ensures: { between: spec.between } })
