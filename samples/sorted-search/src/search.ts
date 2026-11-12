import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/search.ts"

export const block = lean(
  "spec",
  String.raw`
def sorted (xs : List Int) : Bool := decide (xs.Pairwise (· ≤ ·))

def includes (xs : List Int) (x : Int) : Bool := xs.contains x

def sortedInput (xs : List Int) (_x : Int) : Bool := sorted xs
`,
)

export function sortedIncludes(xs: readonly number[], x: number): boolean {
  for (const y of xs) {
    if (y === x) return true
    if (y > x) return false
  }
  return false
}

model(sortedIncludes, { refines: spec.includes, requires: spec.sortedInput })

export { spec }
