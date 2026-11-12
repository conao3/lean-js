import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/sort.ts"

export const block = lean(
  "spec",
  String.raw`
def sorted (xs : List Int) : Bool := decide (xs.Pairwise (· ≤ ·))

def inputSorted (_x : Int) (xs : List Int) : Bool := sorted xs

def resultSorted (_x : Int) (_xs : List Int) (r : List Int) : Bool := sorted r

def oneMore (_x : Int) (xs : List Int) (r : List Int) : Bool := r.length == xs.length + 1
`,
)

export function insertSorted(x: number, xs: readonly number[]): number[] {
  const out: number[] = []
  for (const y of xs) if (y < x) out.push(y)
  out.push(x)
  for (const y of xs) if (y >= x) out.push(y)
  return out
}

model(insertSorted, {
  requires: spec.inputSorted,
  ensures: { sorted: spec.resultSorted, length: spec.oneMore },
})

export { spec }
