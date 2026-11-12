import { lean } from "lean-ts"
import * as report from "./_lean/report.ts"
import "./shapes.ts"

export const block = lean(
  "report",
  String.raw`
def totalArea (xs : List Shape) : Nat := (xs.map Shape.area).foldl (· + ·) 0

def largest (xs : List Shape) : Option Shape :=
  xs.foldl (fun best s => match best with
    | none => some s
    | some b => if b.area < s.area then some s else some b) none
`,
  { uses: ["./shapes.ts:shapes"] },
)

export { report }
