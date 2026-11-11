import { lean } from "lean-ts"
import * as report from "./_lean/report.ts"
import "./geometry.ts"

export const reportBlock = lean(
  "report",
  String.raw`
def describe (w h : Nat) : String := s!"{w}x{h} has area {(Box.mk w h).area}"

def squareArea (n : Nat) : Nat := (square n).area

def boxArea (b : Box) : Nat := b.area
`,
  { uses: ["./geometry.ts:geometry"] },
)

export const describe: typeof report.describe = report.describe
