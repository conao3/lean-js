import { lean } from "lean-ts"
import * as shapes from "./_lean/shapes.ts"

export const block = lean(
  "shapes",
  String.raw`
inductive Shape where
  | square (side : Nat)
  | rect (w h : Nat)

def Shape.area : Shape → Nat
  | .square s => s * s
  | .rect w h => w * h
`,
)

export { shapes }
