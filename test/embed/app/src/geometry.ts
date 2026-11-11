import { lean } from "lean-ts"
import * as geometryLean from "./_lean/geometry.ts"

export const geometry = lean(
  "geometry",
  String.raw`
structure Box where
  w : Nat
  h : Nat

def Box.area (b : Box) : Nat := b.w * b.h

def square (n : Nat) : Box := ⟨n, n⟩

def unitArea : Nat := (square 1).area
`,
)

export const unitArea: typeof geometryLean.unitArea = geometryLean.unitArea
