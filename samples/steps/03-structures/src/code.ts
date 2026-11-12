import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
structure Point where
  x : Int
  y : Int

def Point.add (p q : Point) : Point := ⟨p.x + q.x, p.y + q.y⟩

def Point.norm1 (p : Point) : Nat := p.x.natAbs + p.y.natAbs

structure Range where
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi

def Range.width (r : Range) : Nat := r.hi - r.lo

def Range.shift (r : Range) (k : Nat) : Range := ⟨r.lo + k, r.hi + k, by have := r.ordered; omega⟩
`,
)

export { m }
