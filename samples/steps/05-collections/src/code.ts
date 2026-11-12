import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
def evens (xs : List Nat) : List Nat := xs.filter (· % 2 == 0)

def squares (xs : Array Int) : Array Int := xs.map (· ^ 2)

def lookup (k : String) (xs : List (String × Nat)) : Option Nat := xs.lookup k

def histogram (xs : List Nat) (buckets : Nat) : Array Nat := Id.run do
  let mut h := Array.replicate buckets 0
  for x in xs do
    if x < buckets then h := h.modify x (· + 1)
  return h
`,
)

export { m }
