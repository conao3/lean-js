import { lean } from "lean-ts"
import * as arith from "./_lean/arith.ts"

export const arithBlock = lean(
  "arith",
  String.raw`
def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double; omega

def sum (xs : List Nat) : Nat := xs.foldl (· + ·) 0
`,
)

export function quadruple(n: bigint): bigint {
  return arith.double(arith.double(n))
}
