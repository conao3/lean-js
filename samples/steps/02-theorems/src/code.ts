import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo, Nat.mul_add, ih, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

def clamp (lo hi x : Int) : Int := max lo (min hi x)

theorem clamp_le (lo hi x : Int) (h : lo ≤ hi) : clamp lo hi x ≤ hi := by
  unfold clamp; omega
`,
)

export { m }
