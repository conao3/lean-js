import { lean } from "lean-ts"
import type { Nat } from "lean-ts/schema"
import { model } from "lean-ts/verify"
import * as sums from "./_lean/sum.ts"

export const block = lean(
  "sums",
  String.raw`
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo, Nat.mul_add, ih, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
`,
)

export function sumTo(n: Nat): Nat {
  let total = 0n
  for (let i = 0n; i <= n; i++) total += i
  return total
}

model(sumTo, { refines: sums.sumTo })

export { sums }
