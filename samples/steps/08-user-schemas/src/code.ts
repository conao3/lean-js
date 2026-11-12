import { lean } from "lean-ts"
import * as z from "zod"
import * as bank from "./_lean/code.ts"

export const Account = z.object({
  owner: z.string().min(1),
  balance: z.number().int().min(0).max(1_000_000),
})

export const block = lean(
  "bank",
  String.raw`
def transfer (a b : Account) (amount : Nat) : Account × Account :=
  if h : amount ≤ a.balance ∧ b.balance + amount ≤ 1000000 then
    ({ a with balance := a.balance - amount, balance_le := by have := a.balance_le; omega },
     { b with balance := b.balance + amount, balance_le := h.2 })
  else (a, b)

theorem transfer_total (a b : Account) (amount : Nat) :
    (transfer a b amount).1.balance + (transfer a b amount).2.balance = a.balance + b.balance := by
  unfold transfer; split <;> simp <;> omega
`,
  { models: { Account } },
)

export { bank }
