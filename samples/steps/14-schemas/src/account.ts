import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as z from "zod"
import * as spec from "./_lean/account.ts"

export const Account = z.object({
  owner: z.string().min(1),
  balance: z.number().int().min(0).max(1_000_000),
})

export const block = lean(
  "spec",
  String.raw`
def inLimits (_a : Account) (_n : Int) (r : Int) : Bool := 0 ≤ r && r ≤ 1000000
`,
  { models: { Account } },
)

export function withdraw(a: z.infer<typeof Account>, n: number): number {
  if (n < 0) return a.balance
  if (n > a.balance) return a.balance
  return a.balance - n
}

model(withdraw, { ensures: { inLimits: spec.inLimits } })
