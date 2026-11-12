import { lean } from "lean-ts"
import * as z from "zod"
import * as pricing from "./_lean/pricing.ts"

export const LineItem = z.object({
  sku: z.string().min(1),
  qty: z.number().int().min(1),
  unitPrice: z.number().int().min(0),
})

export const block = lean(
  "pricing",
  String.raw`
inductive Discount where
  | none
  | percent (p : Nat) (h : p ≤ 100)
  | fixed (amount : Nat)

structure Order where
  items : List LineItem
  discount : Discount

def subtotal (items : List LineItem) : Nat :=
  items.foldl (fun acc i => acc + i.qty * i.unitPrice) 0

def total (o : Order) : Nat :=
  match o.discount with
  | .none => subtotal o.items
  | .percent p _ => subtotal o.items - subtotal o.items * p / 100
  | .fixed a => subtotal o.items - a

theorem total_le (o : Order) : total o ≤ subtotal o.items := by
  unfold total; split <;> omega
`,
  { models: { LineItem } },
)

export { pricing }
