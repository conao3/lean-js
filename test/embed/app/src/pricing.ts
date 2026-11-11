import { lean } from "lean-ts"
import * as z from "zod"
import * as pricing from "./_lean/pricing.ts"

export const LineItem = z.object({
  sku: z
    .string()
    .min(1)
    .regex(/^[A-Z0-9-]+$/u),
  qty: z.number().int().min(1),
  unitPrice: z.number().int().min(0),
  note: z.string().optional(),
  tags: z.array(z.string()).max(3),
  kind: z.enum(["book", "food"]),
})

export const Order = z.object({ buyer: z.string(), item: LineItem })

export const pricingBlock = lean(
  "pricing",
  String.raw`
inductive Discount where
  | none
  | percent (p : Nat) (h : p ≤ 100)
  | fixed (amount : Nat)

def subtotal (items : List LineItem) : Nat :=
  items.foldl (fun acc i => acc + i.qty * i.unitPrice) 0

def total (items : List LineItem) (d : Discount) : Nat :=
  match d with
  | .none => subtotal items
  | .percent p _ => subtotal items - subtotal items * p / 100
  | .fixed a => subtotal items - a

theorem qty_pos (i : LineItem) : 0 < i.qty := by
  have := i.qty_ge
  omega

def orderTotal (o : Order) : Nat := o.item.qty * o.item.unitPrice

def cheapest (items : List LineItem) : Option LineItem :=
  items.foldl (fun acc i => match acc with
    | none => some i
    | some j => if i.unitPrice < j.unitPrice then some i else some j) none
`,
  { models: { LineItem, Order }, output: { tagKey: "kind", option: "undefined" } },
)

export const total: typeof pricing.total = pricing.total
