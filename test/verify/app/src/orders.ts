import { lean } from "lean-ts"
import { model } from "lean-ts/verify"
import * as z from "zod"
import * as orders from "./_lean/orders.ts"

export const Line = z.object({
  qty: z.number().int().min(1).max(1000),
  price: z.number().int().min(0).max(100000),
  note: z.string().optional(),
})

export const ordersBlock = lean(
  "orders",
  String.raw`
def lineTotal (l : Line) : Int := l.qty * l.price

def positive (_l : Line) (r : Int) : Bool := 0 < r

def noted (l : Line) : Bool := l.note?.isSome
`,
  { models: { Line } },
)

export function lineTotal(l: z.infer<typeof Line>): number {
  return l.qty * l.price
}

model(lineTotal, { refines: orders.lineTotal })

export function quantity(l: z.infer<typeof Line>): number {
  return l.qty
}

model(quantity, { ensures: { positive: orders.positive } })

export function hasNote(l: z.infer<typeof Line>): boolean {
  return l.note !== undefined
}

model(hasNote, { refines: orders.noted })
