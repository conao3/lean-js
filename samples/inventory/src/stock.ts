import { lean } from "lean-ts"
import type { Nat } from "lean-ts/schema"
import { model } from "lean-ts/verify"
import * as spec from "./_lean/stock.ts"
import type { Item, Kind } from "./_lean/stock.ts"

export const block = lean(
  "spec",
  String.raw`
inductive Kind where
  | tool
  | food
  deriving DecidableEq

structure Item where
  name : String
  kind : Kind
  qty : Nat

def total (stock : List Item) : Int := (stock.map fun i => (i.qty : Int)).sum

def sameLength (stock : List Item) (_name : String) (_n : Int) (r : List Item) : Bool :=
  r.length == stock.length

def grows (stock : List Item) (_name : String) (n : Int) (r : List Item) : Bool :=
  decide (0 ≤ n → total stock ≤ total r)

def shrinks (stock : List Item) (_kind : Kind) (r : List Item) : Bool := decide (total r ≤ total stock)

def without (_stock : List Item) (kind : Kind) (r : List Item) : Bool := r.all (·.kind != kind)
`,
)

export function total(stock: readonly Item[]): bigint {
  let t = 0n
  for (const i of stock) t += i.qty
  return t
}

model(total, { refines: spec.total })

export function restock(stock: readonly Item[], name: string, n: Nat): Item[] {
  const out: Item[] = []
  for (const i of stock) {
    if (i.name === name) {
      const j: Item = { name: i.name, kind: i.kind, qty: i.qty + n }
      out.push(j)
    } else out.push(i)
  }
  return out
}

model(restock, { ensures: { sameLength: spec.sameLength, grows: spec.grows } })

export function discard(stock: readonly Item[], kind: Kind): Item[] {
  return stock.filter((i) => i.kind !== kind)
}

model(discard, { ensures: { shrinks: spec.shrinks, without: spec.without } })

export { spec }
