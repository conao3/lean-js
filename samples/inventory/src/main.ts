import { checkModel } from "lean-ts/verify"
import type { Item } from "./_lean/stock.ts"
import { discard, restock, total } from "./stock.ts"

const stock: Item[] = [
  { name: "hammer", kind: "tool", qty: 2n },
  { name: "apple", kind: "food", qty: 10n },
  { name: "saw", kind: "tool", qty: 1n },
]
console.log(total(stock).toString())
const more = restock(stock, "saw", 4n)
console.log(more.map((i) => `${i.name}:${i.qty}`).join(" "), total(more).toString())
const food = discard(more, "tool")
console.log(food.map((i) => `${i.name}:${i.qty}`).join(" "), total(food).toString())
for (const f of [total, restock, discard])
  await checkModel(f, { seed: 1, range: { min: 0n, max: 50n } })
console.log("checkModel: total, restock and discard agree with their specs")
