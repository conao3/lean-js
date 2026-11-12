import { checkModel } from "lean-ts/verify"
import { insertSorted } from "./sort.ts"
import { sums, sumTo } from "./sum.ts"

console.log(insertSorted(4, [1, 3, 5, 7]).join(" "))
console.log(sums.sumTo(1_000_000).toString())
await checkModel(insertSorted, { seed: 1, range: { min: -100n, max: 100n } })
await checkModel(sumTo, { seed: 1, range: { min: 0n, max: 300n } })
console.log("checkModel: insertSorted and sumTo agree with their specs")
