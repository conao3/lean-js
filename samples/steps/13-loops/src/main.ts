import { checkModel } from "lean-ts/verify"
import { sumAbs, sumOdd } from "./sums.ts"

console.log([0n, 1n, 2n, 3n, 10n].map((n) => sumOdd(n)).join(" "))
console.log(sumAbs([3, -4, 0, -1]))
await checkModel(sumOdd, { seed: 1, range: { min: 0n, max: 200n } })
await checkModel(sumAbs, { seed: 1, range: { min: -1000n, max: 1000n } })
console.log("checkModel: sumOdd and sumAbs agree with their specs")
