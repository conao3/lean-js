import { checkModel } from "lean-ts/verify"
import { midpoint } from "./mid.ts"

console.log(midpoint(0, 10), midpoint(3, 4), midpoint(-9, -1))
console.log(midpoint(10, 0))
await checkModel(midpoint, { seed: 1 })
console.log("checkModel: midpoint is between lo and hi when lo <= hi")
