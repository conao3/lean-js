import { checkModel } from "lean-ts/verify"
import { calendar, isLeap } from "./calendar.ts"

console.log([1900, 2000, 2024, 2026].map((y) => isLeap(y)).join(" "))
console.log(calendar.leapYears(1896, 1912).join(" "))
await checkModel(isLeap, { seed: 1 })
console.log("checkModel: isLeap equals leap")
