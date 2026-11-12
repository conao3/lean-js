import { checkModel } from "lean-ts/verify"
import { sortedIncludes, spec } from "./search.ts"

console.log(sortedIncludes([1, 3, 5, 7], 5), sortedIncludes([1, 3, 5, 7], 4))
console.log(sortedIncludes([2, 1], 1), spec.includes([2, 1], 1))
await checkModel(sortedIncludes, { seed: 1, range: { min: -20n, max: 20n } })
console.log("checkModel: sortedIncludes agrees with includes on sorted lists")
