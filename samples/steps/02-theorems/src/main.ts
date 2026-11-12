import { m } from "./code.ts"

console.log([0, 1, 2, 3, 4, 5].map((n) => m.sumTo(n)).join(" "))
console.log([-5, 50, 7].map((x) => m.clamp(0, 10, x)).join(" "))
