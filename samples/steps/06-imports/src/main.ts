import { m } from "./code.ts"

for (const [w, is] of m.wordIndex(["to", "be", "or", "not", "to", "be"]))
  console.log(w, is.join(","))
console.log(m.dedup([3, 1, 3, 2, 1]).join(" "))
