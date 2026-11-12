import { m } from "./code.ts"

const pairs: [string, number][] = [
  ["a", 1],
  ["b", 2],
]
console.log(m.evens([1, 2, 3, 4, 10]).join(" "))
console.log(m.squares([-3, 4]).join(" "))
console.log(String(m.lookup("b", pairs)), String(m.lookup("z", pairs)))
console.log(m.histogram([0, 1, 1, 3, 7, 3, 3], 4).join(" "))
