import { search } from "./search.ts"

console.log(search.memberInt(3, [1, 2, 3]), search.memberInt(4, [1, 2, 3]))
console.log(search.memberString("pear", ["apple", "pear"]), search.memberString("fig", []))
console.log(String(search.maxNat([3, 9, 4])), String(search.maxNat([])))
console.log(String(search.maxInt([-7, -2, -5])))
