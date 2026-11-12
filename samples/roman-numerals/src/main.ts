import * as roman from "./_lean/Roman.ts"

console.log(roman.toRoman(1994))
console.log(String(roman.fromRoman("MMXXVI")))
console.log(String(roman.fromRoman("hello")))
console.log(Array.from({ length: 10 }, (_, i) => roman.toRoman(i + 1)).join(" "))
