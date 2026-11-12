import { readFileSync } from "node:fs"
import { stringify } from "lean-ts/schema"
import { wc } from "./count.ts"

const text = readFileSync(new URL("../sample.txt", import.meta.url), "utf8")
const c = wc.count(text)
console.log(`lines ${c.lines}, words ${c.words}, chars ${c.chars}`)
for (const [w, n] of wc.top(text, 3)) console.log(w, n.toString())
console.log(stringify(wc.Counts, c))
