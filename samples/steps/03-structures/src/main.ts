import { LeanValidationError, parse, stringify } from "lean-ts/schema"
import { m } from "./code.ts"

const p = m.Point.add({ x: 1n, y: -2n }, { x: 3n, y: 5n })
console.log(stringify(m.Point, p), m.Point.norm1(p).toString())
const r = m.Range.shift({ lo: 1n, hi: 4n }, 10)
console.log(stringify(m.Range, r), m.Range.width(r).toString())
try {
  parse(m.Range, '{"lo":5,"hi":1}')
} catch (e) {
  if (e instanceof LeanValidationError) console.log("rejected:", e.issues[0]?.message)
}
