import { stringify } from "lean-ts/schema"
import { report } from "./report.ts"
import { shapes } from "./shapes.ts"

const xs: shapes.Shape[] = [
  { ctor: "square", side: 3n },
  { ctor: "rect", w: 2n, h: 7n },
  { ctor: "square", side: 1n },
]
console.log(report.totalArea(xs).toString())
const big = report.largest(xs)
if (big !== null) console.log(stringify(shapes.Shape, big), shapes.Shape.area(big).toString())
