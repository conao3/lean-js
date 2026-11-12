import { stringify } from "lean-ts/schema"
import { m } from "./code.ts"

const suits = ["hearts", "diamonds", "clubs", "spades"] as const
console.log(suits.filter((s) => m.Suit.isRed(s)).join(" "))
const e: m.Expr = {
  ctor: "add",
  a: { ctor: "num", n: 0n },
  b: { ctor: "mul", a: { ctor: "num", n: 1n }, b: { ctor: "neg", a: { ctor: "num", n: 7n } } },
}
console.log(m.Expr.eval(e).toString())
const s = m.Expr.simp(e)
console.log(stringify(m.Expr, s))
if (s.ctor === "neg" && s.a.ctor === "num") console.log("negated", s.a.n.toString())
