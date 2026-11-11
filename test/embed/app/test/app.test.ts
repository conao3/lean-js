import assert from "node:assert/strict"
import { test } from "node:test"
import { arithBlock, quadruple } from "../src/arith.ts"
import * as arith from "../src/_lean/arith.ts"
import { unitArea } from "../src/geometry.ts"
import * as report from "../src/_lean/report.ts"
import { describe } from "../src/report.ts"
import * as pricing from "../src/_lean/pricing.ts"
import { total } from "../src/pricing.ts"
import { greetAll } from "../src/text.ts"

await test("the generated functions of the blocks", () => {
  assert.equal(arith.double(21n), 42n)
  assert.equal(arith.sum([1n, 2n, 3n]), 6n)
  assert.equal(quadruple(5n), 20n)
  assert.equal(arithBlock.name, "arith")
  assert.match(arithBlock.key, /^[0-9a-f]{16}$/u)
})

await test("a block using the types of another block", () => {
  assert.equal(unitArea(), 1n)
  assert.equal(describe(2n, 3n), "2x3 has area 6")
  assert.equal(report.squareArea(4n), 16n)
})

await test("a template literal block and a block with imports", () => {
  assert.equal(greetAll(["ann", "bob"]), "hello, ann\nhello, bob\n2")
})

await test("a block using the user's zod model", () => {
  const book = { sku: "a", qty: 2, unitPrice: 300, tags: [], kind: "book" as const }
  const food = { sku: "b", qty: 1, unitPrice: 100, note: "x", tags: ["t"], kind: "food" as const }
  const items = [book, food]
  assert.equal(total(items, { kind: "percent", p: 10n }), 630n)
  assert.deepEqual(pricing.cheapest(items), food)
  assert.equal(pricing.cheapest([]), undefined)
  assert.throws(() => total([{ ...book, qty: 0 }], { kind: "none" }), /items\.0\.qty/u)
  assert.throws(() => total(items, { kind: "percent", p: 101n }), /Discount\.percent\.h: p ≤ 100/u)
  assert.deepEqual(pricing.Discount["~standard"].validate({ fixed: { amount: 5 } }), {
    value: { kind: "fixed", amount: 5n },
  })
})

await test("a block function taking a structure of the block it uses", () => {
  assert.equal(report.boxArea({ w: 2n, h: 5n }), 10n)
})
