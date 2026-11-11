import assert from "node:assert/strict"
import { test } from "node:test"
import { arithBlock, quadruple } from "../src/arith.ts"
import * as arith from "../src/_lean/arith.ts"
import { unitArea } from "../src/geometry.ts"
import * as report from "../src/_lean/report.ts"
import { describe } from "../src/report.ts"
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
