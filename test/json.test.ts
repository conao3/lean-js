import { readFileSync } from "node:fs"
import { describe, expect, test } from "vite-plus/test"
import * as L from "../src/runtime/index.ts"
import * as S from "../src/schema/index.ts"
import * as J from "../test-out/json.ts"

const ORACLE = readFileSync(new URL("../test-out/json.oracle.txt", import.meta.url), "utf8")
  .trimEnd()
  .split("\n")

function integersAsBigInt(
  this: unknown,
  _key: string,
  value: unknown,
  ...rest: unknown[]
): unknown {
  const ctx = rest[0]
  const source: unknown =
    typeof ctx === "object" && ctx !== null ? Reflect.get(ctx, "source") : undefined
  return typeof value === "number" && typeof source === "string" && /^-?[0-9]+$/u.test(source)
    ? BigInt(source)
    : value
}

function exact(text: string): unknown {
  return JSON.parse(text, integersAsBigInt)
}

const shapes = S.schema<J.ShapeInput[], J.Shape[]>(L.listDesc(J.Shape.desc))
const colors = S.schema<J.ColorInput[], J.Color[]>(L.arrayDesc(J.Color.desc))

const record2: J.Record = {
  inner: { n: 0n, s: "" },
  opt: null,
  note: null,
  xs: [],
  arr: [],
  pair: [0n, ""],
  color: "red",
  shape: { ctor: "dot" },
  tree: { ctor: "leaf" },
  big: 0n,
  flag: false,
  f: -0.25,
  u64: 0n,
  nested: [],
}

const shapeValues: J.Shape[] = [
  { ctor: "dot" },
  { ctor: "circle", r: 4n },
  { ctor: "rect", w: 1n, h: 2n },
  { ctor: "tagged", a0: "t" },
  { ctor: "pair", a0: 9n, a1: false },
  { ctor: "wrap", inner: { n: 5n, s: "five" } },
]

const CASES: readonly [string, S.LeanSchema<unknown, unknown>, unknown][] = [
  ["record1", J.Record, J.record1()],
  ["record2", J.Record, J.record2()],
  ["shapes", shapes, J.shapes()],
  ["child", J.Child, J.child()],
  ["colors", colors, J.colors()],
]

describe("the JSON of Lean's deriving ToJson", () => {
  test.each(CASES.map((c, i) => [...c, i] as const))(
    "stringify(%s) is the JSON the native oracle prints",
    (_name, schema, value, i) => {
      expect(exact(S.stringify(schema, value))).toEqual(exact(ORACLE[i] ?? ""))
    },
  )

  test.each(CASES.map((c, i) => [...c, i] as const))(
    "parse of the oracle's JSON of %s is the value from Lean",
    (_name, schema, value, i) => {
      expect(S.parse(schema, ORACLE[i] ?? "")).toEqual(value)
    },
  )

  test("toJSON keeps safe integers as numbers and the others as strings", () => {
    expect(S.toJSON(J.Record, J.record1())).toMatchObject({
      big: "1208925819614629174706176",
      xs: [-1, 0, "1180591620717411303424"],
      u64: "18446744073709551615",
      note: "hi",
    })
    expect(S.fromJSON(J.Record, S.toJSON(J.Record, J.record1()))).toEqual(J.record1())
  })

  test("values written in TypeScript are the values Lean builds", () => {
    expect(record2).toEqual(J.record2())
    expect(shapeValues).toEqual(J.shapes())
    expect(S.stringify(shapes, shapeValues)).toBe(S.stringify(shapes, J.shapes()))
    expect(J.Child["~standard"].validate({ n: 2, s: "two", extra: true })).toEqual({
      value: J.child(),
    })
  })
})
