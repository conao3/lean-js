import { readFileSync } from "node:fs"
import { describe, expect, test } from "vite-plus/test"
import * as L from "../src/runtime/index.ts"
import * as S from "../src/schema/index.ts"
import * as A from "../test-out/public-alt.ts"
import * as P from "../test-out/public.ts"

function issuesOf(f: () => unknown): readonly L.Issue[] {
  try {
    f()
  } catch (e) {
    if (e instanceof L.LeanValidationError) return e.issues
    throw e
  }
  throw new Error("expected a LeanValidationError")
}

function ioErrorOf(f: () => unknown): L.LeanIOError {
  try {
    f()
  } catch (e) {
    if (e instanceof L.LeanIOError) return e
    throw e
  }
  throw new Error("expected a LeanIOError")
}

function call(f: (...args: never[]) => unknown, ...args: unknown[]): unknown {
  return Reflect.apply(f, undefined, args)
}

describe("exports", () => {
  test("the public functions and namespaces, without the skipped definitions", () => {
    expect(Object.keys(P).toSorted()).toEqual([
      "Calc",
      "Color",
      "Discount",
      "Flags",
      "Labeled",
      "Names",
      "PairBoolNat",
      "PairNatBool",
      "Point",
      "Pos",
      "Range",
      "Small",
      "Tree",
      "answer",
      "applyDiscount",
      "big",
      "bump",
      "bytesOf",
      "describe",
      "double",
      "failing",
      "finSucc",
      "firstEvenQ",
      "flip",
      "fromExcept",
      "greet",
      "halfOff",
      "halve",
      "halve32",
      "ioEcho",
      "ioUnit",
      "isEven",
      "mix",
      "mkRange",
      "negI32",
      "negI8",
      "negate",
      "nested",
      "nextChar",
      "openMissing",
      "orDefault",
      "range",
      "relabel",
      "rotate",
      "roundTrip",
      "safeDiv",
      "signed",
      "smallDouble",
      "squares",
      "sumList",
      "swap",
      "swapPair",
      "toSmall",
      "unit",
      "width",
      "wrapU8",
    ])
    expect(Object.keys(A).toSorted()).toEqual(Object.keys(P).toSorted())
    expect(Object.keys(P.Calc).toSorted()).toEqual(["add", "mul"])
  })
})

describe("summary", () => {
  test("the skipped definitions and why", () => {
    const summary: unknown = JSON.parse(
      readFileSync(new URL("../test-out/public.summary.json", import.meta.url), "utf8"),
    )
    expect(summary).toMatchObject({
      module: "LeanTsTest.Public",
      public: expect.arrayContaining([
        { lean: "LeanTsTest.Public.double", typescript: "double" },
        { lean: "LeanTsTest.Public.firstEven?", typescript: "firstEvenQ" },
        { lean: "LeanTsTest.Public.Calc.add", typescript: "Calc.add" },
      ]),
    })
    expect(Reflect.get(Object(summary), "skipped")).toEqual(
      expect.arrayContaining([
        { name: "LeanTsTest.Public.applyTwice", reason: "polymorphic (takes the type `α`)" },
        { name: "LeanTsTest.Public.twice", reason: "function type `Nat → Nat`" },
        {
          name: "LeanTsTest.Public.optOpt",
          reason: "nested `Option` `Option (Option Nat)` (`none` and `some none` are both `null`)",
        },
        { name: "LeanTsTest.Public.below", reason: "takes a proof argument `_h`" },
      ]),
    )
    expect(Reflect.get(Object(summary), "skipped")).toHaveLength(4)
    expect(Reflect.get(Object(summary), "types")).toEqual(
      expect.arrayContaining([
        { lean: "LeanTsTest.Public.Range", typescript: "Range" },
        { lean: "LeanTsTest.Public.Small", typescript: "Small" },
      ]),
    )
    expect(Reflect.get(Object(summary), "types")).toHaveLength(12)
  })
})

describe("Nat and Int", () => {
  test("bigint and safe-integer arguments, bigint results", () => {
    expect(P.double(21n)).toBe(42n)
    expect(P.double(21)).toBe(42n)
    expect(P.double(2n ** 100n)).toBe(2n ** 101n)
    expect(P.negate(-5n)).toBe(5n)
    expect(P.negate(2n ** 70n)).toBe(-(2n ** 70n))
    expect(P.Calc.add(2, 3n)).toBe(5n)
    expect(P.Calc.mul(-2n, 3)).toBe(-6n)
  })

  test("negative, fractional and unsafe numbers are rejected", () => {
    expect(issuesOf(() => P.double(-1))).toEqual([
      { message: "expected a natural number (a non-negative bigint or safe integer)", path: ["n"] },
    ])
    expect(issuesOf(() => P.double(-1n))).toHaveLength(1)
    expect(issuesOf(() => P.double(1.5))).toHaveLength(1)
    expect(issuesOf(() => P.negate(2 ** 60))).toHaveLength(1)
    expect(issuesOf(() => call(P.double, "1"))).toHaveLength(1)
  })
})

describe("fixed-width integers", () => {
  test("UInt8 to UInt32 are numbers, UInt64 and USize are bigints", () => {
    expect(P.mix(1, 2, 3, 4n, 5n)).toBe(15n)
    expect(P.mix(255, 65535, 2 ** 32 - 1, 2n ** 64n - 1n, 0n)).toBe(255n + 65535n + 2n ** 32n - 2n)
    expect(P.wrapU8(100)).toBe(44)
  })

  test("out-of-range unsigned values are rejected", () => {
    expect(issuesOf(() => P.mix(256, 0, 0, 0n, 0n))).toEqual([
      { message: "expected a UInt8 (an integer number)", path: ["a"] },
    ])
    expect(issuesOf(() => P.mix(-1, 0, 0, 0n, 0n))).toHaveLength(1)
    expect(issuesOf(() => P.mix(0, 0, 0, 2n ** 64n, 0n))).toHaveLength(1)
    expect(issuesOf(() => P.mix(0, 0, 0, 0n, -1n))).toHaveLength(1)
    expect(issuesOf(() => call(P.mix, 0, 0, 0, 0, 0n))).toHaveLength(1)
  })

  test("Int8 to Int32 are signed numbers, Int64 and ISize signed bigints", () => {
    expect(P.signed(-1, -2, -3, -4n, -5n)).toBe(-15n)
    expect(P.negI8(5)).toBe(-5)
    expect(P.negI8(-128)).toBe(-128)
    expect(P.negI32(-(2 ** 31) + 1)).toBe(2 ** 31 - 1)
  })

  test("out-of-range signed values are rejected", () => {
    expect(issuesOf(() => P.negI8(128))).toHaveLength(1)
    expect(issuesOf(() => P.negI8(-129))).toHaveLength(1)
    expect(issuesOf(() => P.signed(0, 0, 0, 2n ** 63n, 0n))).toHaveLength(1)
    expect(issuesOf(() => P.signed(0, 0, 0, 0n, -(2n ** 63n) - 1n))).toHaveLength(1)
  })
})

describe("Bool, Char, String, Float, Unit", () => {
  test("Bool is a boolean", () => {
    expect(P.isEven(10)).toBe(true)
    expect(P.isEven(7n)).toBe(false)
    expect(P.flip(true)).toBe(false)
    expect(issuesOf(() => call(P.flip, 1))).toHaveLength(1)
  })

  test("Char is a string of one code point", () => {
    expect(P.nextChar("a")).toBe("b")
    expect(P.nextChar("😀")).toBe("😁")
    expect(issuesOf(() => P.nextChar("ab"))).toHaveLength(1)
    expect(issuesOf(() => P.nextChar(""))).toHaveLength(1)
    expect(issuesOf(() => P.nextChar("\uD800"))).toHaveLength(1)
  })

  test("String is a string; lone surrogates are rejected", () => {
    expect(P.greet("世界")).toBe("こんにちは, 世界! (2)")
    expect(P.greet("😀")).toBe("こんにちは, 😀! (1)")
    expect(issuesOf(() => P.greet("a\uDC00"))).toHaveLength(1)
    expect(P.bytesOf("é")).toEqual([0xc3, 0xa9])
  })

  test("Float and Float32 are numbers", () => {
    expect(P.halve(3)).toBe(1.5)
    expect(P.halve(Number.NaN)).toBeNaN()
    expect(P.halve32(0.1)).toBe(Math.fround(Math.fround(0.1) / 2))
    expect(issuesOf(() => call(P.halve, 1n))).toHaveLength(1)
  })

  test("Unit is undefined", () => {
    expect(P.unit()).toBeUndefined()
    expect(P.unit(undefined)).toBeUndefined()
    expect(issuesOf(() => call(P.unit, null))).toHaveLength(1)
  })
})

describe("constants", () => {
  test("a definition without arguments is evaluated once and kept", () => {
    expect(P.answer()).toBe(42n)
    expect(P.answer()).toBe(42n)
    expect(P.big()).toBe(2n ** 100n)
  })
})

describe("List, Array, Option, products, Except", () => {
  test("List and Array are arrays", () => {
    expect(P.sumList([1n, 2, 3n])).toBe(6n)
    expect(P.sumList([])).toBe(0n)
    expect(P.range(3)).toEqual([0n, 1n, 2n])
    expect(P.squares([-3n, 4])).toEqual([9n, 16n])
    expect(issuesOf(() => call(P.sumList, "123"))).toHaveLength(1)
  })

  test("every invalid element is reported with its path", () => {
    expect(issuesOf(() => call(P.sumList, [1, -1, "x"]))).toEqual([
      {
        message: "expected a natural number (a non-negative bigint or safe integer)",
        path: ["xs", 1],
      },
      {
        message: "expected a natural number (a non-negative bigint or safe integer)",
        path: ["xs", 2],
      },
    ])
  })

  test("Option is a value or null", () => {
    expect(P.firstEvenQ([1, 3, 4, 6])).toBe(4n)
    expect(P.firstEvenQ([1, 3])).toBeNull()
    expect(P.orDefault(null)).toBe("default")
    expect(P.orDefault("x")).toBe("x")
    expect(issuesOf(() => call(P.orDefault, undefined))).toHaveLength(1)
  })

  test("products are arrays of two elements", () => {
    expect(P.swap([1n, "a"])).toEqual(["a", 1n])
    expect(P.rotate([1, [true, "s"]])).toEqual(["s", [1n, true]])
    expect(issuesOf(() => call(P.swap, [1]))).toHaveLength(1)
    expect(issuesOf(() => call(P.rotate, [1, [true, 2]]))).toEqual([
      { message: "expected a string without lone surrogates", path: ["t", 1, 1] },
    ])
  })

  test("nested collections", () => {
    expect(P.nested([[1n, "ab"], null, [7, ""]])).toEqual([[1n, 2n], [], [7n, 0n]])
  })

  test("Except is { ok, value } or { ok, error }", () => {
    expect(P.safeDiv(7, 2)).toEqual({ ok: true, value: 3n })
    expect(P.safeDiv(1, 0)).toEqual({ ok: false, error: "division by zero" })
    expect(P.fromExcept({ ok: true, value: 5 })).toBe(5n)
    expect(P.fromExcept({ ok: false, error: "abc" })).toBe(3n)
    expect(issuesOf(() => call(P.fromExcept, { ok: true }))).toHaveLength(1)
    expect(issuesOf(() => call(P.fromExcept, { ok: false, error: 1 }))).toEqual([
      { message: "expected a string without lone surrogates", path: ["e", "error"] },
    ])
  })
})

describe("IO", () => {
  test("an IO action returns its value", () => {
    expect(P.ioEcho("hi")).toBe("hi!")
    expect(P.ioUnit()).toBeUndefined()
  })

  test("an IO.Error is thrown as a LeanIOError", () => {
    const user = ioErrorOf(() => P.failing())
    expect(user).toBeInstanceOf(Error)
    expect(user.code).toBe("userError")
    expect(user.message).toBe("nope")
    const missing = ioErrorOf(() => P.openMissing("/nonexistent/lean-ts/missing.txt"))
    expect(missing.code).toBe("noFileOrDirectory")
    expect(missing.message).toBe(
      "no such file or directory (error code: 2)\n  file: /nonexistent/lean-ts/missing.txt",
    )
  })
})

function readText(name: string): string {
  return readFileSync(new URL(`../test-out/${name}`, import.meta.url), "utf8")
}

function validate(
  s: { readonly "~standard": { readonly validate: (v: unknown) => unknown } },
  v: unknown,
): unknown {
  return s["~standard"].validate(v)
}

const FLAGS = {
  a: true,
  b: 255,
  c: 1,
  d: 2,
  e: 3n,
  f: 1.5,
  g: 7n,
  h: -128,
  k: "blue",
  ch: "a",
} as const

describe("structures, inductive types and subtypes", () => {
  test("a structure is a plain object and its proof field is checked", () => {
    expect(P.width({ lo: 1n, hi: 5n })).toBe(4n)
    expect(P.mkRange(5, 2)).toEqual({ lo: 2n, hi: 5n })
    expect(Object.isFrozen(P.mkRange(1, 2))).toBe(false)
    expect(validate(P.Range, { lo: 3, hi: 1 })).toEqual({
      issues: [{ message: "Range.ok: lo ≤ hi", path: [] }],
    })
    expect(issuesOf(() => P.width({ lo: 3n, hi: 1n }))).toEqual([
      { message: "Range.ok: lo ≤ hi", path: ["r"] },
    ])
    expect(issuesOf(() => call(P.width, { lo: -1n, hi: 1n }))).toEqual([
      {
        message: "expected a natural number (a non-negative bigint or safe integer)",
        path: ["r", "lo"],
      },
    ])
  })

  test("an inductive type is a union discriminated by ctor", () => {
    expect(validate(P.Discount, { percent: { p: 150 } })).toEqual({
      issues: [{ message: "Discount.percent.h: p ≤ 100", path: [] }],
    })
    expect(validate(P.Discount, { percent: { p: 10 } })).toEqual({
      value: { ctor: "percent", p: 10n },
    })
    expect(validate(P.Discount, { ctor: "fixed", amount: 5n })).toEqual({
      value: { ctor: "fixed", amount: 5n },
    })
    expect(validate(P.Discount, { coupon: ["x", 3] })).toEqual({
      value: { ctor: "coupon", a0: "x", a1: 3n },
    })
    expect(validate(P.Discount, "none")).toEqual({ value: { ctor: "none" } })
    expect(P.applyDiscount({ ctor: "percent", p: 10n }, 200)).toBe(180n)
    expect(P.applyDiscount({ ctor: "coupon", a0: "c", a1: 30n }, 200)).toBe(170n)
    expect(P.halfOff()).toEqual({ ctor: "percent", p: 50n })
    expect(issuesOf(() => call(P.applyDiscount, { percent: { p: 1 } }, 1))).toHaveLength(1)
    expect(issuesOf(() => P.applyDiscount({ ctor: "percent", p: 101n }, 1))).toEqual([
      { message: "Discount.percent.h: p ≤ 100", path: ["d"] },
    ])
  })

  test("an enum is a string literal union; a recursive type round-trips", () => {
    expect(P.Color.next("blue")).toBe("red")
    expect(issuesOf(() => call(P.Color.next, "pink"))).toEqual([
      { message: 'expected one of "red", "green", "blue"', path: ["arg0"] },
    ])
    expect(P.Tree.sum(P.Tree.build(4))).toBe(10n)
    expect(P.Tree.build(1)).toEqual({
      ctor: "node",
      l: { ctor: "leaf" },
      v: 1n,
      r: { ctor: "leaf" },
    })
  })

  test("a structure extending another has the parent's fields flat", () => {
    expect(P.describe({ x: 1n, y: 2n, label: "a", note: null, tag: 3n })).toBe("a@1,2:-:3")
    expect(P.relabel({ x: 1n, y: 2n, label: "a", note: null, tag: null }, "b")).toEqual({
      x: 1n,
      y: 2n,
      label: "b",
      note: "a",
      tag: null,
    })
  })

  test("scalar fields live in the packed scalar area", () => {
    expect(P.bump(FLAGS)).toEqual({
      a: false,
      b: 0,
      c: 2,
      d: 3,
      e: 4n,
      f: 3,
      g: 8n,
      h: 127,
      k: "red",
      ch: "b",
    })
  })

  test("a subtype, a trivial structure and Fin check their property", () => {
    expect(P.smallDouble(4n)).toBe(8n)
    expect(P.toSmall(12)).toBeNull()
    expect(P.toSmall(3)).toBe(3n)
    expect(issuesOf(() => P.smallDouble(12n))).toEqual([
      { message: "Small.property: val < 10", path: ["s"] },
    ])
    expect(P.Pos.pred({ n: 5n })).toBe(4n)
    expect(issuesOf(() => P.Pos.pred({ n: 0n }))).toEqual([
      { message: "Pos.pos: 0 < n", path: ["p"] },
    ])
    expect(P.finSucc(4)).toBe(0)
    expect(issuesOf(() => P.finSucc(5))).toEqual([
      { message: "expected a natural number below 5", path: ["i"] },
    ])
    expect(P.Names.count({ xs: ["a"] })).toBe(1n)
    expect(issuesOf(() => P.Names.count({ xs: ["a", "b", "c", "d"] }))).toEqual([
      { message: "Names.short: xs.length ≤ 3", path: ["n"] },
    ])
  })

  test("a polymorphic structure is a type per instance", () => {
    expect(P.swapPair({ fst: 1n, snd: true })).toEqual({ fst: true, snd: 1n })
    expect(validate(P.PairNatBool, { fst: 2, snd: false })).toEqual({
      value: { fst: 2n, snd: false },
    })
  })

  test("a namespace of functions is merged into the schema of the same name", () => {
    expect(P.Point.sum({ x: 2n, y: 3n })).toBe(5n)
    expect(P.Point["~standard"].vendor).toBe("lean-ts")
  })
})

describe("generation settings", () => {
  test("tagKey and option change the TypeScript form of both directions", () => {
    expect(A.halfOff()).toEqual({ _tag: "percent", p: 50n })
    expect(A.applyDiscount({ _tag: "fixed", amount: 5n }, 7)).toBe(2n)
    expect(validate(A.Discount, { percent: { p: 3 } })).toEqual({
      value: { _tag: "percent", p: 3n },
    })
    expect(A.relabel({ x: 1n, y: 2n, label: "a" }, "b")).toEqual({
      x: 1n,
      y: 2n,
      label: "b",
      note: "a",
    })
    expect(A.toSmall(12)).toBeUndefined()
    expect(A.orDefault(undefined)).toBe("default")
    expect(issuesOf(() => call(A.orDefault, null))).toHaveLength(1)
    expect(validate(A.Labeled, { x: 1, y: 2, label: "a", note: null })).toEqual({
      value: { x: 1n, y: 2n, label: "a" },
    })
  })

  test("both settings round-trip every type through Lean", () => {
    const d = { ctor: "coupon", a0: "c", a1: 1n } as const
    const t = P.Tree.build(2)
    const l = { x: 1n, y: 2n, label: "a", note: "n", tag: null }
    expect(P.roundTrip(d, l, t, FLAGS)).toEqual([d, [l, [t, FLAGS]]])
    const ad = { _tag: "coupon", a0: "c", a1: 1n } as const
    const at = A.Tree.build(2)
    const al = { x: 1n, y: 2n, label: "a", note: "n" }
    expect(A.roundTrip(ad, al, at, FLAGS)).toEqual([ad, [al, [at, FLAGS]]])
    expect(A.Tree.build(1)).toEqual({
      _tag: "node",
      l: { _tag: "leaf" },
      v: 1n,
      r: { _tag: "leaf" },
    })
    expect(S.toJSON(P.Discount, d)).toEqual(S.toJSON(A.Discount, ad))
    expect(S.toJSON(P.Labeled, l)).toEqual(S.toJSON(A.Labeled, al))
  })

  test("a field named as the tagKey and invalid settings stop the generation with 254", () => {
    expect(readText("public-clash.status").trim()).toBe("254")
    expect(readText("public-clash.stderr")).toContain(
      "the constructor `LeanTsTest.Public.Discount.fixed` of `LeanTsTest.Public.Discount` has a field `amount`, which is the tagKey",
    )
    expect(readText("public-badkey.status").trim()).toBe("254")
    expect(readText("public-badkey.stderr")).toContain(
      'tagKey must be a JavaScript identifier (got "not-an-identifier")',
    )
    expect(readText("public-badopt.status").trim()).toBe("254")
    expect(readText("public-badopt.stderr")).toContain(
      'option must be "null" or "undefined" (got "none")',
    )
  })
})

describe("JSON and JSON Schema", () => {
  test("toJSON, stringify and parse use the JSON form of Lean's ToJson", () => {
    expect(S.toJSON(P.Discount, { ctor: "percent", p: 10n })).toEqual({ percent: { p: 10 } })
    expect(S.toJSON(P.Discount, { ctor: "coupon", a0: "x", a1: 2n ** 70n })).toEqual({
      coupon: ["x", "1180591620717411303424"],
    })
    expect(S.stringify(P.Discount, { ctor: "coupon", a0: "x", a1: 2n ** 70n })).toBe(
      '{"coupon":["x",1180591620717411303424]}',
    )
    expect(S.parse(P.Discount, '{"coupon":["x",1180591620717411303424]}')).toEqual({
      ctor: "coupon",
      a0: "x",
      a1: 2n ** 70n,
    })
    expect(S.toJSON(P.Labeled, { x: 1n, y: 2n, label: "a", note: null, tag: null })).toEqual({
      x: 1,
      y: 2,
      label: "a",
      tag: null,
    })
    expect(S.toJSON(P.Flags, FLAGS)).toMatchObject({ e: "3", g: "7" })
    expect(S.fromJSON(P.Range, { lo: 1, hi: 2 })).toEqual({ lo: 1n, hi: 2n })
    expect(() => S.fromJSON(P.Range, { lo: 2, hi: 1 })).toThrow(L.LeanValidationError)
    expect(S.toJSON(S.Nat, 5n)).toBe(5)
  })

  test("jsonSchema describes the JSON form for every target", () => {
    const tree = P.Tree["~standard"].jsonSchema.input({ target: "draft-2020-12" })
    expect(tree).toMatchObject({
      $ref: "#/$defs/Tree",
      $defs: { Tree: { oneOf: [{ const: "leaf" }, {}] } },
    })
    expect(P.Range["~standard"].jsonSchema.output({ target: "draft-2020-12" })).toEqual({
      $schema: "https://json-schema.org/draft/2020-12/schema",
      type: "object",
      properties: { lo: { type: "integer", minimum: 0 }, hi: { type: "integer", minimum: 0 } },
      required: ["lo", "hi"],
      additionalProperties: false,
    })
    expect(P.Discount["~standard"].jsonSchema.input({ target: "draft-07" })).toMatchObject({
      oneOf: [
        { const: "none" },
        {
          properties: {
            percent: { properties: { p: { type: "integer", minimum: 0, maximum: 100 } } },
          },
        },
        {},
        {
          properties: {
            coupon: { type: "array", items: [{ type: "string" }, { type: "integer" }] },
          },
        },
      ],
    })
    expect(P.Pos["~standard"].jsonSchema.input({ target: "openapi-3.0" })).toMatchObject({
      properties: { n: { minimum: 0, exclusiveMinimum: true } },
    })
    expect(P.Labeled["~standard"].jsonSchema.input({ target: "openapi-3.0" })).toMatchObject({
      properties: { tag: { type: "integer", nullable: true } },
      required: ["x", "y", "label"],
    })
    expect(() => P.Range["~standard"].jsonSchema.input({ target: "draft-04" })).toThrow(TypeError)
  })
})
