import { readFileSync } from "node:fs"
import { describe, expect, test } from "vite-plus/test"
import * as L from "../src/runtime/index.ts"
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
      "answer",
      "big",
      "bytesOf",
      "double",
      "failing",
      "firstEvenQ",
      "flip",
      "fromExcept",
      "greet",
      "halve",
      "halve32",
      "ioEcho",
      "ioUnit",
      "isEven",
      "mix",
      "negI32",
      "negI8",
      "negate",
      "nested",
      "nextChar",
      "openMissing",
      "orDefault",
      "range",
      "rotate",
      "safeDiv",
      "signed",
      "squares",
      "sumList",
      "swap",
      "unit",
      "wrapU8",
    ])
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
        {
          name: "LeanTsTest.Public.Point.sum",
          reason: "unsupported type `LeanTsTest.Public.Point`",
        },
      ]),
    )
    expect(Reflect.get(Object(summary), "skipped")).toHaveLength(5)
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
