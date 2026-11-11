import fc from "fast-check"
import { describe, expect, test } from "vite-plus/test"
import * as M from "../../test-out/ts-model.ts"

const safe = fc.maxSafeInteger()
const nonzero = safe.filter((n) => n !== 0)
const small = fc.integer({ min: -50, max: 50 })
const text = fc.string({ unit: "grapheme", maxLength: 8 })
const parts = fc.string({ unit: fc.constantFrom("a", "b", "😀", "é"), maxLength: 6 })

function ok(v: bigint): { ok: true; value: bigint } {
  return { ok: true, value: v }
}

function num(n: number): bigint {
  return BigInt(n === 0 ? 0 : n)
}

describe("LeanTsLib.Ts agrees with JavaScript", () => {
  test("xs[i] is Ts.index and xs[i]! is Ts.get", () => {
    fc.assert(
      fc.property(fc.array(safe, { maxLength: 6 }), small, (xs, i) => {
        const js = xs[i]
        expect(M.indexInt(xs, i)).toBe(js === undefined ? null : num(js))
        const got = M.getInt(xs, i)
        if (js === undefined) expect(got).toEqual({ ok: false, error: { ctor: "undefinedValue" } })
        else expect(got).toEqual(ok(num(js)))
      }),
    )
  })

  test("Math.floor(a / b) and Math.trunc(a / b) where the quotient is exact enough", () => {
    fc.assert(
      fc.property(
        small,
        nonzero.filter((b) => Math.abs(b) < 1e6),
        (a, b) => {
          expect(M.floorDiv(a, b)).toEqual(ok(num(Math.floor(a / b))))
          expect(M.truncDiv(a, b)).toEqual(ok(num(Math.trunc(a / b))))
        },
      ),
    )
    expect(M.floorDiv(1, 0)).toEqual({ ok: false, error: { ctor: "zeroDivision" } })
  })

  test("bigint / and % and number % keep the sign of the dividend", () => {
    fc.assert(
      fc.property(
        fc.bigInt(),
        fc.bigInt().filter((b) => b !== 0n),
        (a, b) => {
          expect(M.truncDiv(a, b)).toEqual(ok(a / b))
          expect(M.rem(a, b)).toEqual(ok(a % b))
        },
      ),
    )
    fc.assert(
      fc.property(safe, nonzero, (a, b) => {
        expect(M.rem(a, b)).toEqual(ok(num(a % b)))
      }),
    )
    expect(() => 1n / 0n).toThrow(RangeError)
    expect(M.rem(1n, 0n)).toEqual({ ok: false, error: { ctor: "zeroDivision" } })
  })

  test("for (let i = a; i < b; i++) is Ts.range", () => {
    fc.assert(
      fc.property(small, small, (a, b) => {
        const js: bigint[] = []
        for (let i = a; i < b; i++) js.push(BigInt(i))
        expect(M.range(a, b)).toEqual(js)
      }),
    )
  })

  test("Math.abs and .length", () => {
    fc.assert(
      fc.property(safe, fc.array(safe, { maxLength: 6 }), (a, xs) => {
        expect(M.abs(a)).toBe(num(Math.abs(a)))
        expect(M.lengthInt(xs)).toBe(BigInt(xs.length))
      }),
    )
  })

  test("string .length counts UTF-16 code units", () => {
    fc.assert(
      fc.property(text, (s) => {
        expect(M.strLength(s)).toBe(BigInt(s.length))
      }),
    )
    expect(M.strLength("😀a")).toBe(3n)
  })

  test("startsWith, endsWith and includes", () => {
    fc.assert(
      fc.property(parts, parts, (s, t) => {
        expect(M.startsWith(s, t)).toBe(s.startsWith(t))
        expect(M.endsWith(s, t)).toBe(s.endsWith(t))
        expect(M.includes(s, t)).toBe(s.includes(t))
      }),
    )
  })

  test("template literals of integers and booleans", () => {
    fc.assert(
      fc.property(safe, fc.bigInt(), fc.boolean(), (n, b, x) => {
        expect(M.strInt(n)).toBe(`${n}`)
        expect(M.strInt(b)).toBe(`${b}`)
        expect(M.strBool(x)).toBe(`${x}`)
      }),
    )
  })

  test("throw new RangeError(message)", () => {
    expect(M.error("RangeError", "out of range")).toEqual({
      ok: false,
      error: { ctor: "error", name: "RangeError", message: "out of range" },
    })
    expect(M.unwrapInt(null)).toEqual({ ok: false, error: { ctor: "undefinedValue" } })
  })
})
