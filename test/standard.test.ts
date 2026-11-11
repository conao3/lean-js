import { sValidator } from "@hono/standard-validator"
import type { StandardJSONSchemaV1, StandardSchemaV1 } from "@standard-schema/spec"
import { Hono } from "hono"
import { describe, expect, test } from "vite-plus/test"
import * as z from "zod"
import * as S from "../src/schema/index.ts"
import * as P from "../test-out/public.ts"

const discount: StandardSchemaV1<P.DiscountInput, P.Discount> &
  StandardJSONSchemaV1<P.DiscountInput, P.Discount> = P.Discount satisfies StandardSchemaV1 &
  StandardJSONSchemaV1

const output: P.Discount = { ctor: "fixed", amount: 1n } satisfies StandardSchemaV1.InferOutput<
  typeof P.Discount
>

const nat: StandardSchemaV1<bigint | number | string, bigint> = S.Nat

function ok(v: unknown): boolean {
  const r = P.Discount["~standard"].validate(v)
  return !(r instanceof Promise) && r.issues === undefined
}

describe("Standard Schema", () => {
  test("the generated schemas are Standard Schema and Standard JSON Schema values", () => {
    expect(discount["~standard"].version).toBe(1)
    expect(discount["~standard"].vendor).toBe("lean-ts")
    expect(output.ctor).toBe("fixed")
    expect(nat["~standard"].validate("12")).toEqual({ value: 12n })
    expect(discount["~standard"].validate({ fixed: { amount: 2 } })).toEqual({
      value: { ctor: "fixed", amount: 2n },
    })
  })

  test("Hono's sValidator answers 400 for an invalid body and passes the Lean value", async () => {
    const app = new Hono().post("/apply", sValidator("json", P.Range), (c) => {
      const r = c.req.valid("json")
      return c.json(S.toJSON(P.Range, P.mkRange(r.hi, r.lo)))
    })
    const post = (body: unknown): Promise<Response> =>
      Promise.resolve(
        app.request("/apply", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify(body),
        }),
      )
    const bad = await post({ lo: 3, hi: 1 })
    expect(bad.status).toBe(400)
    expect(JSON.stringify(await bad.json())).toContain("Range.ok: lo ≤ hi")
    const good = await post({ lo: 1, hi: 3 })
    expect(good.status).toBe(200)
    expect(await good.json()).toEqual({ lo: 1, hi: 3 })
    const discountApp = new Hono().post("/price", sValidator("json", P.Discount), (c) =>
      c.json({ price: String(P.applyDiscount(c.req.valid("json"), 200)) }),
    )
    const price = async (body: unknown): Promise<Response> =>
      discountApp.request("/price", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(body),
      })
    expect((await price({ percent: { p: 150 } })).status).toBe(400)
    const paid = await price({ percent: { p: 10 } })
    expect(paid.status).toBe(200)
    expect(await paid.json()).toEqual({ price: "180" })
  })

  test("a lean-ts schema runs inside a zod schema", () => {
    const Order = z.object({ id: z.string(), d: z.custom<P.Discount>(ok) })
    expect(Order.safeParse({ id: "a", d: { percent: { p: 10 } } }).success).toBe(true)
    expect(Order.safeParse({ id: "a", d: { percent: { p: 101 } } }).success).toBe(false)
  })
})
