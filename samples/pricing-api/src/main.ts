import * as z from "zod"
import { app } from "./api.ts"

const Answer = z.object({
  total: z.number().optional(),
  error: z.array(z.object({ message: z.string() })).optional(),
})

const Doc = z.object({
  components: z.object({
    schemas: z.object({
      Order: z.object({
        properties: z.object({ discount: z.object({ oneOf: z.array(z.unknown()) }) }),
      }),
    }),
  }),
})

async function post(body: unknown): Promise<string> {
  const r = await app.request("/total", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify(body),
  })
  const a = Answer.parse(await r.json())
  return `${r.status} ${a.total ?? a.error?.[0]?.message ?? ""}`
}

const items = [
  { sku: "apple", qty: 3, unitPrice: 120 },
  { sku: "pear", qty: 1, unitPrice: 200 },
]
for (const discount of [
  "none",
  { percent: { p: 25 } },
  { fixed: { amount: 1000 } },
  { percent: { p: 150 } },
])
  console.log(JSON.stringify(discount), await post({ items, discount }))
console.log("qty 0", await post({ items: [{ sku: "x", qty: 0, unitPrice: 1 }], discount: "none" }))

const doc = Doc.parse(await (await app.request("/openapi.json")).json())
console.log(JSON.stringify(doc.components.schemas.Order.properties.discount.oneOf[1]))
