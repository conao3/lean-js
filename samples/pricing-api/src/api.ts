import { sValidator } from "@hono/standard-validator"
import { Hono } from "hono"
import { pricing } from "./pricing.ts"

export const app = new Hono()
  .post("/total", sValidator("json", pricing.Order), (c) =>
    c.json({ total: Number(pricing.total(c.req.valid("json"))) }),
  )
  .get("/openapi.json", (c) =>
    c.json({
      openapi: "3.0.3",
      info: { title: "pricing", version: "1" },
      paths: {
        "/total": {
          post: {
            requestBody: {
              required: true,
              content: { "application/json": { schema: { $ref: "#/components/schemas/Order" } } },
            },
            responses: { "200": { description: "the total" }, "400": { description: "invalid" } },
          },
        },
      },
      components: {
        schemas: {
          Order: pricing.Order["~standard"].jsonSchema.input({ target: "openapi-3.0" }),
        },
      },
    }),
  )
