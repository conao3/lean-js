import { blockRegistry } from "../runtime/block.ts"
import { resolve, type SchemaBounds, type TypeDesc, type VariantDesc } from "../runtime/marshal.ts"

export {
  type Absent,
  type DescNode,
  type FieldDesc,
  type InvariantDesc,
  resolve,
  type SchemaBounds,
  type Slot,
  type TypeDesc,
  type VariantDesc,
} from "../runtime/marshal.ts"

export type JsonSchemaTarget = "draft-2020-12" | "draft-07" | "openapi-3.0"

type Js = Record<string, unknown>

const TARGETS: readonly string[] = ["draft-2020-12", "draft-07", "openapi-3.0"]

function isTarget(t: string): t is JsonSchemaTarget {
  return TARGETS.includes(t)
}

function isRecord(v: unknown): v is Readonly<Record<string, unknown>> {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

function unreachable(d: never): never {
  throw new TypeError(`lean-ts: unknown type descriptor ${JSON.stringify(d)}`)
}

function withBounds(s: Js, bounds: SchemaBounds): Js {
  if (Object.keys(bounds).length === 0) return s
  if ("$ref" in s || "anyOf" in s || "oneOf" in s || "allOf" in s)
    return { allOf: [s, { ...bounds }] }
  return { ...s, ...bounds }
}

function modelJsonSchema(key: string, name: string, target: JsonSchemaTarget): Js {
  const s: unknown = blockRegistry().models.get(key)
  const std: unknown = isRecord(s) ? s["~standard"] : undefined
  const converter: unknown = isRecord(std) ? std["jsonSchema"] : undefined
  const input: unknown = isRecord(converter) ? converter["input"] : undefined
  if (typeof input !== "function")
    throw new TypeError(
      `lean-ts: the model ${name} (${key}) is not registered as a Standard JSON Schema; the lean(...) block that declares it has not run`,
    )
  const out: unknown = Reflect.apply(input, converter, [{ target }])
  if (!isRecord(out))
    throw new TypeError(`lean-ts: the JSON Schema of the model ${name} is not an object`)
  const { $schema: _, ...rest } = out
  return rest
}

function openapiBounds(v: unknown): unknown {
  if (Array.isArray(v)) return v.map(openapiBounds)
  if (!isRecord(v)) return v
  const out: Js = {}
  for (const [k, x] of Object.entries(v)) {
    if (k === "exclusiveMinimum" && typeof x === "number") {
      out["minimum"] = x
      out["exclusiveMinimum"] = true
    } else if (k === "exclusiveMaximum" && typeof x === "number") {
      out["maximum"] = x
      out["exclusiveMaximum"] = true
    } else out[k] = openapiBounds(x)
  }
  return out
}

export function jsonSchemaOf(root: TypeDesc, target: string): Js {
  if (!isTarget(target))
    throw new TypeError(
      `lean-ts: unsupported JSON Schema target ${JSON.stringify(target)} (expected one of ${TARGETS.join(", ")})`,
    )
  const defsKey = target === "draft-2020-12" ? "$defs" : "definitions"
  const defs = new Map<string, Js>()
  const needed = new Set<string>()
  const stack: string[] = []
  const ref = (name: string): Js => ({ $ref: `#/${defsKey}/${name}` })
  const named = (name: string, make: () => Js): Js => {
    if (stack.includes(name)) {
      needed.add(name)
      return ref(name)
    }
    if (defs.has(name)) return ref(name)
    stack.push(name)
    const s = make()
    stack.pop()
    if (!needed.has(name)) return s
    defs.set(name, s)
    return ref(name)
  }
  const constant = (v: string): Js =>
    target === "openapi-3.0" ? { type: "string", enum: [v] } : { const: v }
  const tuple = (items: readonly Js[]): Js =>
    target === "draft-2020-12"
      ? { type: "array", prefixItems: items, minItems: items.length, maxItems: items.length }
      : { type: "array", items, minItems: items.length, maxItems: items.length }
  const fieldsSchema = (variant: VariantDesc): Js => {
    const properties: Js = {}
    const required: string[] = []
    for (const f of variant.fields) {
      if (f.flat) {
        const parent = fieldsSchema(structVariant(f.desc))
        Object.assign(properties, parent["properties"])
        const req: unknown = parent["required"]
        if (Array.isArray(req)) for (const r of req) if (typeof r === "string") required.push(r)
        continue
      }
      properties[f.key] = withBounds(gen(f.desc), f.bounds)
      if (resolve(f.desc).kind !== "option") required.push(f.key)
    }
    return { type: "object", properties, required, additionalProperties: false }
  }
  const gen = (d: TypeDesc): Js => {
    switch (d.kind) {
      case "nat":
        return { type: "integer", minimum: 0 }
      case "int":
        return { type: "integer" }
      case "uint":
        return d.bits === 64
          ? { type: "string", pattern: "^(0|[1-9][0-9]*)$" }
          : { type: "integer", minimum: 0, maximum: 2 ** d.bits - 1 }
      case "sint":
        return d.bits === 64
          ? { type: "integer", minimum: -(2 ** 63), exclusiveMaximum: 2 ** 63 }
          : { type: "integer", minimum: -(2 ** (d.bits - 1)), maximum: 2 ** (d.bits - 1) - 1 }
      case "usize":
        return { type: "string", pattern: "^(0|[1-9][0-9]*)$" }
      case "isize":
        return { type: "integer", minimum: -(2 ** 63), exclusiveMaximum: 2 ** 63 }
      case "fin":
        return { type: "integer", minimum: 0, exclusiveMaximum: Number(d.bound) }
      case "bool":
        return { type: "boolean" }
      case "char":
        return { type: "string", minLength: 1, maxLength: 1 }
      case "string":
        return { type: "string" }
      case "float":
      case "float32":
        return { type: "number" }
      case "unit":
        return { type: "object", additionalProperties: false }
      case "list":
      case "array":
        return { type: "array", items: gen(d.item) }
      case "option": {
        const item = gen(d.item)
        if (target !== "openapi-3.0") return { anyOf: [item, { type: "null" }] }
        if ("type" in item && !("$ref" in item)) return { ...item, nullable: true }
        return { allOf: [item], nullable: true }
      }
      case "prod":
        return tuple([gen(d.fst), gen(d.snd)])
      case "except":
        return {
          oneOf: [
            {
              type: "object",
              properties: { ok: gen(d.value) },
              required: ["ok"],
              additionalProperties: false,
            },
            {
              type: "object",
              properties: { error: gen(d.error) },
              required: ["error"],
              additionalProperties: false,
            },
          ],
        }
      case "struct":
        return named(d.name, () => fieldsSchema(d.variant))
      case "enum":
        return named(d.name, () => ({ type: "string", enum: [...d.ctors] }))
      case "inductive":
        return named(d.name, () => ({
          oneOf: d.variants.map((v) => {
            if (v.fields.length === 0) return constant(v.name)
            const payload = !v.positional
              ? fieldsSchema(v)
              : v.fields.length === 1 && v.fields[0] !== undefined
                ? withBounds(gen(v.fields[0].desc), v.fields[0].bounds)
                : tuple(v.fields.map((f) => withBounds(gen(f.desc), f.bounds)))
            return {
              type: "object",
              properties: { [v.name]: payload },
              required: [v.name],
              additionalProperties: false,
            }
          }),
        }))
      case "subtype":
        return named(d.name, () => withBounds(gen(d.base), d.bounds))
      case "model":
        return named(d.name, () => modelJsonSchema(d.key, d.name, target))
      case "ref":
        return gen(d.get())
    }
    return unreachable(d)
  }
  const top = gen(root)
  const withDefs =
    defs.size === 0
      ? top
      : target === "draft-2020-12"
        ? { ...top, [defsKey]: Object.fromEntries(defs) }
        : { allOf: [top], [defsKey]: Object.fromEntries(defs) }
  const out = target === "openapi-3.0" ? openapiBounds(withDefs) : withDefs
  const schemaUri =
    target === "draft-2020-12"
      ? "https://json-schema.org/draft/2020-12/schema"
      : target === "draft-07"
        ? "http://json-schema.org/draft-07/schema#"
        : undefined
  if (!isRecord(out)) throw new TypeError("lean-ts: the generated JSON Schema is not an object")
  return schemaUri === undefined ? { ...out } : { $schema: schemaUri, ...out }
}

function structVariant(d: TypeDesc): VariantDesc {
  const r = resolve(d)
  if (r.kind !== "struct")
    throw new TypeError(`lean-ts: a flattened field is not a structure (${r.kind})`)
  return r.variant
}
