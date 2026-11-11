import type { StandardJSONSchemaV1, StandardSchemaV1, StandardTypedV1 } from "@standard-schema/spec"
import {
  boolDesc,
  charDesc,
  checkValue,
  float32Desc,
  floatDesc,
  intDesc,
  isizeDesc,
  jsonValue,
  LeanValidationError,
  natDesc,
  sintDesc,
  stringDesc,
  type TypeDesc,
  uintDesc,
  unitDesc,
  usizeDesc,
} from "../runtime/marshal.ts"
import { jsonSchemaOf } from "./desc.ts"

export { type Issue, LeanValidationError } from "../runtime/marshal.ts"
export * from "./desc.ts"

export interface LeanSchema<Input, Output> {
  readonly "~standard": StandardSchemaV1.Props<Input, Output> &
    StandardJSONSchemaV1.Props<Input, Output>
  readonly desc: TypeDesc<Output>
}

export type InferInput<S extends StandardTypedV1> = StandardTypedV1.InferInput<S>

export type InferOutput<S extends StandardTypedV1> = StandardTypedV1.InferOutput<S>

export type UnitInput = Readonly<Record<string, never>> | undefined

export type ExceptInput<E, A> = { readonly ok: A } | { readonly error: E }

export function schema<Input, Output>(desc: TypeDesc<Output>): LeanSchema<Input, Output> {
  const converter = (options: StandardJSONSchemaV1.Options): Record<string, unknown> =>
    jsonSchemaOf(desc, options.target)
  return {
    "~standard": {
      version: 1,
      vendor: "lean-ts",
      validate: (value: unknown): StandardSchemaV1.Result<Output> => checkValue(desc, value),
      jsonSchema: { input: converter, output: converter },
    },
    desc,
  }
}

export function merge<S extends object, M extends object>(target: S, members: M): S & M {
  return Object.assign(target, members)
}

export function fromJSON<Output>(s: LeanSchema<unknown, Output>, json: unknown): Output {
  const r = checkValue(s.desc, json)
  if ("issues" in r) throw new LeanValidationError(r.issues)
  return r.value
}

export function toJSON<Output>(s: LeanSchema<unknown, Output>, value: Output): unknown {
  return jsonValue(s.desc, value, false)
}

function write(v: unknown): string {
  if (v === null) return "null"
  if (typeof v === "bigint") return v.toString()
  if (typeof v === "number") {
    if (!Number.isFinite(v)) throw new TypeError(`lean-ts: ${v} is not a JSON number`)
    return JSON.stringify(v)
  }
  if (typeof v === "string" || typeof v === "boolean") return JSON.stringify(v)
  if (Array.isArray(v)) return `[${v.map((x: unknown) => write(x)).join(",")}]`
  if (typeof v === "object") {
    const parts: string[] = []
    for (const [k, x] of Object.entries(v)) {
      if (x !== undefined) parts.push(`${JSON.stringify(k)}:${write(x)}`)
    }
    return `{${parts.join(",")}}`
  }
  throw new TypeError(`lean-ts: a ${typeof v} is not a JSON value`)
}

export function stringify<Output>(s: LeanSchema<unknown, Output>, value: Output): string {
  return write(jsonValue(s.desc, value, true))
}

const INTEGER = /^-?(?:0|[1-9][0-9]*)$/u

function reviver(this: unknown, _key: string, value: unknown, ...rest: unknown[]): unknown {
  if (typeof value !== "number" || Number.isSafeInteger(value)) return value
  const ctx = rest[0]
  const source: unknown =
    typeof ctx === "object" && ctx !== null ? Reflect.get(ctx, "source") : undefined
  return typeof source === "string" && INTEGER.test(source) ? BigInt(source) : value
}

export function parse<Output>(s: LeanSchema<unknown, Output>, text: string): Output {
  const json: unknown = JSON.parse(text, reviver)
  return fromJSON(s, json)
}

function scalar<Input, Output>(desc: TypeDesc<Output>): LeanSchema<Input, Output> {
  return schema<Input, Output>(desc)
}

type Big = bigint | number | string

export type Nat = bigint
export type Int = bigint

export const Nat: LeanSchema<Big, bigint> = scalar(natDesc)
export const Int: LeanSchema<Big, bigint> = scalar(intDesc)
export const UInt8: LeanSchema<number, number> = scalar(uintDesc(8))
export const UInt16: LeanSchema<number, number> = scalar(uintDesc(16))
export const UInt32: LeanSchema<number, number> = scalar(uintDesc(32))
export const UInt64: LeanSchema<Big, bigint> = scalar(uintDesc(64))
export const USize: LeanSchema<Big, bigint> = scalar(usizeDesc)
export const Int8: LeanSchema<number, number> = scalar(sintDesc(8))
export const Int16: LeanSchema<number, number> = scalar(sintDesc(16))
export const Int32: LeanSchema<number, number> = scalar(sintDesc(32))
export const Int64: LeanSchema<Big, bigint> = scalar(sintDesc(64))
export const ISize: LeanSchema<Big, bigint> = scalar(isizeDesc)
export const Bool: LeanSchema<boolean, boolean> = scalar(boolDesc)
export const Char: LeanSchema<string, string> = scalar(charDesc)
const StringSchema: LeanSchema<string, string> = scalar(stringDesc)
export { StringSchema as String }
export const Float: LeanSchema<number | string, number> = scalar(floatDesc)
export const Float32: LeanSchema<number | string, number> = scalar(float32Desc)
export const Unit: LeanSchema<UnitInput, undefined> = scalar(unitDesc)
