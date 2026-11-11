import { blockRegistry } from "./block.ts"
import {
  lean_io_error_to_string,
  lean_io_result_get_error,
  lean_io_result_get_value,
  lean_io_result_is_ok,
} from "./io.ts"
import {
  asArray,
  asCtor,
  asNat,
  asString,
  type Ctor,
  lean_alloc_ctor,
  lean_ctor,
  lean_ctor_get,
  lean_ctor_get_f32,
  lean_ctor_get_f64,
  lean_ctor_get_u16,
  lean_ctor_get_u32,
  lean_ctor_get_u64,
  lean_ctor_get_u8,
  lean_ctor_set_f32,
  lean_ctor_set_f64,
  lean_ctor_set_u16,
  lean_ctor_set_u32,
  lean_ctor_set_u64,
  lean_ctor_set_u8,
  lean_ctor_uget,
  lean_ctor_uset,
  lean_tag,
  lean_unbox,
  type Obj,
} from "./object.ts"
import { WORD_BITS } from "./uint.ts"

export type Slot = "obj" | "usize" | "u8" | "u16" | "u32" | "u64" | "f64" | "f32" | "none"

export type SchemaBounds = Readonly<Record<string, number>>

export interface FieldDesc {
  readonly key: string
  readonly desc: TypeDesc
  readonly slot: Slot
  readonly at: number
  readonly omitNone: boolean
  readonly flat: boolean
  readonly bounds: SchemaBounds
}

export interface InvariantDesc {
  readonly field: string
  readonly prop: string
  readonly args: readonly number[]
  readonly decide: (...args: Obj[]) => boolean
}

export interface VariantDesc {
  readonly name: string
  readonly cidx: number
  readonly size: number
  readonly usize: number
  readonly ssize: number
  readonly positional: boolean
  readonly fields: readonly FieldDesc[]
  readonly invariants: readonly InvariantDesc[]
}

export type Absent = "null" | "undefined"

export type DescNode =
  | { readonly kind: "nat" | "int" | "bool" | "char" | "string" | "float" | "float32" | "unit" }
  | { readonly kind: "uint" | "sint"; readonly bits: 8 | 16 | 32 | 64 }
  | { readonly kind: "usize" | "isize" }
  | { readonly kind: "list" | "array"; readonly item: TypeDesc }
  | { readonly kind: "option"; readonly item: TypeDesc; readonly absent: Absent }
  | { readonly kind: "prod"; readonly fst: TypeDesc; readonly snd: TypeDesc }
  | { readonly kind: "except"; readonly error: TypeDesc; readonly value: TypeDesc }
  | { readonly kind: "fin"; readonly bound: bigint }
  | {
      readonly kind: "struct"
      readonly name: string
      readonly variant: VariantDesc
      readonly trivial: number | null
    }
  | { readonly kind: "enum"; readonly name: string; readonly ctors: readonly string[] }
  | {
      readonly kind: "inductive"
      readonly name: string
      readonly tagKey: string
      readonly variants: readonly VariantDesc[]
    }
  | {
      readonly kind: "subtype"
      readonly name: string
      readonly base: TypeDesc
      readonly invariant: InvariantDesc
      readonly bounds: SchemaBounds
    }
  | {
      readonly kind: "model"
      readonly name: string
      readonly key: string
      readonly struct: TypeDesc
    }
  | { readonly kind: "ref"; readonly get: () => TypeDesc }

export type TypeDesc<T = unknown> = DescNode & { readonly output?: T }

export type Except<E, A> = { ok: true; value: A } | { ok: false; error: E }

export const natDesc: TypeDesc<bigint> = { kind: "nat" }
export const intDesc: TypeDesc<bigint> = { kind: "int" }
export const boolDesc: TypeDesc<boolean> = { kind: "bool" }
export const charDesc: TypeDesc<string> = { kind: "char" }
export const stringDesc: TypeDesc<string> = { kind: "string" }
export const floatDesc: TypeDesc<number> = { kind: "float" }
export const float32Desc: TypeDesc<number> = { kind: "float32" }
export const unitDesc: TypeDesc<undefined> = { kind: "unit" }
export const usizeDesc: TypeDesc<bigint> = { kind: "usize" }
export const isizeDesc: TypeDesc<bigint> = { kind: "isize" }

export function uintDesc(bits: 8 | 16 | 32): TypeDesc<number>
export function uintDesc(bits: 64): TypeDesc<bigint>
export function uintDesc(bits: 8 | 16 | 32 | 64): TypeDesc {
  return { kind: "uint", bits }
}

export function sintDesc(bits: 8 | 16 | 32): TypeDesc<number>
export function sintDesc(bits: 64): TypeDesc<bigint>
export function sintDesc(bits: 8 | 16 | 32 | 64): TypeDesc {
  return { kind: "sint", bits }
}

export function listDesc<T>(item: TypeDesc<T>): TypeDesc<T[]> {
  return { kind: "list", item }
}

export function arrayDesc<T>(item: TypeDesc<T>): TypeDesc<T[]> {
  return { kind: "array", item }
}

export function optionDesc<T>(item: TypeDesc<T>, absent: "null"): TypeDesc<T | null>
export function optionDesc<T>(item: TypeDesc<T>, absent: "undefined"): TypeDesc<T | undefined>
export function optionDesc(item: TypeDesc, absent: Absent): TypeDesc {
  return { kind: "option", item, absent }
}

export function prodDesc<A, B>(fst: TypeDesc<A>, snd: TypeDesc<B>): TypeDesc<readonly [A, B]> {
  return { kind: "prod", fst, snd }
}

export function exceptDesc<E, A>(error: TypeDesc<E>, value: TypeDesc<A>): TypeDesc<Except<E, A>> {
  return { kind: "except", error, value }
}

export function finDesc<T extends number | bigint>(bound: bigint): TypeDesc<T> {
  return { kind: "fin", bound }
}

export function refDesc<T>(get: () => TypeDesc<T>): TypeDesc<T> {
  return { kind: "ref", get }
}

export function typeDesc<T>(node: DescNode): TypeDesc<T> {
  return node
}

export function modelDesc<T>(key: string, name: string, struct: TypeDesc): TypeDesc<T> {
  return { kind: "model", key, name, struct }
}

export interface Issue {
  readonly message: string
  readonly path: readonly PropertyKey[]
}

export class LeanValidationError extends Error {
  readonly issues: readonly Issue[]

  constructor(issues: readonly Issue[]) {
    super(issues.map((i) => `${i.path.map(String).join(".")}: ${i.message}`).join("\n"))
    this.name = "LeanValidationError"
    this.issues = issues
  }
}

const IO_ERROR_CTORS: readonly string[] = [
  "alreadyExists",
  "otherError",
  "resourceBusy",
  "resourceVanished",
  "unsupportedOperation",
  "hardwareFault",
  "unsatisfiedConstraints",
  "illegalOperation",
  "protocolError",
  "timeExpired",
  "interrupted",
  "noFileOrDirectory",
  "invalidArgument",
  "permissionDenied",
  "resourceExhausted",
  "inappropriateType",
  "noSuchThing",
  "unexpectedEof",
  "userError",
]

function ioErrorCtor(tag: number): string {
  const name = IO_ERROR_CTORS[tag]
  if (name === undefined) throw new TypeError(`lean-ts runtime: IO.Error has no constructor ${tag}`)
  return name
}

export class LeanIOError extends Error {
  readonly code: string

  constructor(error: Obj) {
    super(lean_io_error_to_string(error))
    this.name = "LeanIOError"
    this.code = ioErrorCtor(lean_tag(error))
  }
}

const LONE_SURROGATE = /[\uD800-\uDFFF]/u

const DECIMAL = /^-?(?:0|[1-9][0-9]*)$/u

function unreachable(d: never): never {
  throw new TypeError(`lean-ts runtime: unknown type descriptor ${JSON.stringify(d)}`)
}

export function resolve(d: TypeDesc): TypeDesc {
  let cur = d
  while (cur.kind === "ref") cur = cur.get()
  return cur
}

function expected(d: TypeDesc): string {
  switch (d.kind) {
    case "nat":
      return "a natural number (a non-negative bigint or safe integer)"
    case "int":
      return "an integer (a bigint or safe integer)"
    case "uint":
      return d.bits === 64 ? "a UInt64 (a bigint)" : `a UInt${d.bits} (an integer number)`
    case "sint":
      return d.bits === 64 ? "an Int64 (a bigint)" : `an Int${d.bits} (an integer number)`
    case "usize":
      return "a USize (a bigint)"
    case "isize":
      return "an ISize (a bigint)"
    case "bool":
      return "a boolean"
    case "char":
      return "a Char (a string of one Unicode scalar value)"
    case "string":
      return "a string without lone surrogates"
    case "float":
    case "float32":
      return "a number"
    case "unit":
      return "undefined"
    case "list":
    case "array":
      return "an array"
    case "option":
      return d.absent === "null" ? "a value or null" : "a value or undefined"
    case "prod":
      return "an array of two elements"
    case "except":
      return "an object { ok: true, value } or { ok: false, error }"
    case "fin":
      return `a natural number below ${d.bound}`
    case "struct":
      return `an object ${d.name}`
    case "enum":
      return `one of ${d.ctors.map((c) => JSON.stringify(c)).join(", ")}`
    case "inductive":
      return `a ${d.name} (an object with a constructor name in ${JSON.stringify(d.tagKey)}, or its JSON form)`
    case "subtype":
      return expected(d.base)
    case "model":
      return `a ${d.name}`
    case "ref":
      return expected(d.get())
  }
  return unreachable(d)
}

function integer(v: unknown, json: boolean): bigint | null {
  if (typeof v === "bigint") return v
  if (typeof v === "number" && Number.isSafeInteger(v)) return BigInt(v)
  if (json && typeof v === "string" && DECIMAL.test(v)) return BigInt(v)
  return null
}

function inRange(
  v: unknown,
  bits: number,
  signed: boolean,
  big: boolean,
  json: boolean,
): bigint | null {
  const i =
    big || json ? integer(v, json) : typeof v === "number" && Number.isInteger(v) ? BigInt(v) : null
  if (i === null || (big && !json && typeof v !== "bigint")) return null
  const n = BigInt(bits)
  const lo = signed ? -(1n << (n - 1n)) : 0n
  const hi = signed ? 1n << (n - 1n) : 1n << n
  return i >= lo && i < hi ? i : null
}

function isObject(v: unknown): v is object {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

function record(v: unknown, key: string): { readonly found: boolean; readonly value: unknown } {
  if (typeof v !== "object" || v === null || !Object.hasOwn(v, key))
    return { found: false, value: undefined }
  return { found: true, value: Reflect.get(v, key) }
}

function charCode(v: unknown): number | null {
  if (typeof v !== "string") return null
  const cp = v.codePointAt(0)
  if (cp === undefined || String.fromCodePoint(cp) !== v || (cp >= 0xd800 && cp <= 0xdfff))
    return null
  return cp
}

function floatValue(v: unknown, json: boolean): number | null {
  if (typeof v === "number") return v
  if (!json) return null
  if (typeof v === "bigint") return Number(v)
  if (v === "NaN") return Number.NaN
  if (v === "Infinity") return Number.POSITIVE_INFINITY
  if (v === "-Infinity") return Number.NEGATIVE_INFINITY
  return null
}

function isUnit(v: unknown, json: boolean): boolean {
  return v === undefined || (json && isObject(v) && Object.keys(v).length === 0)
}

function isAbsent(v: unknown, absent: Absent, json: boolean): boolean {
  if (json) return v === null || v === undefined
  return absent === "null" ? v === null : v === undefined
}

interface Ctx {
  readonly json: boolean
  readonly issues: Issue[]
}

interface Picked {
  readonly variant: VariantDesc
  readonly inputs: readonly FieldInput[]
}

interface FieldInput {
  readonly value: unknown
  readonly path: readonly PropertyKey[]
}

function objectInputs(
  variant: VariantDesc,
  v: unknown,
  path: readonly PropertyKey[],
): FieldInput[] {
  return variant.fields.map((f) =>
    f.flat ? { value: v, path } : { value: record(v, f.key).value, path: [...path, f.key] },
  )
}

function jsonInputs(
  variant: VariantDesc,
  payload: unknown,
  path: readonly PropertyKey[],
): FieldInput[] | null {
  const at = [...path, variant.name]
  if (!variant.positional) return isObject(payload) ? objectInputs(variant, payload, at) : null
  if (variant.fields.length === 1) return [{ value: payload, path: at }]
  if (!Array.isArray(payload) || payload.length !== variant.fields.length) return null
  const items: unknown[] = payload
  return items.map((value, i) => ({ value, path: [...at, i] }))
}

function pick(
  d: Extract<DescNode, { kind: "inductive" }>,
  v: unknown,
  path: readonly PropertyKey[],
  json: boolean,
): Picked | null {
  const tag = record(v, d.tagKey)
  if (isObject(v) && typeof tag.value === "string") {
    const variant = d.variants.find((x) => x.name === tag.value)
    if (variant !== undefined) return { variant, inputs: objectInputs(variant, v, path) }
  }
  if (!json) return null
  if (typeof v === "string") {
    const variant = d.variants.find((x) => x.name === v && x.fields.length === 0)
    return variant === undefined ? null : { variant, inputs: [] }
  }
  if (!isObject(v)) return null
  const keys = Object.keys(v)
  const only = keys[0]
  if (keys.length !== 1 || only === undefined) return null
  const variant = d.variants.find((x) => x.name === only && x.fields.length !== 0)
  if (variant === undefined) return null
  const inputs = jsonInputs(variant, Reflect.get(v, only), path)
  return inputs === null ? null : { variant, inputs }
}

function store(c: Ctor, f: FieldDesc, x: Obj): void {
  switch (f.slot) {
    case "obj":
      c.fields[f.at] = x
      return
    case "usize":
      lean_ctor_uset(c, f.at, asNat(x))
      return
    case "u8":
      lean_ctor_set_u8(c, f.at, lean_unbox(x))
      return
    case "u16":
      lean_ctor_set_u16(c, f.at, lean_unbox(x))
      return
    case "u32":
      lean_ctor_set_u32(c, f.at, lean_unbox(x))
      return
    case "u64":
      lean_ctor_set_u64(c, f.at, asNat(x))
      return
    case "f64":
      lean_ctor_set_f64(c, f.at, lean_unbox(x))
      return
    case "f32":
      lean_ctor_set_f32(c, f.at, lean_unbox(x))
      return
    case "none":
      return
  }
  unreachable(f.slot)
}

function load(x: Obj, f: FieldDesc): Obj {
  switch (f.slot) {
    case "obj":
      return lean_ctor_get(x, f.at)
    case "usize":
      return lean_ctor_uget(x, f.at)
    case "u8":
      return lean_ctor_get_u8(x, f.at)
    case "u16":
      return lean_ctor_get_u16(x, f.at)
    case "u32":
      return lean_ctor_get_u32(x, f.at)
    case "u64":
      return lean_ctor_get_u64(x, f.at)
    case "f64":
      return lean_ctor_get_f64(x, f.at)
    case "f32":
      return lean_ctor_get_f32(x, f.at)
    case "none":
      return 0
  }
  return unreachable(f.slot)
}

function build(variant: VariantDesc, values: readonly Obj[]): Obj {
  if (variant.size === 0 && variant.usize === 0 && variant.ssize === 0) return variant.cidx
  const c = lean_alloc_ctor(variant.cidx, variant.size, variant.usize, variant.ssize)
  variant.fields.forEach((f, i) => store(c, f, values[i]))
  return c
}

function checkInvariants(
  owner: string,
  variant: VariantDesc,
  values: readonly Obj[],
  path: readonly PropertyKey[],
  issues: Issue[],
): void {
  for (const inv of variant.invariants) {
    if (!inv.decide(...inv.args.map((i) => values[i])))
      issues.push({ message: `${owner}.${inv.field}: ${inv.prop}`, path })
  }
}

function ownerName(
  d: { readonly kind: "struct" | "inductive"; readonly name: string },
  v: VariantDesc,
): string {
  return d.kind === "struct" ? d.name : `${d.name}.${v.name}`
}

interface StandardResult {
  readonly value: unknown
  readonly issues: readonly Issue[] | null
}

function segment(p: unknown): PropertyKey {
  if (typeof p === "string" || typeof p === "number" || typeof p === "symbol") return p
  const key = record(p, "key").value
  if (typeof key === "string" || typeof key === "number" || typeof key === "symbol") return key
  return String(key)
}

export function standardValidate(schema: unknown, value: unknown): StandardResult {
  const std = record(schema, "~standard").value
  const validate = record(std, "validate").value
  if (typeof validate !== "function")
    throw new TypeError("lean-ts runtime: the model is not a Standard Schema")
  const r: unknown = Reflect.apply(validate, std, [value])
  if (r instanceof Promise)
    throw new TypeError("lean-ts runtime: the model's ~standard.validate returned a Promise")
  const issues = record(r, "issues").value
  if (Array.isArray(issues)) {
    const items: unknown[] = issues
    return {
      value: undefined,
      issues: items.map((i) => {
        const p = record(i, "path").value
        const segments: unknown[] = Array.isArray(p) ? p : []
        return { message: String(record(i, "message").value), path: segments.map(segment) }
      }),
    }
  }
  return { value: record(r, "value").value, issues: null }
}

function modelSchema(d: { readonly key: string; readonly name: string }): unknown {
  const s = blockRegistry().models.get(d.key)
  if (s === undefined)
    throw new TypeError(
      `lean-ts runtime: the model ${d.name} (${d.key}) is not registered; the lean(...) block that declares it has not run`,
    )
  return s
}

function runModel(
  d: { readonly key: string; readonly name: string },
  v: unknown,
  path: readonly PropertyKey[],
  issues: Issue[],
): { readonly ok: boolean; readonly value: unknown } {
  const r = standardValidate(modelSchema(d), v)
  if (r.issues !== null) {
    for (const i of r.issues) issues.push({ message: i.message, path: [...path, ...i.path] })
    return { ok: false, value: undefined }
  }
  return { ok: true, value: r.value }
}

function encode(d: TypeDesc, v: unknown, path: readonly PropertyKey[], cx: Ctx): Obj {
  const bad = (): Obj => {
    cx.issues.push({ message: `expected ${expected(d)}`, path })
    return undefined
  }
  switch (d.kind) {
    case "nat": {
      const i = integer(v, cx.json)
      return i !== null && i >= 0n ? i : bad()
    }
    case "int":
      return integer(v, cx.json) ?? bad()
    case "uint":
    case "sint": {
      const i = inRange(v, d.bits, d.kind === "sint", d.bits === 64, cx.json)
      if (i === null) return bad()
      return d.bits === 64 ? i : Number(BigInt.asUintN(d.bits, i))
    }
    case "usize":
      return inRange(v, WORD_BITS, false, true, cx.json) ?? bad()
    case "isize":
      return inRange(v, 64, true, true, cx.json) ?? bad()
    case "bool":
      return typeof v === "boolean" ? (v ? 1 : 0) : bad()
    case "char":
      return charCode(v) ?? bad()
    case "string":
      return typeof v === "string" && !LONE_SURROGATE.test(v) ? v : bad()
    case "float":
      return floatValue(v, cx.json) ?? bad()
    case "float32": {
      const f = floatValue(v, cx.json)
      return f === null ? bad() : Math.fround(f)
    }
    case "unit":
      return isUnit(v, cx.json) ? 0 : bad()
    case "list": {
      if (!Array.isArray(v)) return bad()
      const items: unknown[] = v
      const encoded = items.map((x, i) => encode(d.item, x, [...path, i], cx))
      let out: Obj = 0
      for (let i = encoded.length - 1; i >= 0; i--) out = lean_ctor(1, 2, 0, 0, encoded[i], out)
      return out
    }
    case "array": {
      if (!Array.isArray(v)) return bad()
      const items: unknown[] = v
      return items.map((x, i) => encode(d.item, x, [...path, i], cx))
    }
    case "option":
      return isAbsent(v, d.absent, cx.json) ? 0 : lean_ctor(1, 1, 0, 0, encode(d.item, v, path, cx))
    case "prod": {
      if (!Array.isArray(v) || v.length !== 2) return bad()
      const pair: unknown[] = v
      return lean_ctor(
        0,
        2,
        0,
        0,
        encode(d.fst, pair[0], [...path, 0], cx),
        encode(d.snd, pair[1], [...path, 1], cx),
      )
    }
    case "except": {
      const ok = record(v, "ok")
      const value = record(v, "value")
      const error = record(v, "error")
      if (ok.value === true && value.found)
        return lean_ctor(1, 1, 0, 0, encode(d.value, value.value, [...path, "value"], cx))
      if (ok.value === false && error.found)
        return lean_ctor(0, 1, 0, 0, encode(d.error, error.value, [...path, "error"], cx))
      if (cx.json && isObject(v) && Object.keys(v).length === 1) {
        if (ok.found) return lean_ctor(1, 1, 0, 0, encode(d.value, ok.value, [...path, "ok"], cx))
        if (error.found)
          return lean_ctor(0, 1, 0, 0, encode(d.error, error.value, [...path, "error"], cx))
      }
      return bad()
    }
    case "fin": {
      const i = integer(v, cx.json)
      return i !== null && i >= 0n && i < d.bound ? i : bad()
    }
    case "struct": {
      if (!isObject(v)) return bad()
      return encodeVariant(d, d.variant, objectInputs(d.variant, v, path), d.trivial, path, cx)
    }
    case "enum": {
      const i = typeof v === "string" ? d.ctors.indexOf(v) : -1
      return i >= 0 ? i : bad()
    }
    case "inductive": {
      const p = pick(d, v, path, cx.json)
      if (p === null) return bad()
      return encodeVariant(d, p.variant, p.inputs, null, path, cx)
    }
    case "subtype": {
      const before = cx.issues.length
      const x = encode(d.base, v, path, cx)
      if (cx.issues.length === before && !d.invariant.decide(x))
        cx.issues.push({ message: `${d.name}.${d.invariant.field}: ${d.invariant.prop}`, path })
      return x
    }
    case "model": {
      const r = runModel(d, v, path, cx.issues)
      return r.ok ? encode(d.struct, r.value, path, { json: true, issues: cx.issues }) : undefined
    }
    case "ref":
      return encode(d.get(), v, path, cx)
  }
  return unreachable(d)
}

function encodeVariant(
  d: { readonly kind: "struct" | "inductive"; readonly name: string },
  variant: VariantDesc,
  inputs: readonly FieldInput[],
  trivial: number | null,
  path: readonly PropertyKey[],
  cx: Ctx,
): Obj {
  const before = cx.issues.length
  const values = variant.fields.map((f, i) => {
    const input = inputs[i]
    return encode(f.desc, input?.value, input?.path ?? path, cx)
  })
  if (cx.issues.length === before)
    checkInvariants(ownerName(d, variant), variant, values, path, cx.issues)
  if (trivial !== null) return values[trivial]
  return build(variant, values)
}

function check(d: TypeDesc, v: unknown, path: readonly PropertyKey[], issues: Issue[]): unknown {
  const bad = (): unknown => {
    issues.push({ message: `expected ${expected(d)}`, path })
    return undefined
  }
  switch (d.kind) {
    case "nat":
    case "int":
    case "usize":
    case "isize":
    case "fin": {
      const before = issues.length
      const x = encode(d, v, path, { json: true, issues })
      if (issues.length !== before) return undefined
      if (d.kind === "fin" && d.bound <= 1n << 32n) return Number(asNat(x))
      return x
    }
    case "uint":
    case "sint": {
      const i = inRange(v, d.bits, d.kind === "sint", d.bits === 64, true)
      if (i === null) return bad()
      return d.bits === 64 ? i : Number(i)
    }
    case "bool":
      return typeof v === "boolean" ? v : bad()
    case "char":
      return charCode(v) === null ? bad() : v
    case "string":
      return typeof v === "string" && !LONE_SURROGATE.test(v) ? v : bad()
    case "float":
      return floatValue(v, true) ?? bad()
    case "float32": {
      const f = floatValue(v, true)
      return f === null ? bad() : Math.fround(f)
    }
    case "unit":
      return isUnit(v, true) ? undefined : bad()
    case "list":
    case "array": {
      if (!Array.isArray(v)) return bad()
      const items: unknown[] = v
      return items.map((x, i) => check(d.item, x, [...path, i], issues))
    }
    case "option":
      if (isAbsent(v, d.absent, true)) return d.absent === "null" ? null : undefined
      return check(d.item, v, path, issues)
    case "prod": {
      if (!Array.isArray(v) || v.length !== 2) return bad()
      const pair: unknown[] = v
      return [
        check(d.fst, pair[0], [...path, 0], issues),
        check(d.snd, pair[1], [...path, 1], issues),
      ]
    }
    case "except": {
      const ok = record(v, "ok")
      const value = record(v, "value")
      const error = record(v, "error")
      if (ok.value === true && value.found)
        return { ok: true, value: check(d.value, value.value, [...path, "value"], issues) }
      if (ok.value === false && error.found)
        return { ok: false, error: check(d.error, error.value, [...path, "error"], issues) }
      if (isObject(v) && Object.keys(v).length === 1) {
        if (ok.found) return { ok: true, value: check(d.value, ok.value, [...path, "ok"], issues) }
        if (error.found)
          return { ok: false, error: check(d.error, error.value, [...path, "error"], issues) }
      }
      return bad()
    }
    case "struct": {
      if (!isObject(v)) return bad()
      return checkVariant(d, d.variant, objectInputs(d.variant, v, path), path, issues, {})
    }
    case "enum":
      return typeof v === "string" && d.ctors.includes(v) ? v : bad()
    case "inductive": {
      const p = pick(d, v, path, true)
      if (p === null) return bad()
      return checkVariant(d, p.variant, p.inputs, path, issues, { [d.tagKey]: p.variant.name })
    }
    case "subtype": {
      const before = issues.length
      const x = check(d.base, v, path, issues)
      if (issues.length === before) {
        const lean = encode(d.base, x, path, { json: false, issues })
        if (issues.length === before && !d.invariant.decide(lean))
          issues.push({ message: `${d.name}.${d.invariant.field}: ${d.invariant.prop}`, path })
      }
      return x
    }
    case "model": {
      const r = runModel(d, v, path, issues)
      return r.value
    }
    case "ref":
      return check(d.get(), v, path, issues)
  }
  return unreachable(d)
}

function checkVariant(
  d: { readonly kind: "struct" | "inductive"; readonly name: string },
  variant: VariantDesc,
  inputs: readonly FieldInput[],
  path: readonly PropertyKey[],
  issues: Issue[],
  head: Readonly<Record<string, unknown>>,
): unknown {
  const before = issues.length
  const outputs = variant.fields.map((f, i) => {
    const input = inputs[i]
    return check(f.desc, input?.value, input?.path ?? path, issues)
  })
  if (issues.length !== before) return undefined
  if (variant.invariants.length !== 0) {
    const values = variant.fields.map((f, i) =>
      encode(f.desc, outputs[i], path, { json: false, issues }),
    )
    if (issues.length !== before) return undefined
    checkInvariants(ownerName(d, variant), variant, values, path, issues)
  }
  return assemble(variant, outputs, head)
}

function assemble(
  variant: VariantDesc,
  outputs: readonly unknown[],
  head: Readonly<Record<string, unknown>>,
): Record<string, unknown> {
  const out: Record<string, unknown> = { ...head }
  variant.fields.forEach((f, i) => {
    const x = outputs[i]
    if (f.flat) Object.assign(out, x)
    else if (x !== undefined || resolve(f.desc).kind !== "option") out[f.key] = x
  })
  return out
}

function decodeVariant(
  variant: VariantDesc,
  x: Obj,
  trivial: number | null,
  head: Readonly<Record<string, unknown>>,
): Record<string, unknown> {
  const outputs = variant.fields.map((f, i) =>
    decode(f.desc, trivial === null ? load(x, f) : i === trivial ? x : 0),
  )
  return assemble(variant, outputs, head)
}

function decode(d: TypeDesc, x: Obj): unknown {
  switch (d.kind) {
    case "nat":
    case "int":
    case "usize":
      return asNat(x)
    case "uint":
      return d.bits === 64 ? asNat(x) : lean_unbox(x)
    case "sint":
      return d.bits === 64
        ? BigInt.asIntN(64, asNat(x))
        : Number(BigInt.asIntN(d.bits, BigInt(lean_unbox(x))))
    case "isize":
      return BigInt.asIntN(64, asNat(x))
    case "bool":
      return lean_unbox(x) !== 0
    case "char":
      return String.fromCodePoint(lean_unbox(x))
    case "string":
      return asString(x)
    case "float":
    case "float32":
      return lean_unbox(x)
    case "unit":
      return undefined
    case "list": {
      const out: unknown[] = []
      let cur = x
      while (lean_tag(cur) === 1) {
        const cell = asCtor(cur)
        out.push(decode(d.item, cell.fields[0]))
        cur = cell.fields[1]
      }
      return out
    }
    case "array":
      return asArray(x).map((e) => decode(d.item, e))
    case "option":
      if (lean_tag(x) === 0) return d.absent === "null" ? null : undefined
      return decode(d.item, asCtor(x).fields[0])
    case "prod": {
      const c = asCtor(x)
      return [decode(d.fst, c.fields[0]), decode(d.snd, c.fields[1])]
    }
    case "except": {
      const c = asCtor(x)
      return c.tag === 1
        ? { ok: true, value: decode(d.value, c.fields[0]) }
        : { ok: false, error: decode(d.error, c.fields[0]) }
    }
    case "fin":
      return d.bound <= 1n << 32n ? Number(asNat(x)) : asNat(x)
    case "struct":
      return decodeVariant(d.variant, x, d.trivial, {})
    case "enum": {
      const cidx = lean_unbox(x)
      const name = d.ctors[cidx]
      if (name === undefined)
        throw new TypeError(`lean-ts runtime: ${d.name} has no constructor ${cidx}`)
      return name
    }
    case "inductive": {
      const tag = lean_tag(x)
      const variant = d.variants.find((v) => v.cidx === tag)
      if (variant === undefined)
        throw new TypeError(`lean-ts runtime: ${d.name} has no constructor ${tag}`)
      return decodeVariant(variant, x, null, { [d.tagKey]: variant.name })
    }
    case "subtype":
      return decode(d.base, x)
    case "model":
      return jsonValue(d.struct, decode(d.struct, x), false)
    case "ref":
      return decode(d.get(), x)
  }
  return unreachable(d)
}

function bigJson(v: unknown, big: boolean): unknown {
  if (typeof v !== "bigint" || big) return v
  return Number.isSafeInteger(Number(v)) ? Number(v) : v.toString()
}

function floatJson(v: unknown): unknown {
  if (typeof v !== "number" || Number.isFinite(v)) return v
  if (Number.isNaN(v)) return "NaN"
  return v > 0 ? "Infinity" : "-Infinity"
}

function variantJson(variant: VariantDesc, v: unknown, big: boolean): Record<string, unknown> {
  const out: Record<string, unknown> = {}
  for (const f of variant.fields) {
    if (f.flat) {
      Object.assign(out, jsonValue(f.desc, v, big))
      continue
    }
    const x = record(v, f.key).value
    const none = resolve(f.desc).kind === "option" && (x === null || x === undefined)
    if (none && f.omitNone) continue
    out[f.key] = jsonValue(f.desc, x, big)
  }
  return out
}

export function jsonValue(d: TypeDesc, v: unknown, big: boolean): unknown {
  switch (d.kind) {
    case "nat":
    case "int":
    case "isize":
    case "fin":
      return bigJson(v, big)
    case "sint":
      return d.bits === 64 ? bigJson(v, big) : v
    case "uint":
      return d.bits === 64 && typeof v === "bigint" ? v.toString() : v
    case "usize":
      return typeof v === "bigint" ? v.toString() : v
    case "bool":
    case "char":
    case "string":
    case "enum":
      return v
    case "float":
    case "float32":
      return floatJson(v)
    case "unit":
      return {}
    case "list":
    case "array":
      return Array.isArray(v) ? v.map((x: unknown) => jsonValue(d.item, x, big)) : v
    case "option":
      return v === null || v === undefined ? null : jsonValue(d.item, v, big)
    case "prod":
      return Array.isArray(v) ? [jsonValue(d.fst, v[0], big), jsonValue(d.snd, v[1], big)] : v
    case "except":
      return record(v, "ok").value === true
        ? { ok: jsonValue(d.value, record(v, "value").value, big) }
        : { error: jsonValue(d.error, record(v, "error").value, big) }
    case "struct":
      return variantJson(d.variant, v, big)
    case "inductive": {
      const tag = record(v, d.tagKey).value
      const variant = d.variants.find((x) => x.name === tag)
      if (variant === undefined) return v
      if (variant.fields.length === 0) return variant.name
      if (!variant.positional) return { [variant.name]: variantJson(variant, v, big) }
      const items = variant.fields.map((f) => jsonValue(f.desc, record(v, f.key).value, big))
      return { [variant.name]: items.length === 1 ? items[0] : items }
    }
    case "subtype":
      return jsonValue(d.base, v, big)
    case "model":
      return jsonValue(d.struct, v, big)
    case "ref":
      return jsonValue(d.get(), v, big)
  }
  return unreachable(d)
}

export type Checked<T> = { readonly value: T } | { readonly issues: readonly Issue[] }

export function checkValue<T>(d: TypeDesc<T>, v: unknown): Checked<T>
export function checkValue(d: TypeDesc, v: unknown): Checked<unknown> {
  const issues: Issue[] = []
  const value = check(d, v, [], issues)
  return issues.length === 0 ? { value } : { issues }
}

export function toLean(d: TypeDesc, v: unknown, name: string): Obj {
  const issues: Issue[] = []
  const out = encode(d, v, [name], { json: false, issues })
  if (issues.length > 0) throw new LeanValidationError(issues)
  return out
}

export function toTs<T>(d: TypeDesc<T>, x: Obj): T
export function toTs(d: TypeDesc, x: Obj): unknown {
  return decode(d, x)
}

export function ioResult<T>(d: TypeDesc<T>, r: Obj): T
export function ioResult(d: TypeDesc, r: Obj): unknown {
  if (!lean_io_result_is_ok(r)) throw new LeanIOError(lean_io_result_get_error(r))
  return decode(d, lean_io_result_get_value(r))
}

export function lazy(f: () => Obj): () => Obj {
  let done = false
  let value: Obj
  return () => {
    if (!done) {
      value = f()
      done = true
    }
    return value
  }
}
