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
  lean_ctor,
  lean_tag,
  lean_unbox,
  type Obj,
} from "./object.ts"
import { WORD_BITS } from "./uint.ts"

export type DescNode =
  | { readonly kind: "nat" | "int" | "bool" | "char" | "string" | "float" | "float32" | "unit" }
  | { readonly kind: "uint" | "sint"; readonly bits: 8 | 16 | 32 | 64 }
  | { readonly kind: "usize" | "isize" }
  | { readonly kind: "list" | "array" | "option"; readonly item: TypeDesc }
  | { readonly kind: "prod"; readonly fst: TypeDesc; readonly snd: TypeDesc }
  | { readonly kind: "except"; readonly error: TypeDesc; readonly value: TypeDesc }

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

export function optionDesc<T>(item: TypeDesc<T>): TypeDesc<T | null> {
  return { kind: "option", item }
}

export function prodDesc<A, B>(fst: TypeDesc<A>, snd: TypeDesc<B>): TypeDesc<readonly [A, B]> {
  return { kind: "prod", fst, snd }
}

export function exceptDesc<E, A>(error: TypeDesc<E>, value: TypeDesc<A>): TypeDesc<Except<E, A>> {
  return { kind: "except", error, value }
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

function unreachable(d: never): never {
  throw new TypeError(`lean-ts runtime: unknown type descriptor ${JSON.stringify(d)}`)
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
      return "a value or null"
    case "prod":
      return "an array of two elements"
    case "except":
      return "an object { ok: true, value } or { ok: false, error }"
  }
  return unreachable(d)
}

function integer(v: unknown): bigint | null {
  if (typeof v === "bigint") return v
  if (typeof v === "number" && Number.isSafeInteger(v)) return BigInt(v)
  return null
}

function inRange(v: unknown, bits: number, signed: boolean, big: boolean): bigint | null {
  const i = big
    ? typeof v === "bigint"
      ? v
      : null
    : typeof v === "number" && Number.isInteger(v)
      ? BigInt(v)
      : null
  if (i === null) return null
  const n = BigInt(bits)
  const lo = signed ? -(1n << (n - 1n)) : 0n
  const hi = signed ? 1n << (n - 1n) : 1n << n
  return i >= lo && i < hi ? i : null
}

function record(v: unknown, key: string): { readonly found: boolean; readonly value: unknown } {
  if (typeof v !== "object" || v === null || !Object.hasOwn(v, key))
    return { found: false, value: undefined }
  return { found: true, value: Reflect.get(v, key) }
}

function encode(d: TypeDesc, v: unknown, path: readonly PropertyKey[], issues: Issue[]): Obj {
  const bad = (): Obj => {
    issues.push({ message: `expected ${expected(d)}`, path })
    return undefined
  }
  switch (d.kind) {
    case "nat": {
      const i = integer(v)
      return i !== null && i >= 0n ? i : bad()
    }
    case "int":
      return integer(v) ?? bad()
    case "uint":
    case "sint": {
      const i = inRange(v, d.bits, d.kind === "sint", d.bits === 64)
      if (i === null) return bad()
      return d.bits === 64 ? i : Number(BigInt.asUintN(d.bits, i))
    }
    case "usize":
      return inRange(v, WORD_BITS, false, true) ?? bad()
    case "isize":
      return inRange(v, 64, true, true) ?? bad()
    case "bool":
      return typeof v === "boolean" ? (v ? 1 : 0) : bad()
    case "char": {
      if (typeof v !== "string") return bad()
      const cp = v.codePointAt(0)
      if (cp === undefined || String.fromCodePoint(cp) !== v || (cp >= 0xd800 && cp <= 0xdfff))
        return bad()
      return cp
    }
    case "string":
      return typeof v === "string" && !LONE_SURROGATE.test(v) ? v : bad()
    case "float":
      return typeof v === "number" ? v : bad()
    case "float32":
      return typeof v === "number" ? Math.fround(v) : bad()
    case "unit":
      return v === undefined ? 0 : bad()
    case "list": {
      if (!Array.isArray(v)) return bad()
      const items: unknown[] = v
      const encoded = items.map((x, i) => encode(d.item, x, [...path, i], issues))
      let out: Obj = 0
      for (let i = encoded.length - 1; i >= 0; i--) out = lean_ctor(1, 2, 0, 0, encoded[i], out)
      return out
    }
    case "array": {
      if (!Array.isArray(v)) return bad()
      const items: unknown[] = v
      return items.map((x, i) => encode(d.item, x, [...path, i], issues))
    }
    case "option":
      return v === null ? 0 : lean_ctor(1, 1, 0, 0, encode(d.item, v, path, issues))
    case "prod": {
      if (!Array.isArray(v) || v.length !== 2) return bad()
      const pair: unknown[] = v
      return lean_ctor(
        0,
        2,
        0,
        0,
        encode(d.fst, pair[0], [...path, 0], issues),
        encode(d.snd, pair[1], [...path, 1], issues),
      )
    }
    case "except": {
      const ok = record(v, "ok")
      if (ok.value === true) {
        const value = record(v, "value")
        if (!value.found) return bad()
        return lean_ctor(1, 1, 0, 0, encode(d.value, value.value, [...path, "value"], issues))
      }
      if (ok.value === false) {
        const error = record(v, "error")
        if (!error.found) return bad()
        return lean_ctor(0, 1, 0, 0, encode(d.error, error.value, [...path, "error"], issues))
      }
      return bad()
    }
  }
  return unreachable(d)
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
      return lean_tag(x) === 0 ? null : decode(d.item, asCtor(x).fields[0])
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
  }
  return unreachable(d)
}

export function toLean(d: TypeDesc, v: unknown, name: string): Obj {
  const issues: Issue[] = []
  const out = encode(d, v, [name], issues)
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
