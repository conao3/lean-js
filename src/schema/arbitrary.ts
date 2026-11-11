import type * as FastCheck from "fast-check"
import {
  checkValue,
  resolve,
  type FieldDesc,
  type TypeDesc,
  type VariantDesc,
} from "../runtime/marshal.ts"

export type FC = typeof FastCheck

const MAX_DEPTH = 3

function bound(f: FieldDesc, key: string): bigint | undefined {
  const v = f.bounds[key]
  return v === undefined ? undefined : BigInt(v)
}

function intRange(
  fc: FC,
  lo: bigint | undefined,
  hi: bigint | undefined,
): FastCheck.Arbitrary<bigint> {
  if (lo !== undefined && hi !== undefined) return fc.bigInt({ min: lo, max: hi })
  if (lo !== undefined) return fc.bigInt({ min: lo, max: lo + 2n ** 64n })
  if (hi !== undefined) return fc.bigInt({ min: hi - 2n ** 64n, max: hi })
  return fc.bigInt()
}

function fieldArb(fc: FC, f: FieldDesc, depth: number): FastCheck.Arbitrary<unknown> {
  const d = resolve(f.desc)
  if (d.kind === "nat" || d.kind === "int") {
    const exMin = bound(f, "exclusiveMinimum")
    const exMax = bound(f, "exclusiveMaximum")
    const lo = bound(f, "minimum") ?? (exMin === undefined ? undefined : exMin + 1n)
    const hi = bound(f, "maximum") ?? (exMax === undefined ? undefined : exMax - 1n)
    return intRange(fc, d.kind === "nat" && (lo === undefined || lo < 0n) ? 0n : lo, hi)
  }
  return gen(fc, f.desc, depth)
}

function variantArb(
  fc: FC,
  v: VariantDesc,
  depth: number,
  head: Readonly<Record<string, unknown>>,
): FastCheck.Arbitrary<Record<string, unknown>> {
  const parts = v.fields.map((f) => fieldArb(fc, f, depth).map((x): [FieldDesc, unknown] => [f, x]))
  return fc.tuple(...parts).map((xs) => {
    const out: Record<string, unknown> = { ...head }
    for (const [f, x] of xs) {
      if (f.flat && typeof x === "object" && x !== null) Object.assign(out, x)
      else if (!(x === undefined && f.omitNone)) out[f.key] = x
    }
    return out
  })
}

function weight(v: VariantDesc): number {
  return v.fields.filter((f) => {
    const k = resolve(f.desc).kind
    return k === "struct" || k === "inductive" || k === "list" || k === "array"
  }).length
}

function gen(fc: FC, desc: TypeDesc, depth: number): FastCheck.Arbitrary<unknown> {
  const d = resolve(desc)
  switch (d.kind) {
    case "nat":
      return fc.bigInt({ min: 0n, max: 2n ** 64n })
    case "int":
      return fc.bigInt({ min: -(2n ** 64n), max: 2n ** 64n })
    case "bool":
      return fc.boolean()
    case "char":
      return fc
        .integer({ min: 0x20, max: 0x10ffff })
        .filter((c) => c < 0xd800 || c > 0xdfff)
        .map((c) => String.fromCodePoint(c))
    case "string":
      return fc.string({ unit: "grapheme", maxLength: 12 })
    case "float":
    case "float32":
      return fc.double({ noNaN: true })
    case "unit":
      return fc.constant(undefined)
    case "uint":
      return d.bits === 64
        ? fc.bigInt({ min: 0n, max: 2n ** 64n - 1n })
        : fc.integer({ min: 0, max: 2 ** d.bits - 1 })
    case "sint":
      return d.bits === 64
        ? fc.bigInt({ min: -(2n ** 63n), max: 2n ** 63n - 1n })
        : fc.integer({ min: -(2 ** (d.bits - 1)), max: 2 ** (d.bits - 1) - 1 })
    case "usize":
      return fc.bigInt({ min: 0n, max: 2n ** 64n - 1n })
    case "isize":
      return fc.bigInt({ min: -(2n ** 63n), max: 2n ** 63n - 1n })
    case "list":
    case "array":
      return fc.array(gen(fc, d.item, depth - 1), { maxLength: depth > 0 ? 8 : 0 })
    case "option": {
      const nil = d.absent === "null" ? null : undefined
      return fc.option(gen(fc, d.item, depth), { nil })
    }
    case "prod":
      return fc.tuple(gen(fc, d.fst, depth), gen(fc, d.snd, depth))
    case "except":
      return fc.oneof(
        gen(fc, d.error, depth).map((error) => ({ ok: false, error })),
        gen(fc, d.value, depth).map((value) => ({ ok: true, value })),
      )
    case "fin": {
      const big = fc.bigInt({ min: 0n, max: d.bound - 1n })
      return d.bound <= 2n ** 32n ? big.map(Number) : big
    }
    case "struct":
      return variantArb(fc, d.variant, depth - 1, {})
    case "enum":
      return fc.constantFrom(...d.ctors)
    case "inductive": {
      const vs = depth > 0 ? d.variants : d.variants.filter((v) => weight(v) === 0)
      const pool = vs.length === 0 ? d.variants : vs
      return fc.oneof(...pool.map((v) => variantArb(fc, v, depth - 1, { [d.tagKey]: v.name })))
    }
    case "subtype":
      return gen(fc, d.base, depth)
    case "model":
      throw new TypeError(`lean-ts: no arbitrary for the user schema ${d.name}`)
    default:
      return gen(fc, d.get(), depth)
  }
}

export function arbitrary<T>(
  schema: { readonly desc: TypeDesc<T> } | TypeDesc<T>,
  fc: FC,
): FastCheck.Arbitrary<T> {
  const desc: TypeDesc<T> = "desc" in schema ? schema.desc : schema
  return gen(fc, desc, MAX_DEPTH)
    .map((v) => checkValue(desc, v))
    .filter((r): r is { readonly value: T } => "value" in r)
    .map((r) => r.value)
}
