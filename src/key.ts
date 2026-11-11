export type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [k: string]: Json }

function isJsonObject(v: unknown): v is { readonly [k: string]: unknown } {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

export function toJson(v: unknown, where: string): Json {
  if (v === null || typeof v === "boolean" || typeof v === "string") return v
  if (typeof v === "number") {
    if (!Number.isFinite(v)) throw new TypeError(`${where}: ${v} is not a JSON number`)
    return v
  }
  if (Array.isArray(v)) return v.map((x: unknown, i) => toJson(x, `${where}[${i}]`))
  if (isJsonObject(v)) {
    const out: Record<string, Json> = {}
    for (const k of Object.keys(v).toSorted()) {
      const x = v[k]
      if (x !== undefined) out[k] = toJson(x, `${where}.${k}`)
    }
    return out
  }
  throw new TypeError(`${where}: ${typeof v} is not a JSON value`)
}

export function canonicalJson(v: unknown): string {
  return JSON.stringify(toJson(v, "value"))
}

const FNV_OFFSET = 0xcbf29ce484222325n
const FNV_PRIME = 0x100000001b3n

export function fnv1a64(s: string): string {
  let h = FNV_OFFSET
  for (const b of new TextEncoder().encode(s)) {
    h = BigInt.asUintN(64, (h ^ BigInt(b)) * FNV_PRIME)
  }
  return h.toString(16).padStart(16, "0")
}
