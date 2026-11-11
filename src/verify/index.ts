import { dirname } from "node:path"
import { pathToFileURL } from "node:url"
import type * as FastCheck from "fast-check"
import { leanNameOf } from "../runtime/block.ts"
import type { TypeDesc } from "../runtime/marshal.ts"
import { arbitrary, type FC } from "../schema/arbitrary.ts"
import { readSource } from "./check.ts"
import { BIG, Fn, type TsType, type TypeResolver } from "./translate.ts"

export type Spec = (...args: never[]) => unknown

export interface ModelOptions {
  readonly refines?: Spec
  readonly requires?: Spec
  readonly ensures?: Readonly<Record<string, Spec>>
}

export interface ModelEntry {
  readonly fn: Spec
  readonly name: string
  readonly options: ModelOptions
  readonly file: string | undefined
}

const KEY: unique symbol = Symbol.for("lean-ts.models")

interface ModelRegistry {
  readonly brand: "lean-ts.models"
  readonly models: Map<Spec, ModelEntry>
}

function isRegistry(x: unknown): x is ModelRegistry {
  return typeof x === "object" && x !== null && Reflect.get(x, "brand") === "lean-ts.models"
}

export function modelRegistry(): Map<Spec, ModelEntry> {
  const existing: unknown = Reflect.get(globalThis, KEY)
  if (isRegistry(existing)) return existing.models
  const created: ModelRegistry = { brand: "lean-ts.models", models: new Map() }
  Reflect.set(globalThis, KEY, created)
  return created.models
}

function callerFile(): string | undefined {
  const holder: { stack?: string } = {}
  Error.captureStackTrace(holder, model)
  for (const line of (holder.stack ?? "").split("\n").slice(1)) {
    const m = /\(?((?:file:\/\/)?\/[^():]+\.[cm]?[tj]sx?)(?:\?[^:]*)?:\d+:\d+\)?\s*$/u.exec(line)
    const f = m?.[1]
    if (f !== undefined)
      return f.startsWith("file://") ? decodeURIComponent(new URL(f).pathname) : f
  }
  return undefined
}

function checkSpec(fnName: string, label: string, s: unknown): void {
  if (typeof s !== "function" || leanNameOf(s) === undefined)
    throw new TypeError(
      `lean-ts: the ${label} specification of ${fnName} is not a function of a lean(...) block`,
    )
}

export function model<F extends Spec>(fn: F, options: ModelOptions): F {
  modelRegistry().set(fn, { fn, name: fn.name, options, file: callerFile() })
  return fn
}

export class PropertyFailure extends Error {
  constructor(message: string, cause?: unknown) {
    super(message, cause === undefined ? undefined : { cause })
    this.name = "PropertyFailure"
  }
}

export interface CheckOptions {
  readonly numRuns?: number
  readonly seed?: number
  readonly range?: { readonly min: bigint; readonly max: bigint }
}

const SAFE = BigInt(Number.MAX_SAFE_INTEGER)

function show(v: unknown): string {
  return (
    JSON.stringify(v, (_k, x: unknown) =>
      typeof x === "bigint" ? `${x}n` : x === undefined ? null : x,
    ) ?? "undefined"
  )
}

function normal(v: unknown): unknown {
  if (typeof v === "number" && Number.isInteger(v)) return BigInt(v)
  if (v === undefined) return null
  if (Array.isArray(v)) return v.map(normal)
  if (typeof v === "object" && v !== null)
    return Object.fromEntries(
      Object.entries(v)
        .filter(([, x]) => x !== undefined)
        .toSorted(([a], [b]) => a.localeCompare(b))
        .map(([k, x]) => [k, normal(x)]),
    )
  return v
}

function unsafeNumber(v: unknown): boolean {
  if (typeof v === "number") return !Number.isSafeInteger(v)
  if (Array.isArray(v)) return v.some(unsafeNumber)
  if (typeof v === "object" && v !== null) return Object.values(v).some(unsafeNumber)
  return false
}

function isTypeDesc(d: unknown): d is TypeDesc {
  return typeof d === "object" && d !== null && typeof Reflect.get(d, "kind") === "string"
}

async function loadFastCheck(): Promise<FC> {
  try {
    return await import("fast-check")
  } catch (e) {
    throw new TypeError("lean-ts: checkModel needs the optional peer dependency fast-check", {
      cause: e,
    })
  }
}

async function paramTypes(entry: ModelEntry): Promise<{ fn: Fn; descs: Map<string, TypeDesc> }> {
  const file = entry.file
  if (file === undefined)
    throw new TypeError(`lean-ts: the source file of the model call of ${entry.name} is unknown`)
  const src = readSource(dirname(file), file)
  const node = src.fns.get(entry.name)
  if (node === undefined)
    throw new TypeError(`lean-ts: ${entry.name} is not a function declaration of ${file}`)
  const modules = new Map<string, unknown>()
  for (const i of src.imports.values())
    if (i.from.startsWith("/") && !modules.has(i.from))
      modules.set(
        i.from,
        await import(pathToFileURL(i.from.endsWith(".ts") ? i.from : `${i.from}.ts`).href),
      )
  const descs = new Map<string, TypeDesc>()
  const types: TypeResolver = {
    reference(name, qualifier, at) {
      const i = src.imports.get(qualifier ?? name)
      if (i === undefined) return undefined
      const exportName =
        qualifier === undefined ? i.exportName : i.exportName === null ? name : null
      if (exportName === null) return undefined
      if (i.from === "lean-ts/schema" && (exportName === "Nat" || exportName === "Int")) return BIG
      const m = modules.get(i.from)
      const v: unknown =
        typeof m === "object" && m !== null ? Reflect.get(m, exportName) : undefined
      const d: unknown =
        (typeof v === "object" && v !== null) || typeof v === "function"
          ? Reflect.get(v, "desc")
          : undefined
      if (!isTypeDesc(d))
        throw new TypeError(`lean-ts: ${src.where(at)}: ${exportName} is not a lean-ts schema`)
      const key = `${i.from}#${exportName}`
      descs.set(key, d)
      return { k: "struct", lean: key, ts: exportName, fields: [] }
    },
  }
  return { fn: new Fn(entry.name, node, src, types), descs }
}

function arbOf(
  fc: FC,
  t: TsType,
  nat: boolean,
  descs: ReadonlyMap<string, TypeDesc>,
  options: CheckOptions,
): FastCheck.Arbitrary<unknown> {
  const lo = options.range?.min
  const hi = options.range?.max
  switch (t.k) {
    case "num": {
      const min = lo === undefined ? -SAFE : lo < -SAFE ? -SAFE : lo
      const max = hi === undefined ? SAFE : hi > SAFE ? SAFE : hi
      return fc.bigInt({ min: nat && min < 0n ? 0n : min, max }).map(Number)
    }
    case "big":
      return fc.bigInt({
        min: nat && (lo === undefined || lo < 0n) ? 0n : (lo ?? -(2n ** 64n)),
        max: hi ?? 2n ** 64n,
      })
    case "bool":
      return fc.boolean()
    case "str":
      return fc.string({ unit: "grapheme", maxLength: 12 })
    case "list":
      return fc.array(arbOf(fc, t.item, false, descs, options), { maxLength: 10 })
    case "tuple":
      return fc.tuple(...t.items.map((x) => arbOf(fc, x, false, descs, options)))
    case "opt":
      return fc.option(arbOf(fc, t.item, false, descs, options), {
        nil: t.absent === "null" ? null : undefined,
      })
    default: {
      const d = descs.get(t.lean)
      if (d === undefined) throw new TypeError(`lean-ts: no descriptor for ${t.ts}`)
      return arbitrary(d, fc)
    }
  }
}

export async function checkModel(fn: Spec, options: CheckOptions = {}): Promise<void> {
  const entry = modelRegistry().get(fn)
  if (entry === undefined) throw new TypeError(`lean-ts: ${fn.name} has no model(...) call`)
  const fc: FC = await loadFastCheck()
  const { fn: sig, descs } = await paramTypes(entry)
  const arbs = sig.params.map((p) => arbOf(fc, p.type, p.nat, descs, options))
  const { refines, requires, ensures } = entry.options
  const name = entry.name
  if (refines !== undefined) checkSpec(name, "refines", refines)
  if (requires !== undefined) checkSpec(name, "requires", requires)
  for (const [label, s] of Object.entries(ensures ?? {})) checkSpec(name, label, s)
  const property = fc.property(fc.tuple(...arbs), (args: unknown[]) => {
    if (requires !== undefined) fc.pre(Reflect.apply(requires, undefined, args) === true)
    let result: unknown
    try {
      result = Reflect.apply(fn, undefined, args)
    } catch (e) {
      throw new PropertyFailure(
        `${name}${show(args)} raised ${e instanceof Error ? `${e.name}: ${e.message}` : String(e)}`,
      )
    }
    fc.pre(!unsafeNumber(result))
    if (refines !== undefined) {
      const expected: unknown = Reflect.apply(refines, undefined, args)
      if (show(normal(result)) !== show(normal(expected)))
        throw new PropertyFailure(
          `${name}${show(args)} = ${show(result)}, the spec gives ${show(expected)}`,
        )
    }
    for (const [label, e] of Object.entries(ensures ?? {}))
      if (Reflect.apply(e, undefined, [...args, result]) !== true)
        throw new PropertyFailure(`${name}${show(args)} = ${show(result)} breaks ${label}`)
    return true
  })
  try {
    fc.assert(property, {
      numRuns: options.numRuns ?? 200,
      ...(options.seed === undefined ? {} : { seed: options.seed }),
    })
  } catch (e) {
    if (e instanceof Error) {
      const c: unknown = e.cause
      throw new PropertyFailure(c instanceof Error ? `${e.message}\n${c.message}` : e.message, e)
    }
    throw e
  }
}

export async function checkModule(
  module: Readonly<Record<string, unknown>>,
  options: CheckOptions = {},
): Promise<void> {
  const values = new Set(Object.values(module))
  const entries = [...modelRegistry().values()].filter((e) => values.has(e.fn))
  if (entries.length === 0) throw new TypeError("lean-ts: the module has no model(...) functions")
  for (const entry of entries) await checkModel(entry.fn, options)
}
