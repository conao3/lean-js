export interface BlockSettings {
  readonly tagKey: string
  readonly option: string
}

export interface BlockEntry {
  readonly name: string
  readonly module: string
  readonly fnv: string
  readonly settings: BlockSettings
  readonly url: string
}

export interface RecordedBlock {
  readonly name: string
  readonly source: string
  readonly options: unknown
}

export interface BlockRegistry {
  readonly brand: "lean-ts.blocks"
  readonly blocks: Map<string, BlockEntry[]>
  readonly models: Map<string, unknown>
  recording: RecordedBlock[] | null
}

const KEY: unique symbol = Symbol.for("lean-ts.blocks")

function isRegistry(x: unknown): x is BlockRegistry {
  return typeof x === "object" && x !== null && Reflect.get(x, "brand") === "lean-ts.blocks"
}

export function blockRegistry(): BlockRegistry {
  const existing: unknown = Reflect.get(globalThis, KEY)
  if (isRegistry(existing)) return existing
  const created: BlockRegistry = {
    brand: "lean-ts.blocks",
    blocks: new Map(),
    models: new Map(),
    recording: null,
  }
  Reflect.set(globalThis, KEY, created)
  return created
}

export function registerBlock(entry: BlockEntry): void {
  const blocks = blockRegistry().blocks
  const list = blocks.get(entry.name)
  if (list === undefined) blocks.set(entry.name, [entry])
  else list.push(entry)
}

export function leanName<F extends object>(fn: F, name: string): F {
  Object.defineProperty(fn, "__leanName", { value: name })
  return fn
}

export function leanNameOf(fn: unknown): string | undefined {
  const n: unknown = typeof fn === "function" ? Reflect.get(fn, "__leanName") : undefined
  return typeof n === "string" ? n : undefined
}

export type Numbers<T> = T extends bigint
  ? number
  : T extends readonly [infer A, infer B]
    ? [Numbers<A>, Numbers<B>]
    : T extends readonly (infer U)[]
      ? Numbers<U>[]
      : T

export function tsNumbers<T>(v: T): Numbers<T>
export function tsNumbers(v: unknown): unknown {
  if (typeof v === "bigint") return Number(v)
  if (Array.isArray(v)) return v.map((x: unknown) => tsNumbers(x))
  return v
}
