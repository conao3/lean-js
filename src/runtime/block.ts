export interface BlockEntry {
  readonly name: string
  readonly module: string
  readonly fnv: string
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
