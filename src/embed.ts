import type { StandardJSONSchemaV1, StandardSchemaV1 } from "@standard-schema/spec"
import { canonicalJson, fnv1a64, type Json, toJson } from "./key.ts"
import { type BlockEntry, blockRegistry } from "./runtime/block.ts"

export const GENERATOR_VERSION: string = "3"

export type LeanModel = StandardSchemaV1 & StandardJSONSchemaV1

export interface OutputOptions {
  readonly tagKey?: string
  readonly option?: "null" | "undefined"
}

export interface LeanBlockOptions {
  readonly imports?: readonly string[]
  readonly uses?: readonly string[]
  readonly models?: Readonly<Record<string, LeanModel>>
  readonly output?: OutputOptions
}

export interface LeanBlock {
  readonly name: string
  readonly key: string
  readonly models: Readonly<Record<string, LeanModel>>
}

export class LeanBlockStale extends Error {
  constructor(message: string) {
    super(message)
    this.name = "LeanBlockStale"
  }
}

export interface BlockInputs {
  readonly name: string
  readonly source: string
  readonly imports: readonly string[]
  readonly uses: readonly string[]
  readonly models: Readonly<Record<string, Json>>
  readonly output: OutputOptions
}

function stringList(v: unknown, where: string): readonly string[] {
  if (v === undefined) return []
  if (!Array.isArray(v) || !v.every((x: unknown) => typeof x === "string"))
    throw new TypeError(`lean(): ${where} must be an array of strings`)
  return v
}

function isRecord(v: unknown): v is Readonly<Record<string, unknown>> {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

export function modelSchema(name: string, model: unknown): Json {
  const std: unknown = isRecord(model) ? model["~standard"] : undefined
  const converter: unknown = isRecord(std) ? std["jsonSchema"] : undefined
  const output: unknown = isRecord(converter) ? converter["output"] : undefined
  if (typeof output !== "function")
    throw new TypeError(
      `lean(): the model ${name} is not a Standard JSON Schema (no ~standard.jsonSchema.output)`,
    )
  const schema: unknown = Reflect.apply(output, converter, [{ target: "draft-2020-12" }])
  return toJson(schema, `the JSON Schema of the model ${name}`)
}

function outputOptions(v: unknown): OutputOptions {
  if (v === undefined) return {}
  if (!isRecord(v)) throw new TypeError("lean(): options.output must be an object")
  const out: { tagKey?: string; option?: "null" | "undefined" } = {}
  const { tagKey, option } = v
  if (tagKey !== undefined) {
    if (typeof tagKey !== "string") throw new TypeError("lean(): output.tagKey must be a string")
    out.tagKey = tagKey
  }
  if (option !== undefined) {
    if (option !== "null" && option !== "undefined")
      throw new TypeError('lean(): output.option must be "null" or "undefined"')
    out.option = option
  }
  return out
}

export function blockInputs(name: unknown, source: unknown, options: unknown): BlockInputs {
  if (typeof name !== "string") throw new TypeError("lean(): the block name must be a string")
  if (typeof source !== "string") throw new TypeError("lean(): the Lean source must be a string")
  if (options !== undefined && !isRecord(options))
    throw new TypeError("lean(): options must be an object")
  const o = options ?? {}
  const models: Record<string, Json> = {}
  if (o["models"] !== undefined) {
    if (!isRecord(o["models"])) throw new TypeError("lean(): options.models must be an object")
    for (const [k, m] of Object.entries(o["models"])) models[k] = modelSchema(k, m)
  }
  return {
    name,
    source,
    imports: stringList(o["imports"], "options.imports"),
    uses: stringList(o["uses"], "options.uses"),
    models,
    output: outputOptions(o["output"]),
  }
}

export function blockContent(b: BlockInputs): Json {
  return toJson(
    {
      name: b.name,
      source: b.source,
      imports: b.imports,
      uses: b.uses,
      models: b.models,
      output: b.output,
      generator: GENERATOR_VERSION,
    },
    "block",
  )
}

export function blockFnv(b: BlockInputs): string {
  return fnv1a64(canonicalJson(blockContent(b)))
}

function nodeProcess(): NodeJS.Process | undefined {
  return typeof process !== "undefined" && typeof process.getBuiltinModule === "function"
    ? process
    : undefined
}

function packageRoot(proc: NodeJS.Process, entries: readonly BlockEntry[]): string {
  const fs = proc.getBuiltinModule("node:fs")
  const path = proc.getBuiltinModule("node:path")
  const url = proc.getBuiltinModule("node:url")
  const first = entries[0]
  let dir = first === undefined ? proc.cwd() : path.dirname(url.fileURLToPath(first.url))
  for (;;) {
    if (fs.existsSync(path.join(dir, "package.json"))) return dir
    const up = path.dirname(dir)
    if (up === dir) throw new LeanBlockStale(`lean-ts: no package.json above ${dir}`)
    dir = up
  }
}

function autoSync(proc: NodeJS.Process, name: string, entries: readonly BlockEntry[]): boolean {
  if (proc.env["LEAN_TS_AUTO_SYNC"] !== "1") return false
  const root = packageRoot(proc, entries)
  const cli = proc
    .getBuiltinModule("node:url")
    .fileURLToPath(
      new URL(import.meta.url.endsWith(".ts") ? "./cli.ts" : "./cli.js", import.meta.url),
    )
  const r = proc
    .getBuiltinModule("node:child_process")
    .spawnSync(proc.execPath, [cli, "sync", "--package", root], {
      stdio: "inherit",
      env: { ...proc.env, LEAN_TS_AUTO_SYNC: "0" },
    })
  if (r.status !== 0)
    throw new LeanBlockStale(
      `lean-ts: \`lean-ts sync --package ${root}\` failed (exit ${r.status})`,
    )
  proc.stderr.write(
    `lean-ts: regenerated the Lean block ${JSON.stringify(name)} of ${root}; the generated module takes effect when the program starts again\n`,
  )
  return true
}

export function lean(name: string, source: string, options?: LeanBlockOptions): LeanBlock {
  const registry = blockRegistry()
  const models = options?.models ?? {}
  if (registry.recording !== null) {
    registry.recording.push({ name, source, options })
    return { name, key: "", models }
  }
  const fnv = blockFnv(blockInputs(name, source, options))
  for (const [k, m] of Object.entries(models)) registry.models.set(`${fnv}:${k}`, m)
  const entries = registry.blocks.get(name) ?? []
  if (entries.some((e) => e.fnv === fnv)) return { name, key: fnv, models }
  const proc = nodeProcess()
  if (proc !== undefined && autoSync(proc, name, entries)) return { name, key: fnv, models }
  const where =
    entries.length === 0
      ? "its generated module was not imported"
      : "it has changed since `lean-ts sync` generated it"
  throw new LeanBlockStale(
    `the Lean block ${JSON.stringify(name)} is stale (${where}); run \`lean-ts sync\` (or set LEAN_TS_AUTO_SYNC=1)`,
  )
}
