import { spawnSync } from "node:child_process"
import { createHash } from "node:crypto"
import {
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  rmdirSync,
  writeFileSync,
} from "node:fs"
import { basename, dirname, join, relative, resolve, sep } from "node:path"
import { pathToFileURL } from "node:url"
import {
  type BlockInputs,
  blockContent,
  blockFnv,
  blockInputs,
  GENERATOR_VERSION,
  modelSchema,
} from "./embed.ts"
import { canonicalJson, type Json } from "./key.ts"
import { modelsLean } from "./models.ts"
import { blockRegistry, type RecordedBlock } from "./runtime/block.ts"
import { posixRelative, type ScannedBlock, scanFile, SyncError, tsFiles } from "./scan.ts"

export { SyncError }

const LAKEFILE = `name = "lean-ts-workspace"
defaultTargets = ["LeanTsModels", "LeanTsEmbed", "LeanTsCsimp"]

[[lean_lib]]
name = "LeanTsModels"

[[lean_lib]]
name = "LeanTsEmbed"

[[lean_lib]]
name = "LeanTsCsimp"
`

const DEFAULT_SETTINGS: Readonly<Record<string, string>> = { tagKey: "ctor", option: "null" }

const TAG_KEY = /^[A-Za-z_$][A-Za-z0-9_$]*$/u

const BLOCK_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u

const LAKE_MESSAGE =
  /^(error|warning): (?:\.\/)*(LeanTs(?:Embed|Models)\/[^:]+\.lean):(\d+):(\d+): (.*)$/u

export interface Block extends ScannedBlock {
  readonly leanModule: readonly string[]
  readonly outFile: string
  readonly settings: Readonly<Record<string, string>>
  readonly inputs: BlockInputs
  readonly fnv: string
  readonly key: string
}

export interface Package {
  readonly root: string
  readonly config: Readonly<Record<string, string>>
  readonly blocks: readonly Block[]
}

export type Log = (line: string) => void

function readJson(file: string): unknown {
  return JSON.parse(readFileSync(file, "utf8"))
}

export function isRecord(v: unknown): v is Readonly<Record<string, unknown>> {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

function checkSettings(
  settings: Readonly<Record<string, unknown>>,
  where: string,
): Record<string, string> {
  const out: Record<string, string> = {}
  for (const [k, v] of Object.entries(settings)) {
    if (k === "tagKey") {
      if (typeof v !== "string" || !TAG_KEY.test(v))
        throw new SyncError(
          `${where}: tagKey must be a JavaScript identifier (got ${JSON.stringify(v)})`,
          254,
        )
      out[k] = v
    } else if (k === "option") {
      if (v !== "null" && v !== "undefined")
        throw new SyncError(
          `${where}: option must be "null" or "undefined" (got ${JSON.stringify(v)})`,
          254,
        )
      out[k] = v
    } else throw new SyncError(`${where}: unknown setting ${k}`, 254)
  }
  return out
}

export function packageRoot(dir: string): string {
  const root = resolve(dir)
  if (!existsSync(join(root, "package.json")))
    throw new SyncError(`no package.json in ${root}`, 252)
  if (!existsSync(join(root, "src"))) throw new SyncError(`no src directory in ${root}`, 252)
  return root
}

function packageConfig(root: string): Record<string, string> {
  const pkg = readJson(join(root, "package.json"))
  const field: unknown = isRecord(pkg) ? pkg["lean-ts"] : undefined
  if (field === undefined) return {}
  const where = `${join(root, "package.json")} ("lean-ts")`
  if (!isRecord(field)) throw new SyncError(`${where}: must be an object`, 254)
  return checkSettings(field, where)
}

function leanIdent(s: string): string {
  const t = s.replaceAll(/[^A-Za-z0-9_]/gu, "_")
  return /^[0-9]/u.test(t) ? `_${t}` : t
}

export function leanName(parts: readonly string[]): string {
  return parts.map((p, i) => (i === 0 ? p : `«${p}»`)).join(".")
}

export function moduleParts(module: string): string[] {
  const parts = module.replace(/\.ts$/u, "").split("/")
  return (parts[0] === "src" ? parts.slice(1) : parts).map(leanIdent)
}

function locate(b: ScannedBlock): string {
  return `${b.file}:${b.at.line}:${b.at.col}`
}

function placeholder(module: string): string {
  return `// Placeholder written by lean-ts sync for ${module}. Do not edit.\nexport {}\n`
}

interface Output {
  readonly module: string
  readonly file: string
  readonly outFile: string
  readonly at: ScannedBlock["at"]
}

export function aliasFile(b: Output): string {
  return join(dirname(b.file), "_lean", `${basename(b.file, ".ts")}.ts`)
}

function outputsOf(blocks: readonly Output[]): Map<string, string> {
  const out = new Map<string, string>()
  const perModule = new Map<string, Output[]>()
  for (const b of blocks) perModule.set(b.module, [...(perModule.get(b.module) ?? []), b])
  for (const b of blocks) out.set(b.outFile, "")
  for (const [module, bs] of perModule) {
    const only = bs[0]
    if (bs.length !== 1 || only === undefined) continue
    const alias = aliasFile(only)
    if (out.has(alias))
      throw new SyncError(
        `${only.file}:${only.at.line}:${only.at.col}: the generated module ${alias} of ${module} is also the module of another block`,
        252,
      )
    out.set(
      alias,
      `// Generated by lean-ts sync from ${module}. Do not edit.\nexport * from "./${basename(only.outFile)}"\n`,
    )
  }
  return out
}

let recordRound = 0

async function recordModels(files: readonly string[]): Promise<RecordedBlock[]> {
  recordRound++
  const registry = blockRegistry()
  registry.recording = []
  try {
    for (const f of files) {
      try {
        await import(`${pathToFileURL(f).href}?lean-ts-record=${recordRound}`)
      } catch (e) {
        throw new SyncError(
          `importing ${f} to read its models: ${e instanceof Error ? e.message : String(e)}`,
          254,
        )
      }
    }
    return registry.recording
  } finally {
    registry.recording = null
  }
}

function recordedModels(b: ScannedBlock, recorded: readonly RecordedBlock[]): Record<string, Json> {
  const r = recorded.find((x) => x.name === b.name && x.source === b.source)
  if (r === undefined)
    throw new SyncError(
      `${locate(b)}: importing ${b.file} did not run lean(${JSON.stringify(b.name)}, ...)`,
      254,
    )
  const models: unknown = isRecord(r.options) ? r.options["models"] : undefined
  if (!isRecord(models))
    throw new SyncError(`${locate(b)}: the models of the block are not an object`, 254)
  const out: Record<string, Json> = {}
  for (const k of b.modelNames) {
    try {
      out[k] = modelSchema(k, models[k])
    } catch (e) {
      throw new SyncError(`${locate(b)}: ${e instanceof Error ? e.message : String(e)}`, 254)
    }
  }
  return out
}

export async function readPackage(dir: string, writePlaceholders: boolean): Promise<Package> {
  const root = packageRoot(dir)
  const config = packageConfig(root)
  const scanned = tsFiles(join(root, "src")).flatMap((f) => scanFile(root, f))
  const seen = new Map<string, ScannedBlock>()
  const leanModules = new Map<string, ScannedBlock>()
  const pre: {
    b: ScannedBlock
    leanModule: string[]
    outFile: string
    settings: Record<string, string>
  }[] = []
  for (const b of scanned) {
    if (!BLOCK_NAME.test(b.name))
      throw new SyncError(
        `${locate(b)}: the block name ${JSON.stringify(b.name)} must be an identifier`,
        252,
      )
    const q = `${b.module}:${b.name}`
    const prev = seen.get(q)
    if (prev !== undefined)
      throw new SyncError(
        `${locate(b)}: the Lean block ${b.name} is also defined at ${locate(prev)}`,
        252,
      )
    seen.set(q, b)
    const leanModule = ["LeanTsEmbed", ...moduleParts(b.module), b.name]
    const ln = leanModule.join(".")
    const clash = leanModules.get(ln)
    if (clash !== undefined)
      throw new SyncError(
        `${locate(b)}: the Lean module ${ln} is also the module of ${locate(clash)}`,
        252,
      )
    leanModules.set(ln, b)
    const settings = {
      ...DEFAULT_SETTINGS,
      ...config,
      ...checkSettings(b.output, `${locate(b)} (output)`),
    }
    pre.push({
      b,
      leanModule,
      outFile: join(dirname(b.file), "_lean", `${basename(b.file, ".ts")}__${b.name}.ts`),
      settings,
    })
  }
  const withModels = [
    ...new Set(pre.filter((p) => p.b.modelNames.length !== 0).map((p) => p.b.file)),
  ]
  if (writePlaceholders && withModels.length !== 0) {
    for (const f of outputsOf(pre.map((p) => ({ ...p.b, outFile: p.outFile }))).keys()) {
      if (existsSync(f)) continue
      mkdirSync(dirname(f), { recursive: true })
      writeFileSync(f, placeholder(posixRelative(root, f)))
    }
  }
  const recorded = withModels.length === 0 ? [] : await recordModels(withModels)
  const blocks = pre.map(({ b, leanModule, outFile, settings }): Block => {
    const models = b.modelNames.length === 0 ? {} : recordedModels(b, recorded)
    const inputs = {
      ...blockInputs(b.name, b.source, { imports: b.imports, uses: b.uses, output: b.output }),
      models,
    }
    const key = createHash("sha256")
      .update(canonicalJson({ module: b.module, package: config, block: blockContent(inputs) }))
      .digest("hex")
    return { ...b, leanModule, outFile, settings, inputs, fnv: blockFnv(inputs), key }
  })
  return { root, config, blocks }
}

function resolveUse(pkg: Package, b: Block, use: string): Block {
  const i = use.lastIndexOf(":")
  const module =
    i < 0 ? b.module : posixRelative(pkg.root, resolve(dirname(b.file), use.slice(0, i)))
  const name = i < 0 ? use : use.slice(i + 1)
  const found = pkg.blocks.find((x) => x.module === module && x.name === name)
  if (found === undefined)
    throw new SyncError(
      `${locate(b)}: the Lean block ${b.name} uses ${JSON.stringify(use)}, which is not a block of the package`,
      252,
    )
  if (canonicalJson(found.settings) !== canonicalJson(b.settings))
    throw new SyncError(
      `${locate(b)}: the Lean block ${b.name} (settings ${canonicalJson(b.settings)}) uses ${found.name} of ${found.module} (settings ${canonicalJson(found.settings)}); the settings must be the same`,
      254,
    )
  return found
}

function modelsModule(b: Block): string[] {
  return ["LeanTsModels", ...moduleParts(b.module)]
}

function blockLean(pkg: Package, b: Block): { head: string; text: string } {
  const used = b.uses.map((u) => resolveUse(pkg, b, u))
  const models = b.modelNames.length === 0 ? [] : [leanName(modelsModule(b))]
  const imports = [
    ...new Set([...b.imports, ...models, ...used.map((u) => leanName(u.leanModule))]),
  ]
  const ns = leanName(b.leanModule)
  const head =
    imports.map((i) => `import ${i}\n`).join("") +
    `\nnamespace ${ns}\n` +
    [...models, ...used.map((u) => leanName(u.leanModule))].map((o) => `open ${o}\n`).join("") +
    "\n"
  return { head, text: `${head}${b.source}\n\nend ${ns}\n` }
}

function leanMessages(
  output: string,
  offsets: ReadonlyMap<string, { b: Block; headLines: number }>,
): string[] {
  const lines = output.split("\n")
  const out: string[] = []
  for (let i = 0; i < lines.length; i++) {
    const m = LAKE_MESSAGE.exec((lines[i] ?? "").trim())
    if (m === null) continue
    const [, sev, path, ln, col, msg] = m
    const info = offsets.get(path ?? "")
    const k = Number(ln) - (info?.headLines ?? 0)
    const c = Number(col)
    let text: string
    if (info === undefined) text = `${path}:${ln}:${col}: ${sev}: ${msg}`
    else if (k < 1)
      text = `${locate(info.b)}: ${sev}: (lean block ${info.b.name}, Lean ${ln}:${col}) ${msg}`
    else {
      const line = info.b.sourceAt.line + k - 1
      const tsCol = k === 1 ? info.b.sourceAt.col + c : c + 1
      text = `${info.b.file}:${line}:${tsCol}: ${sev}: (lean block ${info.b.name}, Lean ${k}:${c}) ${msg}`
    }
    while (
      i + 1 < lines.length &&
      (lines[i + 1] ?? "").trim() !== "" &&
      LAKE_MESSAGE.exec((lines[i + 1] ?? "").trim()) === null &&
      !/^(✖|✔|⣿|trace:|info:|error:|warning:|Some required|- )/u.test(lines[i + 1] ?? "")
    ) {
      text += `\n${lines[i + 1]}`
      i++
    }
    out.push(text)
  }
  return out
}

export function run(
  cmd: string,
  args: readonly string[],
  cwd?: string,
): { status: number; stdout: string; stderr: string } {
  const r = spawnSync(cmd, args, { cwd, encoding: "utf8", maxBuffer: 1 << 28 })
  if (r.error !== undefined) throw new SyncError(`cannot run ${cmd}: ${r.error.message}`, 255)
  return { status: r.status ?? 255, stdout: r.stdout, stderr: r.stderr }
}

export function leanTypescriptCli(given: string | undefined): string {
  return given ?? process.env["LEAN_TYPESCRIPT"] ?? "lean-typescript"
}

export function specifier(from: string, to: string): string {
  const r = relative(dirname(from), to).split(sep).join("/")
  return r.startsWith(".") ? r : `./${r}`
}

function removeStale(dir: string, keep: ReadonlySet<string>): void {
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name)
    if (e.isDirectory()) {
      if (e.name === "node_modules") continue
      if (e.name === "_lean") {
        for (const f of readdirSync(p))
          if (!keep.has(join(p, f))) rmSync(join(p, f), { recursive: true })
        if (readdirSync(p).length === 0) rmdirSync(p)
      } else removeStale(p, keep)
    }
  }
}

function packageModels(pkg: Package): Map<string[], string> {
  const perModule = new Map<string, { parts: string[]; models: Map<string, Json>; b: Block }>()
  for (const b of pkg.blocks) {
    if (b.modelNames.length === 0) continue
    const entry = perModule.get(b.module) ?? { parts: modelsModule(b), models: new Map(), b }
    perModule.set(b.module, entry)
    for (const [name, schema] of Object.entries(b.inputs.models)) {
      const prev = entry.models.get(name)
      if (prev !== undefined && canonicalJson(prev) !== canonicalJson(schema))
        throw new SyncError(
          `${locate(b)}: the model ${name} has another JSON Schema in the block ${entry.b.name} of the same module`,
          252,
        )
      entry.models.set(name, schema)
    }
  }
  const out = new Map<string[], string>()
  for (const [module, e] of perModule)
    out.set(e.parts, modelsLean(module, e.parts.slice(1), e.models).lean)
  return out
}

export function blocksFile(root: string): string {
  return join(root, ".lean-ts", "blocks.json")
}

export interface Named {
  readonly lean: string
  readonly typescript: string
}

export interface Summary {
  readonly public: readonly Named[]
  readonly types: readonly Named[]
}

export interface Synced {
  readonly pkg: Package
  readonly summaries: ReadonlyMap<string, Summary>
}

function named(v: unknown): Named[] {
  if (!Array.isArray(v)) return []
  return v.flatMap((x: unknown) =>
    isRecord(x) && typeof x["lean"] === "string" && typeof x["typescript"] === "string"
      ? [{ lean: x["lean"], typescript: x["typescript"] }]
      : [],
  )
}

export async function syncPackage(
  dir: string,
  cliPath: string | undefined,
  log: Log,
  csimp: (pkg: Package) => ReadonlyMap<string, string> = () => new Map(),
): Promise<Synced> {
  const cli = leanTypescriptCli(cliPath)
  const gv = run(cli, ["--generator-version"])
  if (gv.status !== 0) throw new SyncError(`${cli} --generator-version failed: ${gv.stderr}`, 255)
  if (gv.stdout.trim() !== GENERATOR_VERSION)
    throw new SyncError(
      `${cli} generates version ${gv.stdout.trim()}, this lean-ts expects ${GENERATOR_VERSION}`,
      255,
    )
  const pkg = await readPackage(dir, true)
  const ws = join(pkg.root, ".lean-ts", "workspace")
  rmSync(join(ws, "LeanTsEmbed"), { recursive: true, force: true })
  rmSync(join(ws, "LeanTsModels"), { recursive: true, force: true })
  rmSync(join(ws, "LeanTsCsimp"), { recursive: true, force: true })
  mkdirSync(ws, { recursive: true })
  writeFileSync(join(ws, "lakefile.toml"), LAKEFILE)
  const models = packageModels(pkg)
  for (const [module, m] of models) {
    const rel = `${module.join("/")}.lean`
    mkdirSync(dirname(join(ws, rel)), { recursive: true })
    writeFileSync(join(ws, rel), m)
  }
  writeFileSync(
    join(ws, "LeanTsModels.lean"),
    [...models.keys()].map((m) => `import ${leanName(m)}\n`).join("") || "\n",
  )
  writeFileSync(
    join(ws, "LeanTsEmbed.lean"),
    pkg.blocks.map((b) => `import ${leanName(b.leanModule)}\n`).join("") || "\n",
  )
  const csimps = csimp(pkg)
  for (const [rel, text] of csimps) {
    mkdirSync(dirname(join(ws, rel)), { recursive: true })
    writeFileSync(join(ws, rel), text)
  }
  writeFileSync(
    join(ws, "LeanTsCsimp.lean"),
    [...csimps.keys()]
      .map((rel) => `import ${leanName(rel.replace(/\.lean$/u, "").split("/"))}\n`)
      .join("") || "\n",
  )
  const offsets = new Map<string, { b: Block; headLines: number }>()
  for (const b of pkg.blocks) {
    const { head, text } = blockLean(pkg, b)
    const rel = `${b.leanModule.join("/")}.lean`
    mkdirSync(dirname(join(ws, rel)), { recursive: true })
    writeFileSync(join(ws, rel), text)
    offsets.set(rel, { b, headLines: head.split("\n").length - 1 })
  }
  const lake = run(process.env["LAKE"] ?? "lake", ["build"], ws)
  const messages = leanMessages(lake.stdout + lake.stderr, offsets)
  for (const m of messages)
    if (lake.status !== 0 || m.split("\n")[0]?.includes(": warning:") === true) log(`lean-ts: ${m}`)
  if (lake.status !== 0) {
    if (messages.length === 0) log(lake.stdout + lake.stderr)
    throw new SyncError("lake build failed", 254)
  }
  const jobs = pkg.blocks.map((b) => ({
    module: b.leanModule.join("."),
    namespace: b.leanModule.join("."),
    output_file: b.outFile,
    type_modules: b.uses.map((u) => {
      const used = resolveUse(pkg, b, u)
      return { namespace: used.leanModule.join("."), module: specifier(b.outFile, used.outFile) }
    }),
    model_modules: b.models.map((m) => ({
      namespace: [...modelsModule(b), m.name].join("."),
      key: `${b.fnv}:${m.name}`,
      module: m.from.startsWith("/") ? specifier(b.outFile, m.from) : m.from,
      export: m.exportName,
    })),
    tag_key: b.settings["tagKey"],
    option: b.settings["option"],
    block: { name: b.name, module: b.module, fnv: b.fnv },
    ts_root: `${posixRelative(dirname(b.outFile), pkg.root)}/`,
  }))
  writeFileSync(join(ws, "batch.json"), JSON.stringify(jobs, null, 2) + "\n")
  const outputs = outputsOf(pkg.blocks)
  const companions = pkg.blocks.map((b) => b.outFile.replace(/\.ts$/u, ".block.ts"))
  for (const c of companions) rmSync(c, { force: true })
  const summaries = new Map<string, Summary>()
  if (pkg.blocks.length !== 0) {
    const gen = run(cli, [
      "module",
      "generate",
      "--batch",
      join(ws, "batch.json"),
      "--import",
      "LeanTsCsimp",
      "--search-path",
      join(ws, ".lake", "build", "lib", "lean"),
      "--output",
      "json",
    ])
    if (gen.status !== 0) {
      log(gen.stderr + gen.stdout)
      throw new SyncError("lean-typescript module generate failed", gen.status)
    }
    const parsed: unknown = JSON.parse(gen.stdout)
    if (Array.isArray(parsed))
      parsed.forEach((s: unknown, i) => {
        const b = pkg.blocks[i]
        if (b !== undefined && isRecord(s))
          summaries.set(b.outFile, { public: named(s["public"]), types: named(s["types"]) })
        const skipped: unknown = isRecord(s) ? s["skipped"] : undefined
        if (Array.isArray(skipped))
          for (const k of skipped)
            if (isRecord(k)) log(`lean-ts: skipped ${String(k["name"])}: ${String(k["reason"])}`)
      })
  }
  for (const [f, text] of outputs) if (text !== "") writeFileSync(f, text)
  removeStale(
    join(pkg.root, "src"),
    new Set([...outputs.keys(), ...companions.filter((c) => existsSync(c))]),
  )
  const registry: Record<string, Json> = {}
  for (const b of pkg.blocks)
    registry[`${b.module}:${b.name}`] = {
      sha256: b.key,
      fnv: b.fnv,
      output: posixRelative(pkg.root, b.outFile),
    }
  writeFileSync(
    blocksFile(pkg.root),
    JSON.stringify(JSON.parse(canonicalJson(registry)), null, 2) + "\n",
  )
  log(`lean-ts: ${pkg.blocks.length} blocks of ${pkg.root} checked and generated`)
  return { pkg, summaries }
}

export interface StatusRow {
  readonly block: string
  readonly state: "fresh" | "stale" | "removed"
}

export function statusPackage(pkg: Package): StatusRow[] {
  const file = blocksFile(pkg.root)
  const recorded: unknown = existsSync(file) ? readJson(file) : {}
  const known = isRecord(recorded) ? recorded : {}
  const rows: StatusRow[] = []
  const current = new Set<string>()
  for (const b of pkg.blocks) {
    const q = `${b.module}:${b.name}`
    current.add(q)
    const entry = known[q]
    const fresh = isRecord(entry) && entry["sha256"] === b.key && existsSync(b.outFile)
    rows.push({ block: q, state: fresh ? "fresh" : "stale" })
  }
  for (const q of Object.keys(known)) if (!current.has(q)) rows.push({ block: q, state: "removed" })
  return rows.toSorted((a, b) => a.block.localeCompare(b.block))
}
