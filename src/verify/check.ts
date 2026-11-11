import { spawnSync } from "node:child_process"
import { createHash } from "node:crypto"
import {
  cpSync,
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs"
import { dirname, join, relative, resolve, sep } from "node:path"
import { fileURLToPath } from "node:url"
import {
  type ArrowFunctionExpression,
  type Expression,
  type Function as FunctionNode,
  parseSync,
  type Program,
  Visitor,
} from "oxc-parser"
import { canonicalJson, type Json } from "../key.ts"
import { leanIdent as modelIdent } from "../models.ts"
import { resolve as resolveDesc, type TypeDesc } from "../runtime/marshal.ts"
import { posixRelative, SyncError, tsFiles } from "../scan.ts"
import {
  aliasFile,
  type Block,
  isRecord,
  leanName,
  leanTypescriptCli,
  type Log,
  moduleParts,
  type Package,
  run,
  type Summary,
  syncPackage,
} from "../sync.ts"
import {
  astHash,
  BIG,
  BOOL,
  type FieldType,
  Fn,
  ident,
  leanType,
  NUM,
  type Located,
  STR,
  Translator,
  TranslateError,
  type TsType,
  type TypeResolver,
} from "./translate.ts"

export const STATUSES = [
  "proved",
  "sorry",
  "axioms",
  "failed",
  "missing",
  "mismatch",
  "unextracted",
  "stale",
] as const

export type Status = (typeof STATUSES)[number]

function isStatus(s: unknown): s is Status {
  return typeof s === "string" && (STATUSES as readonly string[]).includes(s)
}

function isDesc(x: unknown): x is TypeDesc {
  return isRecord(x) && typeof x["kind"] === "string"
}

const LAKEFILE_EXTRA = `
[[lean_lib]]
name = "LeanTsLib"

[[lean_lib]]
name = "LeanTsModel"

[[lean_lib]]
name = "Proofs"
globs = ["Proofs.+"]
`

interface Import {
  readonly from: string
  readonly exportName: string | null
}

export interface SpecRef {
  readonly exportName: string
  readonly outFile: string
  readonly at: number
}

export interface ModelCall {
  readonly file: string
  readonly module: string
  readonly fn: string
  readonly fnNode: FunctionNode | ArrowFunctionExpression
  readonly refines: SpecRef | undefined
  readonly requires: SpecRef | undefined
  readonly ensures: readonly (readonly [string, SpecRef])[]
  readonly hash: string
  readonly at: number
}

export interface Source extends Located {
  readonly module: string
  readonly program: Program
  readonly imports: ReadonlyMap<string, Import>
  readonly fns: ReadonlyMap<string, FunctionNode | ArrowFunctionExpression>
  readonly models: readonly ModelCall[]
}

export interface Row {
  readonly fn: string
  readonly label: string
  readonly status: Status
}

interface Csimp {
  readonly spec: string
  readonly module: string
  readonly modes: readonly string[]
}

interface LockEntry {
  readonly spec_hash: string
  readonly lean: string
  readonly obligations: Readonly<Record<string, Status>>
  readonly csimp?: Csimp
}

type Lock = Readonly<Record<string, LockEntry>>

function lineStarts(text: string): number[] {
  const starts = [0]
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") starts.push(i + 1)
  return starts
}

function locator(file: string, text: string): (offset: number) => string {
  const starts = lineStarts(text)
  return (offset) => {
    let lo = 0
    let hi = starts.length - 1
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1
      if ((starts[mid] ?? 0) <= offset) lo = mid
      else hi = mid - 1
    }
    return `${file}:${lo + 1}:${offset - (starts[lo] ?? 0) + 1}`
  }
}

function tsSpecifierFile(file: string, spec: string): string {
  return resolve(dirname(file), spec)
}

export function readSource(root: string, file: string): Source {
  const text = readFileSync(file, "utf8")
  const where = locator(file, text)
  const parsed = parseSync(file, text, { lang: "ts", sourceType: "module", preserveParens: false })
  const err = parsed.errors[0]
  if (err !== undefined)
    throw new SyncError(`${where(err.labels[0]?.start ?? 0)}: cannot parse: ${err.message}`, 252)
  const imports = new Map<string, Import>()
  const fns = new Map<string, FunctionNode | ArrowFunctionExpression>()
  const modelNames = new Set<string>()
  const verifyNamespaces = new Set<string>()
  for (const s of parsed.program.body) {
    if (s.type === "ImportDeclaration") {
      const from = s.source.value.startsWith(".")
        ? tsSpecifierFile(file, s.source.value)
        : s.source.value
      for (const sp of s.specifiers) {
        if (sp.type === "ImportNamespaceSpecifier")
          imports.set(sp.local.name, { from, exportName: null })
        else if (sp.type === "ImportSpecifier") {
          const name = sp.imported.type === "Literal" ? sp.imported.value : sp.imported.name
          imports.set(sp.local.name, { from, exportName: name })
          if (from === "lean-ts/verify" && name === "model") modelNames.add(sp.local.name)
        }
        if (sp.type === "ImportNamespaceSpecifier" && from === "lean-ts/verify")
          verifyNamespaces.add(sp.local.name)
      }
      continue
    }
    const d = s.type === "ExportNamedDeclaration" ? s.declaration : s
    if (d === null) continue
    if (d.type === "FunctionDeclaration" && d.id !== null) fns.set(d.id.name, d)
    if (d.type === "VariableDeclaration" && d.kind === "const")
      for (const x of d.declarations)
        if (x.id.type === "Identifier" && x.init?.type === "ArrowFunctionExpression")
          fns.set(x.id.name, x.init)
  }
  const module = posixRelative(root, file)
  const models: ModelCall[] = []
  const specRef = (e: Expression, label: string): SpecRef => {
    const bad = (): never => {
      throw new SyncError(
        `${where(e.start)}: the ${label} specification must be a function of a generated module (a named import or a property of a namespace import of _lean/)`,
        252,
      )
    }
    if (e.type === "Identifier") {
      const i = imports.get(e.name)
      if (i === undefined || i.exportName === null) return bad()
      return { exportName: i.exportName, outFile: i.from, at: e.start }
    }
    if (
      e.type === "MemberExpression" &&
      !e.computed &&
      e.object.type === "Identifier" &&
      e.property.type === "Identifier"
    ) {
      const i = imports.get(e.object.name)
      if (i === undefined || i.exportName !== null) return bad()
      return { exportName: e.property.name, outFile: i.from, at: e.start }
    }
    return bad()
  }
  new Visitor({
    CallExpression(c) {
      const f = c.callee
      const isModel =
        (f.type === "Identifier" && modelNames.has(f.name)) ||
        (f.type === "MemberExpression" &&
          !f.computed &&
          f.object.type === "Identifier" &&
          verifyNamespaces.has(f.object.name) &&
          f.property.type === "Identifier" &&
          f.property.name === "model")
      if (!isModel) return
      const [target, options, ...rest] = c.arguments
      if (
        target?.type !== "Identifier" ||
        options?.type !== "ObjectExpression" ||
        rest.length !== 0
      )
        throw new SyncError(
          `${where(c.start)}: model takes a function of the module and an object literal`,
          252,
        )
      const fnNode = fns.get(target.name)
      if (fnNode === undefined)
        throw new SyncError(
          `${where(target.start)}: ${target.name} must be a function declaration or a const arrow function of the module`,
          252,
        )
      let refines: SpecRef | undefined
      let requires: SpecRef | undefined
      const ensures: [string, SpecRef][] = []
      for (const p of options.properties) {
        if (p.type !== "Property" || p.computed || p.key.type !== "Identifier")
          throw new SyncError(
            `${where(p.start)}: the options of model must be plain properties`,
            252,
          )
        if (p.key.name === "refines") refines = specRef(p.value, "refines")
        else if (p.key.name === "requires") requires = specRef(p.value, "requires")
        else if (p.key.name === "ensures") {
          if (p.value.type !== "ObjectExpression")
            throw new SyncError(
              `${where(p.value.start)}: ensures must be an object literal of labelled specifications`,
              252,
            )
          for (const q of p.value.properties) {
            if (q.type !== "Property" || q.computed || q.key.type !== "Identifier")
              throw new SyncError(`${where(q.start)}: the labels of ensures must be names`, 252)
            if (
              !/^[A-Za-z_][A-Za-z0-9_]*$/u.test(q.key.name) ||
              q.key.name === "refines" ||
              q.key.name === "returnsNat"
            )
              throw new SyncError(
                `${where(q.start)}: ${q.key.name} cannot be a label of ensures`,
                252,
              )
            ensures.push([q.key.name, specRef(q.value, q.key.name)])
          }
        } else throw new SyncError(`${where(p.start)}: unknown option ${p.key.name} of model`, 252)
      }
      models.push({
        file,
        module,
        fn: target.name,
        fnNode,
        refines,
        requires,
        ensures,
        hash: createHash("sha256")
          .update(astHash({ fn: fnNode, options }))
          .digest("hex"),
        at: c.start,
      })
    },
  }).visit(parsed.program)
  return { file, where, module, program: parsed.program, imports, fns, models }
}

export function readSources(root: string): Source[] {
  return tsFiles(join(root, "src")).map((f) => readSource(root, f))
}

function blockOf(pkg: Package, file: string): Block | undefined {
  const f = file.endsWith(".ts") ? file : `${file}.ts`
  return (
    pkg.blocks.find((b) => b.outFile === f) ??
    pkg.blocks.find(
      (b) => aliasFile(b) === f && pkg.blocks.filter((x) => x.module === b.module).length === 1,
    )
  )
}

function specBlock(pkg: Package, src: Source, ref: SpecRef): Block {
  const b = blockOf(pkg, ref.outFile)
  if (b === undefined)
    throw new SyncError(
      `${src.where(ref.at)}: ${ref.outFile} is not a module generated from a lean(...) block`,
      252,
    )
  return b
}

function specHash(pkg: Package, src: Source, m: ModelCall): string {
  const refs = [m.refines, m.requires, ...m.ensures.map(([, r]) => r)].filter(
    (r) => r !== undefined,
  )
  const keys = [...new Set(refs.map((r) => specBlock(pkg, src, r).key))].toSorted()
  return createHash("sha256")
    .update(JSON.stringify({ fn: m.hash, blocks: keys }))
    .digest("hex")
}

export function modelModule(module: string): string[] {
  return ["LeanTsModel", ...moduleParts(module)]
}

function qualified(m: ModelCall): string {
  return `${m.module}:${m.fn}`
}

type Descs = Map<string, Map<string, TypeDesc>>

const DESCS_CHILD = `
import { pathToFileURL } from "node:url"
const ser = (d0, stack) => {
  let d = d0
  while (d.kind === "ref") d = d.get()
  if ((d.kind === "struct" || d.kind === "inductive") && stack.includes(d.name)) return { kind: "recursive", name: d.name }
  const st = d.kind === "struct" || d.kind === "inductive" ? [...stack, d.name] : stack
  const v = (x) => ({ name: x.name, fields: x.fields.map((f) => ({ key: f.key, omitNone: f.omitNone, flat: f.flat, desc: ser(f.desc, st) })) })
  switch (d.kind) {
    case "list": case "array": case "option": return { ...d, item: ser(d.item, st) }
    case "prod": return { kind: "prod", fst: ser(d.fst, st), snd: ser(d.snd, st) }
    case "except": return { kind: "except", error: ser(d.error, st), value: ser(d.value, st) }
    case "struct": return { kind: "struct", name: d.name, trivial: d.trivial, variant: v(d.variant) }
    case "inductive": return { kind: "inductive", name: d.name, tagKey: d.tagKey, variants: d.variants.map(v) }
    case "subtype": return { kind: "subtype", name: d.name, base: ser(d.base, st) }
    case "model": return { kind: "model", name: d.name, key: d.key }
    case "fin": return { kind: "fin", bound: String(d.bound) }
    default: return { kind: d.kind, ...(d.bits === undefined ? {} : { bits: d.bits }), ...(d.name === undefined ? {} : { name: d.name }), ...(d.ctors === undefined ? {} : { ctors: d.ctors }) }
  }
}
const [first, ...files] = JSON.parse(process.argv[1])
for (const f of first) await import(pathToFileURL(f).href)
const out = {}
for (const f of files) {
  const m = await import(pathToFileURL(f).href)
  out[f] = {}
  for (const [k, x] of Object.entries(m)) {
    const d = (typeof x === "object" && x !== null) || typeof x === "function" ? x.desc : undefined
    if (typeof d === "object" && d !== null && typeof d.kind === "string") out[f][k] = ser(d, [])
  }
}
process.stdout.write(JSON.stringify(out))
`

function loadDescs(pkg: Package, sources: readonly Source[]): Descs {
  const users = sources.filter((s) => s.models.length !== 0)
  const files = new Set<string>()
  for (const s of users)
    for (const i of s.imports.values())
      if (blockOf(pkg, i.from) !== undefined)
        files.add(i.from.endsWith(".ts") ? i.from : `${i.from}.ts`)
  const out: Descs = new Map()
  if (files.size === 0) return out
  const r = spawnSync(
    process.execPath,
    [
      "--input-type=module",
      "-e",
      DESCS_CHILD,
      JSON.stringify([users.map((s) => s.file), ...files]),
    ],
    { encoding: "utf8", maxBuffer: 1 << 28 },
  )
  if (r.status !== 0)
    throw new SyncError(`reading the types of the generated modules: ${r.stderr}`, 254)
  const parsed: unknown = JSON.parse(r.stdout)
  if (!isRecord(parsed))
    throw new SyncError("reading the types of the generated modules returned no object", 255)
  for (const [f, ds] of Object.entries(parsed)) {
    const m = new Map<string, TypeDesc>()
    if (isRecord(ds)) for (const [k, d] of Object.entries(ds)) if (isDesc(d)) m.set(k, d)
    out.set(f, m)
  }
  return out
}

function descType(d: TypeDesc, names: ReadonlyMap<string, string>, seen: Set<string>): TsType {
  const r = resolveDesc(d)
  const fields = (
    fs: readonly { key: string; desc: TypeDesc; omitNone: boolean; flat: boolean }[],
  ): FieldType[] =>
    fs.flatMap((f): FieldType[] => {
      if (f.flat) {
        const inner = descType(f.desc, names, seen)
        return inner.k === "struct" ? [...inner.fields] : []
      }
      const fr = resolveDesc(f.desc)
      return [
        {
          key: f.key,
          lean: f.omitNone ? `${f.key}?` : f.key,
          type: descType(f.desc, names, seen),
          nat: fr.kind === "nat",
        },
      ]
    })
  const leanOf = (name: string): string => {
    const l = names.get(name)
    if (l === undefined) throw new TranslateError(`the Lean name of the type ${name} is unknown`)
    return l
  }
  switch (r.kind) {
    case "nat":
    case "int":
      return BIG
    case "bool":
      return BOOL
    case "string":
      return STR
    case "list":
      return { k: "list", item: descType(r.item, names, seen) }
    case "option":
      return { k: "opt", item: descType(r.item, names, seen), absent: r.absent }
    case "prod":
      return { k: "tuple", items: [descType(r.fst, names, seen), descType(r.snd, names, seen)] }
    case "struct":
      if (seen.has(r.name))
        throw new TranslateError(`the recursive type ${r.name} is outside the subset`)
      return { k: "struct", lean: leanOf(r.name), ts: r.name, fields: fields(r.variant.fields) }
    case "enum":
      return { k: "enum", lean: leanOf(r.name), ts: r.name, ctors: r.ctors }
    case "inductive": {
      if (seen.has(r.name))
        throw new TranslateError(`the recursive type ${r.name} is outside the subset`)
      const inner = new Set([...seen, r.name])
      return {
        k: "ind",
        lean: leanOf(r.name),
        ts: r.name,
        tagKey: r.tagKey,
        variants: r.variants.map((v) => ({
          name: v.name,
          fields: v.fields.map((f) => ({
            key: f.key,
            lean: f.key,
            type: descType(f.desc, names, inner),
            nat: resolveDesc(f.desc).kind === "nat",
          })),
        })),
      }
    }
    default:
      throw new TranslateError(`the Lean type of kind ${r.kind} is outside the subset`)
  }
}

function nullableOf(
  s: Readonly<Record<string, unknown>>,
): Readonly<Record<string, unknown>> | undefined {
  const any = s["anyOf"]
  if (Array.isArray(any) && any.length === 2) {
    const other = any.find((x: unknown) => !(isRecord(x) && x["type"] === "null"))
    if (isRecord(other) && any.some((x: unknown) => isRecord(x) && x["type"] === "null"))
      return other
  }
  const t = s["type"]
  if (Array.isArray(t) && t.length === 2 && t.includes("null"))
    return { ...s, type: t.find((x: unknown) => x !== "null") }
  return undefined
}

function jsonType(s: unknown, where: string): { t: TsType; nat: boolean } {
  if (!isRecord(s)) throw new TranslateError(`${where}: a property schema is not an object`)
  const min = s["minimum"]
  const ex = s["exclusiveMinimum"]
  const lo = typeof min === "number" ? min : typeof ex === "number" ? Math.floor(ex) + 1 : undefined
  switch (s["type"]) {
    case "integer":
      return { t: NUM, nat: lo !== undefined && lo >= 0 }
    case "string":
      return { t: STR, nat: false }
    case "boolean":
      return { t: BOOL, nat: false }
    case "array":
      return { t: { k: "list", item: jsonType(s["items"], where).t }, nat: false }
    default:
      throw new TranslateError(
        `${where}: the model property ${JSON.stringify(s)} is outside the subset lean-ts translates`,
      )
  }
}

export function modelStruct(json: Json, lean: string, ts: string, where: string): TsType {
  if (!isRecord(json) || !isRecord(json["properties"]))
    throw new TranslateError(`${where}: the model ${ts} is not an object schema`)
  const req = json["required"]
  const required = new Set(Array.isArray(req) ? req.filter((x) => typeof x === "string") : [])
  const fields: FieldType[] = Object.entries(json["properties"]).map(([key, raw]) => {
    if (!isRecord(raw))
      throw new TranslateError(`${where}: the property ${key} of ${ts} is not an object`)
    const inner = nullableOf(raw)
    const { t, nat } = jsonType(inner ?? raw, where)
    if (!required.has(key))
      return { key, lean: `${key}?`, type: { k: "opt", item: t, absent: "undefined" }, nat: false }
    if (inner !== undefined)
      return { key, lean: key, type: { k: "opt", item: t, absent: "null" }, nat: false }
    return { key, lean: key, type: t, nat }
  })
  return { k: "struct", lean, ts, fields }
}

export function typeResolver(
  pkg: Package,
  src: Source,
  summaries: ReadonlyMap<string, Summary> | undefined,
  descs: Descs | undefined,
): TypeResolver {
  return {
    reference(name, qualifier, at) {
      const local = qualifier ?? name
      const i = src.imports.get(local)
      if (i === undefined) return undefined
      const exportName =
        qualifier === undefined ? i.exportName : i.exportName === null ? name : undefined
      if (exportName === undefined || exportName === null) return undefined
      if (i.from === "lean-ts/schema" && (exportName === "Nat" || exportName === "Int")) return BIG
      const b = blockOf(pkg, i.from)
      if (b === undefined) return undefined
      if (summaries === undefined || descs === undefined)
        return { k: "struct", lean: exportName, ts: exportName, fields: [] }
      const summary = summaries.get(b.outFile)
      const d = descs.get(i.from.endsWith(".ts") ? i.from : `${i.from}.ts`)?.get(exportName)
      if (summary === undefined || d === undefined)
        throw new TranslateError(
          `${src.where(at)}: ${exportName} is not a type generated from ${b.name}`,
        )
      const names = new Map(summary.types.map((t) => [t.typescript, t.lean]))
      return descType(d, names, new Set())
    },
    model(name, at) {
      const i = src.imports.get(name)
      const from = i === undefined ? src.file : i.from
      const exportName = i === undefined ? name : i.exportName
      for (const b of pkg.blocks)
        for (const m of b.models)
          if (m.from === from && m.exportName === exportName) {
            const json = b.inputs.models[m.name]
            if (json === undefined)
              throw new TranslateError(`${src.where(at)}: no JSON Schema of the model ${m.name}`)
            const lean = `${leanName(["LeanTsModels", ...moduleParts(b.module)])}.${modelIdent(m.name)}`
            return modelStruct(json, lean, m.name, src.where(at))
          }
      return undefined
    },
  }
}

interface SpecName {
  readonly lean: string
  readonly module: string
}

function specName(
  pkg: Package,
  src: Source,
  ref: SpecRef,
  summaries: ReadonlyMap<string, Summary>,
): SpecName {
  const b = specBlock(pkg, src, ref)
  const p = summaries.get(b.outFile)?.public.find((x) => x.typescript === ref.exportName)
  if (p === undefined)
    throw new SyncError(
      `${src.where(ref.at)}: ${ref.exportName} is not a public function of the block ${b.name}`,
      252,
    )
  return { lean: p.lean, module: leanName(b.leanModule) }
}

function obligations(
  m: ModelCall,
  fn: Fn,
  pkg: Package,
  src: Source,
  summaries: ReadonlyMap<string, Summary>,
): { props: Map<string, string>; imports: Set<string> } {
  const binders = fn.params.map((p) => `(${ident(p.name)} : ${p.nat ? "Nat" : leanType(p.type)})`)
  const args = fn.params.map((p) => ident(p.name)).join(" ")
  const a = args === "" ? "" : ` ${args}`
  const call = `(${ident(fn.name)}${a})`
  const imports = new Set<string>()
  const spec = (r: SpecRef): string => {
    const n = specName(pkg, src, r, summaries)
    imports.add(n.module)
    return `_root_.${n.lean}`
  }
  const pre = m.requires === undefined ? "" : `${spec(m.requires)}${a} = true → `
  const wrap = (body: string): string =>
    binders.length === 0 ? `${pre}${body}` : `∀ ${binders.join(" ")}, ${pre}${body}`
  const ret = leanType(fn.ret)
  const props = new Map<string, string>()
  if (m.refines !== undefined) {
    const expected = `(${spec(m.refines)}${a} : ${ret})`
    props.set(
      "refines",
      wrap(fn.fails ? `${call} = Except.ok ${expected}` : `${call} = ${expected}`),
    )
  }
  for (const [label, r] of m.ensures) {
    const e = spec(r)
    props.set(
      label,
      wrap(fn.fails ? `∀ r, ${call} = Except.ok r → ${e}${a} r = true` : `${e}${a} ${call} = true`),
    )
  }
  if (fn.retNat)
    props.set("returnsNat", wrap(fn.fails ? `∀ r, ${call} = Except.ok r → 0 ≤ r` : `0 ≤ ${call}`))
  return { props, imports }
}

function libDir(): string {
  const here = dirname(fileURLToPath(import.meta.url))
  const dev = join(here, "..", "lean")
  return existsSync(join(dev, "LeanTsLib")) ? dev : join(here, "..", "src", "lean")
}

function leanFiles(dir: string): string[] {
  if (!existsSync(dir)) return []
  const out: string[] = []
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name)
    if (e.isDirectory()) out.push(...leanFiles(p))
    else if (e.name.endsWith(".lean")) out.push(p)
  }
  return out.toSorted()
}

function lockFile(root: string): string {
  return join(root, "lean-ts.lock")
}

function readLock(root: string): Lock {
  const f = lockFile(root)
  if (!existsSync(f)) return {}
  const j: unknown = JSON.parse(readFileSync(f, "utf8"))
  if (!isRecord(j)) throw new SyncError(`${f}: not a JSON object`, 254)
  const out: Record<string, LockEntry> = {}
  for (const [k, v] of Object.entries(j)) {
    if (
      !isRecord(v) ||
      typeof v["spec_hash"] !== "string" ||
      typeof v["lean"] !== "string" ||
      !isRecord(v["obligations"])
    )
      throw new SyncError(`${f}: the entry ${k} is malformed`, 254)
    const obls: Record<string, Status> = {}
    for (const [l, s] of Object.entries(v["obligations"])) {
      if (!isStatus(s))
        throw new SyncError(`${f}: the entry ${k} has an unknown status for ${l}`, 254)
      obls[l] = s
    }
    const c = v["csimp"]
    const csimp =
      isRecord(c) &&
      typeof c["spec"] === "string" &&
      typeof c["module"] === "string" &&
      Array.isArray(c["modes"]) &&
      c["modes"].every((x: unknown) => typeof x === "string")
        ? { spec: c["spec"], module: c["module"], modes: c["modes"].map(String) }
        : undefined
    if (c !== undefined && csimp === undefined)
      throw new SyncError(`${f}: the csimp of ${k} is malformed`, 254)
    out[k] = {
      spec_hash: v["spec_hash"],
      lean: v["lean"],
      obligations: obls,
      ...(csimp === undefined ? {} : { csimp }),
    }
  }
  return out
}

function moduleFileOf(ws: string, parts: readonly string[]): string {
  return join(ws, `${parts.join("/")}.lean`)
}

export interface Checked {
  readonly rows: readonly Row[]
  readonly lock: Lock
}

export async function checkPackage(
  dir: string,
  cliPath: string | undefined,
  log: Log,
): Promise<Checked> {
  const cli = leanTypescriptCli(cliPath)
  const first = await syncPackage(dir, cliPath, log, csimpFiles)
  const { pkg, summaries } = first
  const before = canonicalJson(Object.fromEntries(csimpFiles(pkg)))
  const ws = join(pkg.root, ".lean-ts", "workspace")
  const sources = readSources(pkg.root).filter((s) => s.models.length !== 0)
  const descs = loadDescs(pkg, sources)
  rmSync(join(ws, "LeanTsLib"), { recursive: true, force: true })
  cpSync(join(libDir(), "LeanTsLib"), join(ws, "LeanTsLib"), { recursive: true })
  writeFileSync(join(ws, "LeanTsLib.lean"), "import LeanTsLib.Ts\n")
  rmSync(join(ws, "LeanTsModel"), { recursive: true, force: true })
  rmSync(join(ws, "Proofs"), { recursive: true, force: true })
  const proofsSrc = join(pkg.root, "lean", "Proofs")
  if (existsSync(proofsSrc)) cpSync(proofsSrc, join(ws, "Proofs"), { recursive: true })
  else mkdirSync(join(ws, "Proofs"), { recursive: true })
  writeFileSync(join(ws, "Proofs", "Empty.lean"), "")
  writeFileSync(
    join(ws, "lakefile.toml"),
    readFileSync(join(ws, "lakefile.toml"), "utf8") + LAKEFILE_EXTRA,
  )
  const refs: { m: ModelCall; label: string; lean: string }[] = []
  const modelModules: string[] = []
  const hashes = new Map<string, string>()
  const candidates = new Map<string, Csimp>()
  for (const src of sources) {
    const types = typeResolver(pkg, src, summaries, descs)
    const fns = src.models.map((m) => new Fn(m.fn, m.fnNode, src, types))
    const seen = new Set<string>()
    for (const m of src.models) {
      if (seen.has(m.fn))
        throw new SyncError(`${src.where(m.at)}: ${m.fn} has two model(...) calls`, 252)
      seen.add(m.fn)
    }
    const tr = new Translator(fns, types)
    const defs = tr.definitions()
    const parts = modelModule(src.module)
    const ns = leanName(parts)
    const imports = new Set(["LeanTsLib"])
    for (const i of src.imports.values()) {
      const b = blockOf(pkg, i.from)
      if (b !== undefined) imports.add(leanName(b.leanModule))
    }
    const body: string[] = []
    src.models.forEach((m, k) => {
      const fn = fns[k]
      if (fn === undefined) return
      const modes = fn.params.map((p) => modeOf(p.type))
      const target = `ts:${m.module}#${m.fn}(${modes.map((x) => (x === "mixed" ? "_" : x)).join(",")})`
      body.push(
        `/-- \`${m.module}\` ${m.fn}, translated from TypeScript. -/\n@[extern ${JSON.stringify(target)}]\n${defs.get(m.fn) ?? ""}`,
      )
      if (m.refines !== undefined && m.requires === undefined && !modes.includes("mixed")) {
        const n = specName(pkg, src, m.refines, summaries)
        candidates.set(qualified(m), { spec: n.lean, module: n.module, modes })
      }
      const o = obligations(m, fn, pkg, src, summaries)
      for (const i of o.imports) imports.add(i)
      for (const [label, prop] of o.props) {
        body.push(`abbrev ${ident(m.fn)}.obligation.${label} : Prop :=\n  ${prop}`)
        refs.push({ m, label, lean: `${parts.join(".")}.${m.fn}` })
      }
      hashes.set(qualified(m), specHash(pkg, src, m))
    })
    const text =
      [...imports]
        .toSorted()
        .map((i) => `import ${i}\n`)
        .join("") + `\nnamespace ${ns}\n\n${body.join("\n\n")}\n\nend ${ns}\n`
    const file = moduleFileOf(ws, parts)
    mkdirSync(dirname(file), { recursive: true })
    writeFileSync(file, text)
    modelModules.push(ns)
  }
  writeFileSync(
    join(ws, "LeanTsModel.lean"),
    modelModules.map((m) => `import ${m}\n`).join("") || "\n",
  )
  const proofModules = leanFiles(join(ws, "Proofs")).map((p) =>
    relative(ws, p)
      .replace(/\.lean$/u, "")
      .split(sep)
      .map((c) => (/^[A-Za-z_][A-Za-z0-9_]*$/u.test(c) ? c : `«${c}»`))
      .join("."),
  )
  writeFileSync(join(ws, "Proofs.lean"), proofModules.map((m) => `import ${m}\n`).join(""))
  const lake = process.env["LAKE"] ?? "lake"
  const built = run(lake, ["build", "LeanTsLib", "LeanTsModel"], ws)
  if (built.status !== 0) {
    log(built.stdout + built.stderr)
    throw new SyncError("lake build of the translated functions failed", 254)
  }
  const failedText: string[] = []
  const okProofs: string[] = []
  for (const m of proofModules) {
    const r = run(lake, ["build", m], ws)
    if (r.status === 0) {
      okProofs.push(m)
      continue
    }
    failedText.push(
      readFileSync(join(ws, `${m.replaceAll(/[«»]/gu, "").split(".").join("/")}.lean`), "utf8"),
    )
    for (const line of (r.stdout + r.stderr).split("\n"))
      if (/^(error:|  |⊢|case )/u.test(line) || line.includes(": error")) log(`lean-ts: ${line}`)
  }
  const oblFile = join(ws, "obligations.json")
  writeFileSync(oblFile, JSON.stringify(refs.map((r) => ({ model: r.lean, label: r.label }))))
  let results: unknown[] = []
  if (refs.length !== 0) {
    const r = run(cli, [
      "obligations",
      "check",
      "--search-path",
      join(ws, ".lake", "build", "lib", "lean"),
      "--obligations",
      oblFile,
      "--modules",
      ...modelModules.map((m) => m.replaceAll(/[«»]/gu, "")),
      ...okProofs.map((m) => m.replaceAll(/[«»]/gu, "")),
    ])
    if (r.status !== 0) {
      log(r.stderr)
      throw new SyncError("lean-typescript obligations check failed", r.status)
    }
    const parsed: unknown = JSON.parse(r.stdout)
    if (!Array.isArray(parsed) || parsed.length !== refs.length)
      throw new SyncError("lean-typescript obligations check returned an unexpected result", 255)
    results = parsed
  }
  const lock: Record<
    string,
    { spec_hash: string; lean: string; obligations: Record<string, Status>; csimp?: Csimp }
  > = {}
  const rows: Row[] = []
  refs.forEach((ref, k) => {
    const res = results[k]
    const raw = isRecord(res) ? res["status"] : undefined
    if (!isStatus(raw))
      throw new SyncError(
        `lean-typescript obligations check returned no status for ${ref.lean} ${ref.label}`,
        255,
      )
    let status: Status = raw
    if (
      status === "missing" &&
      failedText.some((t) => t.includes(`${ref.m.fn}.proof.${ref.label}`))
    )
      status = "failed"
    if (isRecord(res) && typeof res["detail"] === "string" && status === "mismatch")
      log(`lean-ts: ${res["detail"]}`)
    const q = qualified(ref.m)
    const entry = lock[q] ?? { spec_hash: hashes.get(q) ?? "", lean: ref.lean, obligations: {} }
    entry.obligations[ref.label] = status
    const cand = candidates.get(q)
    if (ref.label === "refines" && status === "proved" && cand !== undefined) entry.csimp = cand
    lock[q] = entry
    rows.push({ fn: q, label: ref.label, status })
  })
  const sorted = Object.fromEntries(Object.entries(lock).toSorted(([a], [b]) => a.localeCompare(b)))
  writeFileSync(lockFile(pkg.root), JSON.stringify(sorted, null, 2) + "\n")
  if (canonicalJson(Object.fromEntries(csimpFiles(pkg))) !== before)
    await syncPackage(dir, cliPath, log, csimpFiles)
  return { rows, lock: sorted }
}

function modeOf(t: TsType): "n" | "_" | "mixed" {
  const kinds = new Set<string>()
  const walk = (x: TsType): void => {
    if (x.k === "num" || x.k === "big") kinds.add(x.k)
    else if (x.k === "list" || x.k === "opt") walk(x.item)
    else if (x.k === "tuple") x.items.forEach(walk)
    else if (x.k === "struct") x.fields.forEach((f) => walk(f.type))
    else if (x.k === "ind") x.variants.forEach((v) => v.fields.forEach((f) => walk(f.type)))
  }
  walk(t)
  if (kinds.has("num") && kinds.has("big")) return "mixed"
  return kinds.has("num") ? "n" : "_"
}

export function csimpFiles(pkg: Package): Map<string, string> {
  const lock = readLock(pkg.root)
  const out = new Map<string, string>()
  for (const src of readSources(pkg.root)) {
    const parts = ["LeanTsCsimp", ...moduleParts(src.module)]
    const ns = leanName(parts)
    const imports = new Set<string>()
    const defs: string[] = []
    for (const m of src.models) {
      const e = lock[qualified(m)]
      if (e?.csimp === undefined || e.obligations["refines"] !== "proved") continue
      if (e.spec_hash !== specHash(pkg, src, m)) continue
      imports.add(e.csimp.module)
      const target = `ts:${m.module}#${m.fn}(${e.csimp.modes.join(",")})`
      defs.push(
        `@[extern ${JSON.stringify(target)}]\ndef ${ident(m.fn)} := @_root_.${e.csimp.spec}\n\n@[csimp] theorem ${ident(m.fn)}.csimp : @_root_.${e.csimp.spec} = @${ident(m.fn)} := rfl`,
      )
    }
    if (defs.length === 0) continue
    out.set(
      `${parts.join("/")}.lean`,
      [...imports]
        .toSorted()
        .map((i) => `import ${i}\n`)
        .join("") + `\nnamespace ${ns}\n\n${defs.join("\n\n")}\n\nend ${ns}\n`,
    )
  }
  return out
}

export function statusModels(pkg: Package): Row[] {
  const lock = readLock(pkg.root)
  const rows: Row[] = []
  for (const src of readSources(pkg.root)) {
    for (const m of src.models) {
      const q = qualified(m)
      const entry = lock[q]
      const types = typeResolver(pkg, src, undefined, undefined)
      const fn = new Fn(m.fn, m.fnNode, src, types)
      const labels = [
        ...(m.refines === undefined ? [] : ["refines"]),
        ...m.ensures.map(([l]) => l),
        ...(fn.retNat ? ["returnsNat"] : []),
      ]
      const stale = entry === undefined || entry.spec_hash !== specHash(pkg, src, m)
      for (const label of labels) {
        const st = entry?.obligations[label]
        rows.push({ fn: q, label, status: stale || st === undefined ? "stale" : st })
      }
    }
  }
  return rows
}
