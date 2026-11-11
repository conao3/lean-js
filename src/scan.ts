import { readdirSync, readFileSync } from "node:fs"
import { dirname, join, relative, resolve, sep } from "node:path"
import {
  type Argument,
  type CallExpression,
  type Expression,
  type ObjectExpression,
  parseSync,
  type PropertyKey,
  type TemplateLiteral,
  Visitor,
} from "oxc-parser"

export class SyncError extends Error {
  readonly code: number

  constructor(message: string, code: number) {
    super(message)
    this.name = "SyncError"
    this.code = code
  }
}

export interface Position {
  readonly line: number
  readonly col: number
}

export interface ModelBinding {
  readonly name: string
  readonly from: string
  readonly exportName: string
}

export interface ScannedBlock {
  readonly file: string
  readonly module: string
  readonly name: string
  readonly source: string
  readonly imports: readonly string[]
  readonly uses: readonly string[]
  readonly output: Readonly<Record<string, string>>
  readonly modelNames: readonly string[]
  readonly models: readonly ModelBinding[]
  readonly at: Position
  readonly sourceAt: Position
}

function lineStarts(text: string): number[] {
  const starts = [0]
  for (let i = 0; i < text.length; i++) if (text[i] === "\n") starts.push(i + 1)
  return starts
}

function position(starts: readonly number[], offset: number): Position {
  let lo = 0
  let hi = starts.length - 1
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1
    if ((starts[mid] ?? 0) <= offset) lo = mid
    else hi = mid - 1
  }
  return { line: lo + 1, col: offset - (starts[lo] ?? 0) + 1 }
}

function normalizeNewlines(s: string): string {
  return s.replaceAll("\r\n", "\n").replaceAll("\r", "\n")
}

export function tsFiles(dir: string): string[] {
  const out: string[] = []
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name)
    if (e.isDirectory()) {
      if (e.name !== "_lean" && e.name !== "node_modules") out.push(...tsFiles(p))
    } else if (e.name.endsWith(".ts") && !e.name.endsWith(".d.ts")) out.push(p)
  }
  return out.toSorted()
}

export function posixRelative(root: string, file: string): string {
  return relative(root, file).split(sep).join("/")
}

function keyName(k: PropertyKey, computed: boolean): string | undefined {
  if (computed) return undefined
  if (k.type === "Identifier") return k.name
  if (k.type === "Literal" && typeof k.value === "string") return k.value
  return undefined
}

function templateText(t: TemplateLiteral, raw: boolean): string | undefined {
  const q = t.quasis[0]
  if (t.expressions.length !== 0 || q === undefined) return undefined
  const text = raw ? q.value.raw : q.value.cooked
  return text === null ? undefined : normalizeNewlines(text)
}

function isStringRaw(e: Expression): boolean {
  return (
    e.type === "MemberExpression" &&
    !e.computed &&
    e.object.type === "Identifier" &&
    e.object.name === "String" &&
    e.property.type === "Identifier" &&
    e.property.name === "raw"
  )
}

function staticString(e: Argument | null): string | undefined {
  if (e === null) return undefined
  if (e.type === "Literal" && typeof e.value === "string") return e.value
  if (e.type === "TemplateLiteral") return templateText(e, false)
  return undefined
}

export function scanFile(root: string, file: string): ScannedBlock[] {
  const text = readFileSync(file, "utf8")
  const starts = lineStarts(text)
  const module = posixRelative(root, file)
  const fail = (offset: number, msg: string): never => {
    const p = position(starts, offset)
    throw new SyncError(`${file}:${p.line}:${p.col}: ${msg}`, 252)
  }
  const parsed = parseSync(file, text, { lang: "ts", sourceType: "module" })
  const firstError = parsed.errors[0]
  if (firstError !== undefined) {
    const label = firstError.labels[0]
    fail(label?.start ?? 0, `cannot parse: ${firstError.message}`)
  }
  const direct = new Set<string>()
  const namespaces = new Set<string>()
  const bindings = new Map<string, { readonly from: string; readonly exportName: string | null }>()
  const exported = new Set<string>()
  const fromSpec = (spec: string): string =>
    spec.startsWith(".") ? resolve(dirname(file), spec) : spec
  for (const s of parsed.program.body) {
    if (s.type === "ImportDeclaration") {
      for (const sp of s.specifiers) {
        if (sp.type === "ImportNamespaceSpecifier")
          bindings.set(sp.local.name, { from: fromSpec(s.source.value), exportName: null })
        else if (sp.type === "ImportSpecifier")
          bindings.set(sp.local.name, {
            from: fromSpec(s.source.value),
            exportName: sp.imported.type === "Literal" ? sp.imported.value : sp.imported.name,
          })
      }
    } else if (s.type === "ExportNamedDeclaration") {
      const d = s.declaration
      if (d?.type === "VariableDeclaration")
        for (const x of d.declarations) if (x.id.type === "Identifier") exported.add(x.id.name)
      if ((d?.type === "FunctionDeclaration" || d?.type === "ClassDeclaration") && d.id !== null)
        exported.add(d.id.name)
      if (s.source === null)
        for (const sp of s.specifiers)
          if (
            sp.local.type === "Identifier" &&
            sp.exported.type === "Identifier" &&
            sp.local.name === sp.exported.name
          )
            exported.add(sp.local.name)
    }
  }
  const binding = (name: string, e: Expression): ModelBinding => {
    if (e.type === "Identifier") {
      const i = bindings.get(e.name)
      if (i !== undefined && i.exportName !== null)
        return { name, from: i.from, exportName: i.exportName }
      if (exported.has(e.name)) return { name, from: file, exportName: e.name }
    } else if (
      e.type === "MemberExpression" &&
      !e.computed &&
      e.object.type === "Identifier" &&
      e.property.type === "Identifier"
    ) {
      const i = bindings.get(e.object.name)
      if (i !== undefined && i.exportName === null)
        return { name, from: i.from, exportName: e.property.name }
    }
    return fail(
      e.start,
      `the model ${name} must be an exported variable of the module, a named import or a property of a namespace import`,
    )
  }
  for (const s of parsed.program.body) {
    if (s.type !== "ImportDeclaration" || s.source.value !== "lean-ts" || s.importKind === "type")
      continue
    for (const sp of s.specifiers) {
      if (sp.type === "ImportNamespaceSpecifier") namespaces.add(sp.local.name)
      else if (sp.type === "ImportSpecifier" && sp.importKind !== "type") {
        const imported = sp.imported.type === "Literal" ? sp.imported.value : sp.imported.name
        if (imported === "lean") direct.add(sp.local.name)
      }
    }
  }
  if (direct.size === 0 && namespaces.size === 0) return []
  const isLean = (c: CallExpression): boolean => {
    const f = c.callee
    if (f.type === "Identifier") return direct.has(f.name)
    return (
      f.type === "MemberExpression" &&
      !f.computed &&
      f.object.type === "Identifier" &&
      namespaces.has(f.object.name) &&
      f.property.type === "Identifier" &&
      f.property.name === "lean"
    )
  }
  const blocks: ScannedBlock[] = []
  const stringArray = (e: Expression, what: string): string[] => {
    if (e.type !== "ArrayExpression")
      return fail(e.start, `${what} must be an array literal of strings`)
    return e.elements.map(
      (x) => staticString(x) ?? fail(x?.start ?? e.start, `${what} must hold string literals`),
    )
  }
  const objectEntries = (e: ObjectExpression, what: string): [string, Expression, number][] =>
    e.properties.map((p) => {
      if (p.type !== "Property" || p.kind !== "init" || p.method)
        return fail(p.start, `${what} must be an object literal of plain properties`)
      const k = keyName(p.key, p.computed) ?? fail(p.start, `${what} must have literal keys`)
      return [k, p.value, p.start]
    })
  const readBlock = (c: CallExpression): ScannedBlock => {
    const [nameArg, sourceArg, optionsArg, ...rest] = c.arguments
    if (rest.length !== 0) fail(c.start, "lean(...) takes at most 3 arguments")
    const name =
      (nameArg?.type === "Literal" && typeof nameArg.value === "string"
        ? nameArg.value
        : undefined) ??
      fail(nameArg?.start ?? c.start, "the block name of lean(...) must be a string literal")
    let source: string | undefined
    let sourceStart = 0
    if (sourceArg?.type === "TemplateLiteral") {
      source = templateText(sourceArg, false)
      sourceStart = sourceArg.start + 1
    } else if (sourceArg?.type === "TaggedTemplateExpression" && isStringRaw(sourceArg.tag)) {
      source = templateText(sourceArg.quasi, true)
      sourceStart = sourceArg.quasi.start + 1
    }
    if (source === undefined)
      return fail(
        sourceArg?.start ?? c.start,
        "the Lean source of lean(...) must be a template literal or String.raw`...` without ${}",
      )
    let imports: string[] = []
    let uses: string[] = []
    const output: Record<string, string> = {}
    const modelNames: string[] = []
    const models: ModelBinding[] = []
    if (optionsArg !== undefined) {
      if (optionsArg.type !== "ObjectExpression")
        return fail(optionsArg.start, "the options of lean(...) must be an object literal")
      for (const [k, v, at] of objectEntries(optionsArg, "the options of lean(...)")) {
        if (k === "imports") imports = stringArray(v, "imports")
        else if (k === "uses") uses = stringArray(v, "uses")
        else if (k === "models") {
          if (v.type !== "ObjectExpression")
            return fail(v.start, "models must be an object literal")
          for (const [m, mv] of objectEntries(v, "models")) {
            modelNames.push(m)
            models.push(binding(m, mv))
          }
        } else if (k === "output") {
          if (v.type !== "ObjectExpression")
            return fail(v.start, "output must be an object literal")
          for (const [o, ov, oat] of objectEntries(v, "output")) {
            if (o !== "tagKey" && o !== "option") return fail(oat, `unknown output setting ${o}`)
            output[o] = staticString(ov) ?? fail(ov.start, `output.${o} must be a string literal`)
          }
        } else return fail(at, `unknown option ${k} of lean(...)`)
      }
    }
    return {
      file,
      module,
      name,
      source,
      imports,
      uses,
      output,
      modelNames,
      models,
      at: position(starts, c.start),
      sourceAt: position(starts, sourceStart),
    }
  }
  new Visitor({
    CallExpression(c) {
      if (isLean(c)) blocks.push(readBlock(c))
    },
  }).visit(parsed.program)
  return blocks
}
