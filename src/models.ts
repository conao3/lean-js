import { canonicalJson, type Json } from "./key.ts"
import { SyncError } from "./scan.ts"

const LEAN_KEYWORDS: ReadonlySet<string> = new Set([
  "at",
  "by",
  "do",
  "else",
  "end",
  "fun",
  "have",
  "if",
  "in",
  "let",
  "match",
  "mut",
  "namespace",
  "open",
  "section",
  "then",
  "theorem",
  "def",
  "structure",
  "inductive",
  "where",
  "with",
  "from",
  "import",
  "instance",
  "class",
  "variable",
  "universe",
  "deriving",
  "show",
  "calc",
  "for",
  "return",
  "try",
  "catch",
  "finally",
  "unless",
  "break",
  "continue",
  "macro",
  "syntax",
  "local",
  "private",
  "protected",
  "partial",
  "unsafe",
  "noncomputable",
  "abbrev",
  "example",
  "axiom",
  "opaque",
  "extends",
  "notation",
  "Type",
  "Sort",
  "Prop",
])

const IDENT = /^[A-Za-z_][A-Za-z0-9_']*$/u

const ANNOTATIONS: ReadonlySet<string> = new Set([
  "$schema",
  "$id",
  "$comment",
  "$defs",
  "definitions",
  "id",
  "title",
  "description",
  "default",
  "examples",
  "readOnly",
  "writeOnly",
  "deprecated",
])

const UNMAPPED: ReadonlySet<string> = new Set([
  "multipleOf",
  "pattern",
  "format",
  "uniqueItems",
  "contentEncoding",
  "contentMediaType",
])

export function leanIdent(s: string): string {
  return IDENT.test(s) && !LEAN_KEYWORDS.has(s) ? s : `«${s}»`
}

function leanIdentWithSuffix(s: string, suffix: string): string {
  return IDENT.test(s) && !LEAN_KEYWORDS.has(s) ? `${s}${suffix}` : `«${s}${suffix}»`
}

type Schema = Readonly<Record<string, Json>>

function isSchema(v: Json | undefined): v is Schema {
  return typeof v === "object" && v !== null && !Array.isArray(v)
}

interface FieldType {
  readonly lean: string
  readonly nat: boolean
  readonly kind: "integer" | "number" | "string" | "array" | "other"
  readonly item?: { readonly schema: Schema; readonly type: FieldType }
}

interface Context {
  readonly module: string
  readonly model: string
  readonly root: Schema
  readonly models: ReadonlyMap<string, Schema>
  readonly enumsNs: string
  readonly modelsNs: string
  readonly enums: Map<string, readonly string[]>
  readonly structs: Map<string, StructSource>
  readonly unmapped: string[]
  readonly deps: Set<string>
}

interface StructSource {
  readonly name: string
  readonly doc: string
  readonly fields: readonly string[]
  readonly deps: ReadonlySet<string>
}

function fail(cx: Context, path: string, msg: string): never {
  throw new SyncError(
    `${cx.module}: the model ${cx.model}${path === "" ? "" : `.${path}`}: ${msg}`,
    254,
  )
}

function numberLit(v: number, nat: boolean, kind: FieldType["kind"]): string {
  if (kind === "number") return `(${Number.isInteger(v) ? `${v}.0` : String(v)} : Float)`
  if (nat) return String(v)
  return `(${v} : Int)`
}

function checkKeys(cx: Context, path: string, s: Schema, allowed: readonly string[]): void {
  for (const k of Object.keys(s)) {
    if (allowed.includes(k) || ANNOTATIONS.has(k)) continue
    if (UNMAPPED.has(k)) {
      cx.unmapped.push(`${path} ${k} ${canonicalJson(s[k])}`)
      continue
    }
    fail(cx, path, `the JSON Schema keyword ${k} cannot be mapped to Lean`)
  }
}

function withoutSchemaUri(s: Schema): string {
  const { $schema: _, ...rest } = s
  return canonicalJson(rest)
}

function equalModel(cx: Context, s: Schema): string | undefined {
  const c = withoutSchemaUri(s)
  for (const [name, m] of cx.models) if (withoutSchemaUri(m) === c) return name
  return undefined
}

function resolveRef(
  cx: Context,
  path: string,
  ref: string,
): { readonly schema: Schema; readonly name: string } {
  if (ref === "#") return { schema: cx.root, name: cx.model }
  const m = /^#\/(?:\$defs|definitions)\/([^/]+)$/u.exec(ref)
  const key = m?.[1]
  if (key === undefined) return fail(cx, path, `the $ref ${ref} is not a local definition`)
  const defs = cx.root["$defs"] ?? cx.root["definitions"]
  const def = isSchema(defs) ? defs[key] : undefined
  if (!isSchema(def)) return fail(cx, path, `the $ref ${ref} has no definition`)
  return { schema: def, name: key }
}

function nullable(s: Schema): Schema | undefined {
  const any = s["anyOf"]
  if (Array.isArray(any) && any.length === 2) {
    const items = any.filter(isSchema)
    const nulls = items.filter((x) => x["type"] === "null")
    const others = items.filter((x) => x["type"] !== "null")
    const other = others[0]
    if (nulls.length === 1 && other !== undefined && others.length === 1) {
      const { anyOf: _, ...rest } = s
      return { ...rest, ...other }
    }
  }
  const t = s["type"]
  if (Array.isArray(t) && t.length === 2 && t.includes("null")) {
    const other = t.find((x) => x !== "null")
    if (typeof other === "string") return { ...s, type: other }
  }
  return undefined
}

function enumType(cx: Context, path: string, name: string, values: readonly Json[]): string {
  const strings = values.filter((v): v is string => typeof v === "string")
  if (strings.length !== values.length || strings.length === 0)
    return fail(cx, path, "an enum must list strings")
  const prev = cx.enums.get(name)
  if (prev !== undefined && canonicalJson(prev) !== canonicalJson(strings))
    return fail(cx, path, `the enum ${name} is defined twice`)
  cx.enums.set(name, strings)
  return `${cx.enumsNs}.${leanIdent(name)}`
}

function structRef(cx: Context, name: string): string {
  cx.deps.add(name)
  return leanIdent(name)
}

function fieldType(cx: Context, path: string, s: Schema, hint: string): FieldType {
  const ref = s["$ref"]
  if (typeof ref === "string") {
    const r = resolveRef(cx, path, ref)
    if (r.name === cx.model && r.schema === cx.root)
      return { lean: structRef(cx, cx.model), nat: false, kind: "other" }
    const other = equalModel(cx, r.schema)
    if (other !== undefined) return { lean: structRef(cx, other), nat: false, kind: "other" }
    return {
      lean: nestedStruct(cx, path, `${cx.model}_${r.name}`, r.schema),
      nat: false,
      kind: "other",
    }
  }
  const e = s["enum"]
  if (Array.isArray(e)) {
    checkKeys(cx, path, s, ["enum", "type"])
    return { lean: enumType(cx, path, `${cx.model}_${hint}`, e), nat: false, kind: "other" }
  }
  const c = s["const"]
  if (typeof c === "string") {
    checkKeys(cx, path, s, ["const", "type"])
    return { lean: enumType(cx, path, `${cx.model}_${hint}`, [c]), nat: false, kind: "other" }
  }
  switch (s["type"]) {
    case "integer": {
      const lo = lowerBound(s)
      const nat = lo !== undefined && lo >= 0
      return { lean: nat ? "Nat" : "Int", nat, kind: "integer" }
    }
    case "number":
      return { lean: "Float", nat: false, kind: "number" }
    case "string":
      return { lean: "String", nat: false, kind: "string" }
    case "boolean":
      checkKeys(cx, path, s, ["type", "const"])
      return { lean: "Bool", nat: false, kind: "other" }
    case "array": {
      const items = s["items"]
      if (!isSchema(items)) return fail(cx, path, "an array needs an items schema")
      const inner = fieldType(cx, `${path}[]`, items, hint)
      return {
        lean: `List ${paren(inner.lean)}`,
        nat: false,
        kind: "array",
        item: { schema: items, type: inner },
      }
    }
    case "object": {
      const other = equalModel(cx, s)
      if (other !== undefined) return { lean: structRef(cx, other), nat: false, kind: "other" }
      return { lean: nestedStruct(cx, path, `${cx.model}_${hint}`, s), nat: false, kind: "other" }
    }
    default:
      return fail(cx, path, `the schema ${canonicalJson(s)} cannot be mapped to Lean`)
  }
}

function paren(t: string): string {
  return t.includes(" ") ? `(${t})` : t
}

function lowerBound(s: Schema): number | undefined {
  const min = s["minimum"]
  const ex = s["exclusiveMinimum"]
  if (typeof min === "number") return min
  if (typeof ex === "number") return Math.floor(ex) + 1
  return undefined
}

interface Proof {
  readonly suffix: string
  readonly prop: (v: string) => string
}

function proofsOf(cx: Context, path: string, s: Schema, t: FieldType): Proof[] {
  const out: Proof[] = []
  const lit = (v: number): string => numberLit(v, t.nat, t.kind)
  if (t.kind === "integer" || t.kind === "number") {
    checkKeys(cx, path, s, [
      "type",
      "minimum",
      "maximum",
      "exclusiveMinimum",
      "exclusiveMaximum",
      "const",
    ])
    const num = (k: string): number | undefined => {
      const v = s[k]
      return typeof v === "number" ? v : undefined
    }
    const min = num("minimum")
    const max = num("maximum")
    const exMin = num("exclusiveMinimum")
    const exMax = num("exclusiveMaximum")
    if (min !== undefined && !(t.nat && min === 0))
      out.push({ suffix: "ge", prop: (v) => `${lit(min)} ≤ ${v}` })
    if (exMin !== undefined) out.push({ suffix: "gt", prop: (v) => `${lit(exMin)} < ${v}` })
    if (max !== undefined) out.push({ suffix: "le", prop: (v) => `${v} ≤ ${lit(max)}` })
    if (exMax !== undefined) out.push({ suffix: "lt", prop: (v) => `${v} < ${lit(exMax)}` })
    const c = s["const"]
    if (typeof c === "number") out.push({ suffix: "eq", prop: (v) => `${v} = ${lit(c)}` })
  } else if (t.kind === "string" || t.kind === "array") {
    const lenKeys = t.kind === "string" ? ["minLength", "maxLength"] : ["minItems", "maxItems"]
    checkKeys(cx, path, s, ["type", "items", ...lenKeys])
    const [minK, maxK] = lenKeys
    const minV = minK === undefined ? undefined : s[minK]
    const maxV = maxK === undefined ? undefined : s[maxK]
    if (typeof minV === "number" && minV > 0)
      out.push({
        suffix: t.kind === "string" ? "min_length" : "min_items",
        prop: (v) => `${minV} ≤ ${v}.length`,
      })
    if (typeof maxV === "number")
      out.push({
        suffix: t.kind === "string" ? "max_length" : "max_items",
        prop: (v) => `${v}.length ≤ ${maxV}`,
      })
    if (t.item !== undefined)
      for (const p of proofsOf(cx, `${path}[]`, t.item.schema, t.item.type))
        out.push({
          suffix: `items_${p.suffix}`,
          prop: (v) => `(${v}.all fun v => decide (${p.prop("v")})) = true`,
        })
  }
  return out
}

function nestedStruct(cx: Context, path: string, name: string, s: Schema): string {
  const prev = cx.structs.get(name)
  if (prev === undefined) {
    const sub: Context = { ...cx, model: name, deps: new Set(), unmapped: [] }
    cx.structs.set(name, { name, doc: "", fields: [], deps: new Set() })
    cx.structs.set(name, structSource(sub, s, `A part of the model ${cx.model} of ${cx.module}.`))
  }
  return structRef(cx, name)
}

function structSource(cx: Context, s: Schema, doc: string): StructSource {
  checkKeys(cx, "", s, ["type", "properties", "required", "additionalProperties"])
  if (s["type"] !== "object") fail(cx, "", "the schema of a model must be an object")
  const additional = s["additionalProperties"]
  if (
    additional !== undefined &&
    additional !== false &&
    !(isSchema(additional) && Object.keys(additional).length === 0)
  )
    fail(cx, "", "additionalProperties with a schema cannot be mapped to Lean")
  const props = s["properties"]
  const properties = isSchema(props) ? props : {}
  const req = s["required"]
  const required = new Set(Array.isArray(req) ? req.filter((x) => typeof x === "string") : [])
  const fields: string[] = []
  for (const [key, raw] of Object.entries(properties)) {
    if (!isSchema(raw)) fail(cx, key, "the property schema is not an object")
    const inner = nullable(raw)
    const option = inner !== undefined || !required.has(key)
    const target = inner ?? raw
    const t = fieldType(cx, key, target, key)
    const proofs = proofsOf(cx, key, target, t)
    const name = required.has(key) ? leanIdent(key) : leanIdentWithSuffix(key, "?")
    fields.push(`  ${name} : ${option ? `Option ${paren(t.lean)}` : t.lean}`)
    for (const p of proofs) {
      const prop = option ? `(${name}.all fun v => decide (${p.prop("v")})) = true` : p.prop(name)
      fields.push(`  ${leanIdentWithSuffix(key, `_${p.suffix}`)} : ${prop}`)
    }
  }
  const unmapped =
    cx.unmapped.length === 0 ? "" : ` Not assumed in Lean: ${cx.unmapped.join(", ")}.`
  return { name: cx.model, doc: `${doc}${unmapped}`, fields, deps: new Set(cx.deps) }
}

export interface ModelsSource {
  readonly lean: string
  readonly names: readonly string[]
}

function order(structs: ReadonlyMap<string, StructSource>, module: string): StructSource[] {
  const out: StructSource[] = []
  const state = new Map<string, "visiting" | "done">()
  const visit = (name: string): void => {
    const st = state.get(name)
    if (st === "done") return
    if (st === "visiting")
      throw new SyncError(
        `${module}: the models refer to each other in a cycle through ${name}`,
        254,
      )
    const s = structs.get(name)
    if (s === undefined) return
    state.set(name, "visiting")
    for (const d of s.deps) if (d !== name) visit(d)
    state.set(name, "done")
    out.push(s)
  }
  for (const name of structs.keys()) visit(name)
  return out
}

export function modelsLean(
  module: string,
  namespace: readonly string[],
  models: ReadonlyMap<string, Json>,
): ModelsSource {
  const schemas = new Map<string, Schema>()
  for (const [name, schema] of models) {
    if (!isSchema(schema))
      throw new SyncError(`${module}: the model ${name} is not an object schema`, 254)
    schemas.set(name, schema)
  }
  const ns = namespace.map((p) => `«${p}»`).join(".")
  const enumsNs = `LeanTsEnums.${ns}`
  const modelsNs = `LeanTsModels.${ns}`
  const enums = new Map<string, readonly string[]>()
  const structs = new Map<string, StructSource>()
  for (const [name, root] of schemas) {
    const cx: Context = {
      module,
      model: name,
      root,
      models: schemas,
      enumsNs,
      modelsNs,
      enums,
      structs,
      unmapped: [],
      deps: new Set(),
    }
    structs.set(name, { name, doc: "", fields: [], deps: new Set() })
    structs.set(name, structSource(cx, root, `The model ${name} of ${module}.`))
  }
  const enumSrc = [...enums]
    .map(
      ([name, values]) =>
        `inductive ${leanIdent(name)} where\n${values.map((v) => `  | ${leanIdent(v)}`).join("\n")}\n  deriving DecidableEq, Repr\n`,
    )
    .join("\n")
  const structSrc = order(structs, module)
    .map(
      (s) =>
        `/-- ${s.doc.replaceAll("-/", "- /")} -/\nstructure ${leanIdent(s.name)} where\n${s.fields.join("\n")}\n`,
    )
    .join("\n")
  const lean =
    (enums.size === 0 ? "" : `namespace ${enumsNs}\n\n${enumSrc}\nend ${enumsNs}\n\n`) +
    `namespace ${modelsNs}\n\n${structSrc}\nend ${modelsNs}\n`
  return { lean, names: [...schemas.keys()] }
}
