import type {
  ArrowFunctionExpression,
  BindingPattern,
  CallExpression,
  Expression,
  Function as FunctionNode,
  ParamPattern,
  Statement,
  TSType,
} from "oxc-parser"
import { SyncError } from "../scan.ts"

export interface FieldType {
  readonly key: string
  readonly lean: string
  readonly type: TsType
  readonly nat: boolean
}

export interface VariantType {
  readonly name: string
  readonly fields: readonly FieldType[]
}

export type TsType =
  | { readonly k: "num" }
  | { readonly k: "big" }
  | { readonly k: "bool" }
  | { readonly k: "str" }
  | { readonly k: "list"; readonly item: TsType }
  | { readonly k: "tuple"; readonly items: readonly TsType[] }
  | { readonly k: "opt"; readonly item: TsType; readonly absent: "null" | "undefined" }
  | {
      readonly k: "struct"
      readonly lean: string
      readonly ts: string
      readonly fields: readonly FieldType[]
    }
  | {
      readonly k: "enum"
      readonly lean: string
      readonly ts: string
      readonly ctors: readonly string[]
    }
  | {
      readonly k: "ind"
      readonly lean: string
      readonly ts: string
      readonly tagKey: string
      readonly variants: readonly VariantType[]
    }

export const NUM: TsType = { k: "num" }
export const BIG: TsType = { k: "big" }
export const BOOL: TsType = { k: "bool" }
export const STR: TsType = { k: "str" }

export class TranslateError extends SyncError {
  constructor(message: string) {
    super(message, 254)
    this.name = "TranslateError"
  }
}

export interface Param {
  readonly name: string
  readonly type: TsType
  readonly nat: boolean
}

export interface Located {
  readonly file: string
  readonly where: (offset: number) => string
}

export interface TypeResolver {
  readonly reference: (
    name: string,
    qualifier: string | undefined,
    at: number,
  ) => TsType | undefined
}

export class Fn {
  readonly name: string
  readonly node: FunctionNode | ArrowFunctionExpression
  readonly params: readonly Param[]
  readonly ret: TsType
  readonly retNat: boolean
  readonly src: Located
  fails = false

  constructor(
    name: string,
    node: FunctionNode | ArrowFunctionExpression,
    src: Located,
    types: TypeResolver,
  ) {
    this.name = name
    this.node = node
    this.src = src
    const params: Param[] = []
    for (const p of node.params) params.push(paramOf(p, src, types, name))
    this.params = params
    const r = node.returnType?.typeAnnotation
    if (r === undefined || r === null)
      throw new TranslateError(`${src.where(node.start)}: ${name} has no return type annotation`)
    this.ret = tsType(r, src, types)
    this.retNat = isNat(r, types)
  }
}

function paramOf(p: ParamPattern, src: Located, types: TypeResolver, fn: string): Param {
  if (p.type !== "Identifier")
    throw new TranslateError(`${src.where(p.start)}: the parameters of ${fn} must be plain names`)
  const ann = p.typeAnnotation?.typeAnnotation
  if (ann === undefined || ann === null)
    throw new TranslateError(
      `${src.where(p.start)}: the parameter ${p.name} of ${fn} has no type annotation`,
    )
  return { name: p.name, type: tsType(ann, src, types), nat: isNat(ann, types) }
}

function isNat(t: TSType, types: TypeResolver): boolean {
  return (
    t.type === "TSTypeReference" &&
    t.typeName.type === "Identifier" &&
    t.typeName.name === "Nat" &&
    types.reference("Nat", undefined, t.start)?.k === "big"
  )
}

export function tsType(t: TSType, src: Located, types: TypeResolver): TsType {
  const bad = (): never => {
    throw new TranslateError(
      `${src.where(t.start)}: the type is outside the subset lean-ts translates`,
    )
  }
  switch (t.type) {
    case "TSNumberKeyword":
      return NUM
    case "TSBigIntKeyword":
      return BIG
    case "TSBooleanKeyword":
      return BOOL
    case "TSStringKeyword":
      return STR
    case "TSParenthesizedType":
      return tsType(t.typeAnnotation, src, types)
    case "TSArrayType":
      return { k: "list", item: tsType(t.elementType, src, types) }
    case "TSTypeOperator":
      return t.operator === "readonly" ? tsType(t.typeAnnotation, src, types) : bad()
    case "TSTupleType":
      return {
        k: "tuple",
        items: t.elementTypes.map((e) =>
          e.type === "TSOptionalType" || e.type === "TSRestType" ? bad() : tsType(e, src, types),
        ),
      }
    case "TSUnionType": {
      const rest = t.types.filter(
        (x) => x.type !== "TSNullKeyword" && x.type !== "TSUndefinedKeyword",
      )
      const only = rest[0]
      if (rest.length !== 1 || t.types.length !== 2 || only === undefined) return bad()
      return {
        k: "opt",
        item: tsType(only, src, types),
        absent: t.types.some((x) => x.type === "TSNullKeyword") ? "null" : "undefined",
      }
    }
    case "TSTypeReference": {
      const n = t.typeName
      const args = t.typeArguments?.params ?? []
      if (n.type === "Identifier") {
        const arg = args[0]
        if (
          (n.name === "Array" || n.name === "ReadonlyArray") &&
          args.length === 1 &&
          arg !== undefined
        )
          return { k: "list", item: tsType(arg, src, types) }
        if (args.length !== 0) return bad()
        return types.reference(n.name, undefined, t.start) ?? bad()
      }
      if (n.type === "TSQualifiedName" && n.left.type === "Identifier" && args.length === 0)
        return types.reference(n.right.name, n.left.name, t.start) ?? bad()
      return bad()
    }
    default:
      return bad()
  }
}

export function leanType(t: TsType): string {
  if (t.k === "num" || t.k === "big") return "Int"
  if (t.k === "bool") return "Bool"
  if (t.k === "str") return "String"
  if (t.k === "list") return `(List ${leanType(t.item)})`
  if (t.k === "tuple") return `(${t.items.map(leanType).join(" × ")})`
  if (t.k === "opt") return `(Option ${leanType(t.item)})`
  return `_root_.${t.lean}`
}

const LEAN_KEYWORDS = new Set([
  "at",
  "by",
  "do",
  "end",
  "else",
  "fun",
  "have",
  "if",
  "in",
  "let",
  "match",
  "mut",
  "then",
  "with",
  "return",
  "for",
  "from",
  "show",
  "where",
  "open",
  "namespace",
  "section",
  "def",
  "theorem",
  "structure",
  "inductive",
  "instance",
  "class",
  "abbrev",
  "import",
  "deriving",
  "unless",
  "break",
  "continue",
  "try",
  "catch",
  "finally",
  "local",
  "private",
  "protected",
  "partial",
  "variable",
  "universe",
  "macro",
  "syntax",
  "Type",
  "Prop",
  "Sort",
  "none",
  "some",
  "true",
  "false",
])

export function ident(name: string): string {
  return LEAN_KEYWORDS.has(name) || !/^[A-Za-z_][A-Za-z0-9_]*$/u.test(name) ? `«${name}»` : name
}

export function stringLit(s: string): string {
  let out = '"'
  for (const ch of s) {
    const c = ch.codePointAt(0) ?? 0
    if (ch === '"') out += '\\"'
    else if (ch === "\\") out += "\\\\"
    else if (ch === "\n") out += "\\n"
    else if (ch === "\t") out += "\\t"
    else if (ch === "\r") out += "\\r"
    else if (c < 0x20) out += `\\x${c.toString(16).padStart(2, "0")}`
    else out += ch
  }
  return out + '"'
}

function same(a: TsType, b: TsType): boolean {
  const key = (t: TsType): string =>
    JSON.stringify(t, (k, v: unknown) => (k === "absent" ? undefined : v))
  return key(a) === key(b)
}

function isInt(t: TsType): boolean {
  return t.k === "num" || t.k === "big"
}

interface Out {
  readonly c: string
  readonly t: TsType
}

interface Local {
  readonly t: TsType
  readonly mutable: boolean
  readonly local: boolean
}

type Scope = Map<string, Local>

const ERRORS = new Set(["Error", "RangeError", "TypeError"])

function tupleProj(base: string, i: number, n: number): string {
  let s = base
  for (let k = 0; k < i; k++) s = `${s}.2`
  return i < n - 1 ? `${s}.1` : s
}

function terminates(stmts: readonly Statement[]): boolean {
  const last = stmts[stmts.length - 1]
  if (last === undefined) return false
  if (last.type === "ReturnStatement" || last.type === "ThrowStatement") return true
  if (last.type === "BlockStatement") return terminates(last.body)
  if (last.type === "IfStatement")
    return last.alternate !== null && terminates([last.consequent]) && terminates([last.alternate])
  return false
}

function isNil(x: Expression): boolean {
  return (
    (x.type === "Literal" && x.value === null && x.raw === "null") ||
    (x.type === "Identifier" && x.name === "undefined")
  )
}

function nullCheck(e: Expression): { name: string; isNull: boolean } | undefined {
  if (e.type !== "BinaryExpression" || (e.operator !== "===" && e.operator !== "!=="))
    return undefined
  const name =
    e.left.type === "Identifier" && isNil(e.right)
      ? e.left.name
      : e.right.type === "Identifier" && isNil(e.left)
        ? e.right.name
        : undefined
  return name === undefined ? undefined : { name, isNull: e.operator === "===" }
}

export class Translator {
  readonly fns: ReadonlyMap<string, Fn>
  readonly types: TypeResolver

  constructor(fns: readonly Fn[], types: TypeResolver) {
    this.fns = new Map(fns.map((f) => [f.name, f]))
    this.types = types
  }

  definitions(): Map<string, string> {
    let out = new Map<string, string>()
    for (let round = 0; round <= this.fns.size + 1; round++) {
      const before = [...this.fns.values()].map((f) => f.fails).join()
      out = new Map([...this.fns.values()].map((f) => [f.name, this.definition(f)]))
      if ([...this.fns.values()].map((f) => f.fails).join() === before) return out
    }
    return out
  }

  private fail(fn: Fn, at: number, msg: string): never {
    throw new TranslateError(`${fn.src.where(at)}: ${fn.name}: ${msg}`)
  }

  definition(fn: Fn): string {
    const scope: Scope = new Map()
    const binders: string[] = []
    const prelude: string[] = []
    for (const p of fn.params) {
      scope.set(p.name, { t: p.type, mutable: false, local: false })
      if (p.nat) {
        binders.push(`(${ident(p.name)} : Nat)`)
        prelude.push(`  let ${ident(p.name)} : Int := ${ident(p.name)}`)
      } else binders.push(`(${ident(p.name)} : ${leanType(p.type)})`)
    }
    const body = fn.node.body
    if (body === null) this.fail(fn, fn.node.start, "has no body")
    const lines =
      body.type === "BlockStatement"
        ? this.block(fn, body.body, scope, 1)
        : [`  return ${this.expr(fn, body, scope, fn.ret).c}`]
    const ret = leanType(fn.ret)
    const head = fn.fails ? `Ts.M ${ret} := do` : `${ret} := Id.run do`
    return [`def ${ident(fn.name)} ${binders.join(" ")} : ${head}`, ...prelude, ...lines].join("\n")
  }

  private block(fn: Fn, stmts: readonly Statement[], scope: Scope, indent: number): string[] {
    const out: string[] = []
    const pad = "  ".repeat(indent)
    for (let i = 0; i < stmts.length; i++) {
      const s = stmts[i]
      if (s === undefined) continue
      if (s.type === "IfStatement") {
        const nc = nullCheck(s.test)
        const v = nc === undefined ? undefined : scope.get(nc.name)
        if (nc !== undefined && v !== undefined && v.t.k === "opt") {
          const inner = new Map(scope)
          inner.set(nc.name, { t: v.t.item, mutable: false, local: false })
          const someBranch = nc.isNull ? s.alternate : s.consequent
          const noneBranch = nc.isNull ? s.consequent : s.alternate
          const rest = stmts.slice(i + 1)
          const takeRest = nc.isNull && s.alternate === null && terminates([s.consequent])
          const someStmts = takeRest ? rest : someBranch === null ? [] : [someBranch]
          out.push(`${pad}match ${ident(nc.name)} with`)
          out.push(`${pad}| some ${ident(nc.name)} =>`)
          out.push(...this.nonEmpty(this.block(fn, someStmts, inner, indent + 1), indent + 1))
          out.push(`${pad}| none =>`)
          out.push(
            ...this.nonEmpty(
              noneBranch === null ? [] : this.block(fn, [noneBranch], new Map(scope), indent + 1),
              indent + 1,
            ),
          )
          if (takeRest) return out
          continue
        }
      }
      out.push(...this.stmt(fn, s, scope, indent))
    }
    return out
  }

  private nonEmpty(lines: string[], indent: number): string[] {
    return lines.length === 0 ? [`${"  ".repeat(indent)}pure ()`] : lines
  }

  private stmt(fn: Fn, s: Statement, scope: Scope, indent: number): string[] {
    const pad = "  ".repeat(indent)
    switch (s.type) {
      case "ReturnStatement": {
        if (s.argument === null) return this.fail(fn, s.start, "a function must return a value")
        return [`${pad}return ${this.expr(fn, s.argument, scope, fn.ret).c}`]
      }
      case "BlockStatement":
        return this.nonEmpty(this.block(fn, s.body, new Map(scope), indent), indent)
      case "EmptyStatement":
        return []
      case "VariableDeclaration": {
        if (s.kind !== "const" && s.kind !== "let")
          return this.fail(fn, s.start, `${s.kind} declarations are outside the subset`)
        return s.declarations.flatMap((d) => {
          if (d.init === null) return this.fail(fn, d.start, "a variable needs an initial value")
          return this.declareVar(fn, d.id, d.init, scope, pad)
        })
      }
      case "IfStatement": {
        const c = this.cond(fn, s.test, scope)
        const out = [`${pad}if ${c} then`]
        out.push(
          ...this.nonEmpty(this.block(fn, [s.consequent], new Map(scope), indent + 1), indent + 1),
        )
        if (s.alternate !== null) {
          out.push(`${pad}else`)
          out.push(
            ...this.nonEmpty(this.block(fn, [s.alternate], new Map(scope), indent + 1), indent + 1),
          )
        }
        return out
      }
      case "ForOfStatement": {
        if (s.await) return this.fail(fn, s.start, "for await is outside the subset")
        const l = s.left
        if (l.type !== "VariableDeclaration" || l.declarations.length !== 1)
          return this.fail(fn, s.start, "only `for (const x of xs)` is in the subset")
        const id = l.declarations[0]?.id
        if (id === undefined || id.type !== "Identifier")
          return this.fail(fn, s.start, "only `for (const x of xs)` is in the subset")
        const xs = this.expr(fn, s.right, scope)
        if (xs.t.k !== "list")
          return this.fail(fn, s.right.start, "for ... of iterates over an array")
        const inner = new Map(scope)
        inner.set(id.name, { t: xs.t.item, mutable: false, local: false })
        return [
          `${pad}for ${ident(id.name)} in ${xs.c} do`,
          ...this.nonEmpty(this.block(fn, [s.body], inner, indent + 1), indent + 1),
        ]
      }
      case "ForStatement":
        return this.forRange(fn, s, scope, indent)
      case "WhileStatement": {
        const c = this.cond(fn, s.test, scope)
        return [
          `${pad}while ${c} do`,
          ...this.nonEmpty(this.block(fn, [s.body], new Map(scope), indent + 1), indent + 1),
        ]
      }
      case "BreakStatement":
        if (s.label !== null) return this.fail(fn, s.start, "labelled break is outside the subset")
        return [`${pad}break`]
      case "ContinueStatement":
        if (s.label !== null)
          return this.fail(fn, s.start, "labelled continue is outside the subset")
        return [`${pad}continue`]
      case "ThrowStatement": {
        const a = s.argument
        if (
          a.type !== "NewExpression" ||
          a.callee.type !== "Identifier" ||
          !ERRORS.has(a.callee.name)
        )
          return this.fail(
            fn,
            s.start,
            "only `throw new Error(...)` (or a built-in Error) is in the subset",
          )
        const m = a.arguments[0]
        const msg =
          m === undefined
            ? '""'
            : m.type === "SpreadElement"
              ? this.fail(fn, m.start, "spread arguments are outside the subset")
              : this.expr(fn, m, scope, STR).c
        fn.fails = true
        return [`${pad}throw (Ts.Exc.error ${stringLit(a.callee.name)} ${msg})`]
      }
      case "SwitchStatement":
        return this.switchStmt(fn, s, scope, indent)
      case "ExpressionStatement":
        return this.exprStmt(fn, s.expression, scope, pad)
      default:
        return this.fail(fn, s.start, `${s.type} is outside the subset`)
    }
  }

  private switchStmt(
    fn: Fn,
    s: Extract<Statement, { type: "SwitchStatement" }>,
    scope: Scope,
    indent: number,
  ): string[] {
    const pad = "  ".repeat(indent)
    const d = s.discriminant
    let subject: Out
    let tagged: { readonly name: string; readonly t: Extract<TsType, { k: "ind" }> } | undefined
    if (
      d.type === "MemberExpression" &&
      !d.computed &&
      d.object.type === "Identifier" &&
      scope.get(d.object.name)?.t.k === "ind"
    ) {
      const t = scope.get(d.object.name)?.t
      if (t?.k !== "ind" || d.property.name !== t.tagKey)
        return this.fail(fn, d.start, "switch on an inductive value reads its tag key")
      tagged = { name: d.object.name, t }
      subject = { c: ident(d.object.name), t }
    } else subject = this.expr(fn, d, scope)
    const out = [`${pad}match ${subject.c} with`]
    let hasDefault = false
    const seen = new Set<string>()
    for (const c of s.cases) {
      const body = c.consequent.filter((x) => !(x.type === "BreakStatement" && x.label === null))
      const last = c.consequent[c.consequent.length - 1]
      if (
        c.consequent.length !== 0 &&
        !terminates(c.consequent) &&
        !(last?.type === "BreakStatement" && last.label === null)
      )
        return this.fail(fn, c.start, "each case must end with return, throw or break")
      if (c.consequent.length === 0)
        return this.fail(fn, c.start, "fall-through cases are outside the subset")
      if (body.some((x) => x.type === "BreakStatement"))
        return this.fail(fn, c.start, "break inside a case is only allowed at its end")
      const inner = new Map(scope)
      let pat: string
      if (c.test === null) {
        hasDefault = true
        pat = "_"
      } else if (c.test.type !== "Literal" || typeof c.test.value !== "string")
        return this.fail(fn, c.test.start, "case labels must be string literals")
      else {
        const label = c.test.value
        seen.add(label)
        if (tagged !== undefined) {
          const v = tagged.t.variants.find((x) => x.name === label)
          if (v === undefined)
            return this.fail(fn, c.test.start, `${tagged.t.ts} has no constructor ${label}`)
          const names = v.fields.map((f) => `${tagged.name}_${f.key}`)
          pat = `.${ident(label)}${names.map((n) => ` ${ident(n)}`).join("")}`
          inner.set(tagged.name, {
            t: { ...tagged.t, variants: [v] },
            mutable: false,
            local: false,
          })
        } else if (subject.t.k === "enum") {
          if (!subject.t.ctors.includes(label))
            return this.fail(fn, c.test.start, `${subject.t.ts} has no constructor ${label}`)
          pat = `.${ident(label)}`
        } else if (subject.t.k === "str") pat = stringLit(label)
        else
          return this.fail(
            fn,
            d.start,
            "switch is on a string, an enum or the tag of an inductive value",
          )
      }
      out.push(`${pad}| ${pat} =>`)
      out.push(...this.nonEmpty(this.block(fn, body, inner, indent + 1), indent + 1))
    }
    const total =
      tagged !== undefined
        ? tagged.t.variants.every((v) => seen.has(v.name))
        : subject.t.k === "enum" && subject.t.ctors.every((x) => seen.has(x))
    if (!hasDefault && !total) out.push(`${pad}| _ => pure ()`)
    return out
  }

  private forRange(
    fn: Fn,
    s: Extract<Statement, { type: "ForStatement" }>,
    scope: Scope,
    indent: number,
  ): string[] {
    const pad = "  ".repeat(indent)
    const bad = (): never =>
      this.fail(fn, s.start, "only `for (let i = a; i < b; i++)` (or `i <= b`) is in the subset")
    const init = s.init
    if (init === null || init.type !== "VariableDeclaration" || init.declarations.length !== 1)
      return bad()
    const d = init.declarations[0]
    if (d === undefined || d.id.type !== "Identifier" || d.init === null) return bad()
    const i = d.id.name
    const t = s.test
    if (
      t === null ||
      t.type !== "BinaryExpression" ||
      (t.operator !== "<" && t.operator !== "<=") ||
      t.left.type !== "Identifier" ||
      t.left.name !== i
    )
      return bad()
    const u = s.update
    const step =
      u !== null &&
      ((u.type === "UpdateExpression" &&
        u.operator === "++" &&
        u.argument.type === "Identifier" &&
        u.argument.name === i) ||
        (u.type === "AssignmentExpression" &&
          u.operator === "+=" &&
          u.left.type === "Identifier" &&
          u.left.name === i &&
          u.right.type === "Literal" &&
          (u.right.value === 1 || u.right.value === 1n)))
    if (!step) return bad()
    const a = this.expr(fn, d.init, scope)
    if (!isInt(a.t)) return bad()
    const b = this.expr(fn, t.right, scope, a.t)
    const assigned = assignedNames(s.body)
    if (assigned.has(i))
      return this.fail(fn, s.body.start, `the loop variable ${i} is assigned in the body`)
    for (const n of identifiers(t.right))
      if (assigned.has(n))
        return this.fail(fn, t.right.start, `the bound reads ${n}, which the body assigns`)
    const hi = t.operator === "<=" ? `(${b.c} + 1)` : b.c
    const inner = new Map(scope)
    inner.set(i, { t: a.t, mutable: false, local: false })
    return [
      `${pad}for ${ident(i)} in Ts.range ${a.c} ${hi} do`,
      ...this.nonEmpty(this.block(fn, [s.body], inner, indent + 1), indent + 1),
    ]
  }

  private declareVar(
    fn: Fn,
    id: BindingPattern,
    init: Expression,
    scope: Scope,
    pad: string,
  ): string[] {
    if (id.type === "Identifier") {
      const ann = id.typeAnnotation?.typeAnnotation
      const t = ann === undefined || ann === null ? undefined : tsType(ann, fn.src, this.types)
      const v = this.expr(fn, init, scope, t)
      const ty = t ?? v.t
      scope.set(id.name, { t: ty, mutable: true, local: true })
      return [`${pad}let mut ${ident(id.name)} : ${leanType(ty)} := ${v.c}`]
    }
    if (id.type === "ArrayPattern") {
      const v = this.expr(fn, init, scope)
      if (v.t.k !== "tuple") return this.fail(fn, id.start, "array destructuring is for tuples")
      const items = v.t.items
      const tmp = `__t${id.start}`
      const out = [`${pad}let ${tmp} := ${v.c}`]
      id.elements.forEach((e, k) => {
        if (e === null) return
        if (e.type !== "Identifier")
          this.fail(fn, e.start, "only names are allowed in destructuring")
        const it = items[k]
        if (it === undefined) this.fail(fn, e.start, "the tuple has no such element")
        scope.set(e.name, { t: it, mutable: true, local: true })
        out.push(
          `${pad}let mut ${ident(e.name)} : ${leanType(it)} := ${tupleProj(tmp, k, items.length)}`,
        )
      })
      return out
    }
    if (id.type === "ObjectPattern") {
      const v = this.expr(fn, init, scope)
      if (v.t.k !== "struct")
        return this.fail(fn, id.start, "object destructuring is for structures")
      const st = v.t
      const tmp = `__t${id.start}`
      const out = [`${pad}let ${tmp} := ${v.c}`]
      for (const p of id.properties) {
        if (
          p.type !== "Property" ||
          p.computed ||
          p.key.type !== "Identifier" ||
          p.value.type !== "Identifier"
        )
          return this.fail(fn, p.start, "only `{ a, b: c }` is allowed in destructuring")
        const keyName = p.key.name
        const f = st.fields.find((x) => x.key === keyName)
        if (f === undefined) return this.fail(fn, p.start, `${st.ts} has no field ${keyName}`)
        scope.set(p.value.name, { t: f.type, mutable: true, local: true })
        const read = `${tmp}.${ident(f.lean)}`
        out.push(
          `${pad}let mut ${ident(p.value.name)} : ${leanType(f.type)} := ${f.nat ? `(${read} : Int)` : read}`,
        )
      }
      return out
    }
    return this.fail(fn, id.start, "this declaration is outside the subset")
  }

  private exprStmt(fn: Fn, e: Expression, scope: Scope, pad: string): string[] {
    if (e.type === "AssignmentExpression") {
      if (e.left.type !== "Identifier")
        return this.fail(fn, e.start, "only assignments to local variables are in the subset")
      const name = e.left.name
      const v = scope.get(name)
      if (v === undefined || !v.local)
        return this.fail(fn, e.start, `${name} is not a local variable`)
      const x = ident(name)
      if (e.operator === "=") return [`${pad}${x} := ${this.expr(fn, e.right, scope, v.t).c}`]
      const op = e.operator.slice(0, -1)
      const r = this.binary(fn, op, { c: x, t: v.t }, e.right, scope, e.start)
      return [`${pad}${x} := ${r.c}`]
    }
    if (e.type === "UpdateExpression") {
      if (e.argument.type !== "Identifier")
        return this.fail(fn, e.start, "++ and -- apply to local variables")
      const name = e.argument.name
      const v = scope.get(name)
      if (v === undefined || !v.local || !isInt(v.t))
        return this.fail(fn, e.start, `${name} is not a local number`)
      return [`${pad}${ident(name)} := ${ident(name)} ${e.operator === "++" ? "+" : "-"} 1`]
    }
    if (
      e.type === "CallExpression" &&
      e.callee.type === "MemberExpression" &&
      !e.callee.computed &&
      e.callee.property.type === "Identifier" &&
      e.callee.property.name === "push"
    ) {
      const target = e.callee.object
      const v = target.type === "Identifier" ? scope.get(target.name) : undefined
      if (target.type !== "Identifier" || v === undefined || !v.local || v.t.k !== "list")
        return this.fail(fn, e.start, "push only to an array created in the function")
      const items = e.arguments.map((a) =>
        a.type === "SpreadElement"
          ? this.fail(fn, a.start, "spread arguments are outside the subset")
          : this.expr(fn, a, scope, v.t.k === "list" ? v.t.item : undefined).c,
      )
      return [`${pad}${ident(target.name)} := ${ident(target.name)} ++ [${items.join(", ")}]`]
    }
    return this.fail(fn, e.start, "this expression statement is outside the subset")
  }

  private cond(fn: Fn, e: Expression, scope: Scope): string {
    const c = this.expr(fn, e, scope, BOOL)
    if (c.t.k !== "bool") return this.fail(fn, e.start, "a condition must be a boolean")
    return c.c
  }

  private lifted(fn: Fn, call: string): string {
    fn.fails = true
    return `(← ${call})`
  }

  private binary(fn: Fn, op: string, a: Out, rightNode: Expression, scope: Scope, at: number): Out {
    const b = this.expr(fn, rightNode, scope, isInt(a.t) ? a.t : undefined)
    if (op === "+") {
      if (a.t.k === "str" && b.t.k === "str") return { c: `(${a.c} ++ ${b.c})`, t: STR }
      if (a.t.k === "str" || b.t.k === "str") {
        const s = (x: Out): string => (x.t.k === "str" ? x.c : `(Ts.str ${x.c})`)
        return { c: `(${s(a)} ++ ${s(b)})`, t: STR }
      }
    }
    if (op === "+" || op === "-" || op === "*") {
      if (!isInt(a.t) || !isInt(b.t)) return this.fail(fn, at, `${op} needs numbers`)
      if (a.t.k !== b.t.k) return this.fail(fn, at, "number and bigint do not mix")
      return { c: `(${a.c} ${op} ${b.c})`, t: a.t }
    }
    if (op === "%") {
      if (!isInt(a.t) || a.t.k !== b.t.k)
        return this.fail(fn, at, "% needs two numbers or two bigints")
      return { c: this.lifted(fn, `Ts.rem ${a.c} ${b.c}`), t: a.t }
    }
    if (op === "/") {
      if (a.t.k === "big" && b.t.k === "big")
        return { c: this.lifted(fn, `Ts.truncDiv ${a.c} ${b.c}`), t: BIG }
      return this.fail(fn, at, "number division is only in Math.floor(a / b) or Math.trunc(a / b)")
    }
    if (op === "<" || op === "<=" || op === ">" || op === ">=") {
      if (!((isInt(a.t) && a.t.k === b.t.k) || (a.t.k === "str" && b.t.k === "str")))
        return this.fail(fn, at, `${op} compares two numbers, two bigints or two strings`)
      const sym = op === "<=" ? "≤" : op === ">=" ? "≥" : op
      return { c: `(decide (${a.c} ${sym} ${b.c}))`, t: BOOL }
    }
    if (op === "===" || op === "!==") {
      if (!same(a.t, b.t)) return this.fail(fn, at, `${op} compares values of the same type`)
      return { c: `(${a.c} ${op === "===" ? "==" : "!="} ${b.c})`, t: BOOL }
    }
    return this.fail(fn, at, `the operator ${op} is outside the subset`)
  }

  expr(fn: Fn, e: Expression, scope: Scope, want?: TsType): Out {
    switch (e.type) {
      case "ParenthesizedExpression":
        return this.expr(fn, e.expression, scope, want)
      case "Literal": {
        const v = e.value
        if (typeof v === "boolean") return { c: v ? "true" : "false", t: BOOL }
        if (typeof v === "bigint") return { c: `(${v} : Int)`, t: BIG }
        if (typeof v === "number") {
          if (!Number.isSafeInteger(v))
            return this.fail(fn, e.start, "only safe integers are in the subset")
          return { c: `(${v} : Int)`, t: want?.k === "big" ? BIG : NUM }
        }
        if (typeof v === "string") return { c: stringLit(v), t: STR }
        if (v === null && want?.k === "opt") return { c: "none", t: want }
        return this.fail(fn, e.start, "this literal is outside the subset")
      }
      case "Identifier": {
        if (e.name === "undefined" && want?.k === "opt") return { c: "none", t: want }
        const v = scope.get(e.name)
        if (v === undefined) return this.fail(fn, e.start, `unknown name ${e.name}`)
        return { c: ident(e.name), t: v.t }
      }
      case "TemplateLiteral": {
        const parts: string[] = []
        e.quasis.forEach((q, i) => {
          const text = q.value.cooked ?? this.fail(fn, q.start, "invalid escape in the template")
          if (text !== "") parts.push(stringLit(text))
          const x = e.expressions[i]
          if (x !== undefined) {
            const o = this.expr(fn, x, scope)
            if (o.t.k !== "str" && !isInt(o.t) && o.t.k !== "bool")
              this.fail(fn, x.start, "${} takes a string, a number, a bigint or a boolean")
            parts.push(o.t.k === "str" ? o.c : `(Ts.str ${o.c})`)
          }
        })
        return { c: parts.length === 0 ? '""' : `(${parts.join(" ++ ")})`, t: STR }
      }
      case "UnaryExpression": {
        const a = this.expr(fn, e.argument, scope, want)
        if (e.operator === "-" && isInt(a.t)) return { c: `(-${a.c})`, t: a.t }
        if (e.operator === "!" && a.t.k === "bool") return { c: `(!${a.c})`, t: BOOL }
        return this.fail(fn, e.start, `the operator ${e.operator} is outside the subset`)
      }
      case "BinaryExpression": {
        if (e.left.type === "PrivateIdentifier") return this.fail(fn, e.start, "outside the subset")
        if (e.operator === "==" || e.operator === "!=")
          return this.fail(fn, e.start, `${e.operator} is outside the subset; use ${e.operator}=`)
        const nc = nullCheck(e)
        if (nc !== undefined) {
          const v = scope.get(nc.name)
          if (v === undefined || v.t.k !== "opt")
            return this.fail(fn, e.start, `${nc.name} is not optional`)
          return { c: `${ident(nc.name)}.${nc.isNull ? "isNone" : "isSome"}`, t: BOOL }
        }
        const a = this.expr(fn, e.left, scope, want !== undefined && isInt(want) ? want : undefined)
        return this.binary(fn, e.operator, a, e.right, scope, e.start)
      }
      case "LogicalExpression": {
        if (e.operator === "??") {
          const a = this.expr(fn, e.left, scope)
          if (a.t.k !== "opt")
            return this.fail(fn, e.start, "?? needs an optional value on its left")
          const b = this.expr(fn, e.right, scope, a.t.item)
          return { c: `(${a.c}.getD ${b.c})`, t: a.t.item }
        }
        const a = this.expr(fn, e.left, scope, BOOL)
        const b = this.expr(fn, e.right, scope, BOOL)
        if (a.t.k !== "bool" || b.t.k !== "bool")
          return this.fail(fn, e.start, `${e.operator} needs booleans`)
        return { c: `(${a.c} ${e.operator} ${b.c})`, t: BOOL }
      }
      case "ConditionalExpression": {
        const c = this.cond(fn, e.test, scope)
        const a = this.expr(fn, e.consequent, scope, want)
        const b = this.expr(fn, e.alternate, scope, want ?? a.t)
        return { c: `(if ${c} then ${a.c} else ${b.c})`, t: a.t }
      }
      case "TSNonNullExpression": {
        const x = e.expression
        if (x.type === "MemberExpression" && x.computed) {
          const xs = this.expr(fn, x.object, scope)
          if (xs.t.k === "list") {
            const i = this.expr(fn, x.property, scope)
            return { c: this.lifted(fn, `Ts.get ${xs.c} ${i.c}`), t: xs.t.item }
          }
        }
        const o = this.expr(fn, x, scope)
        if (o.t.k !== "opt")
          return this.fail(fn, e.start, "! applies to an optional value or xs[i]")
        return { c: this.lifted(fn, `Ts.unwrap ${o.c}`), t: o.t.item }
      }
      case "MemberExpression":
        return this.member(fn, e, scope)
      case "ArrayExpression": {
        const item = want?.k === "list" ? want.item : undefined
        const parts = e.elements.map((x) =>
          x === null || x.type === "SpreadElement"
            ? this.fail(fn, e.start, "holes and spreads are outside the subset")
            : this.expr(fn, x, scope, item),
        )
        if (want?.k === "tuple") {
          const ps = e.elements.map((x, k) =>
            x === null || x.type === "SpreadElement"
              ? this.fail(fn, e.start, "holes and spreads are outside the subset")
              : this.expr(fn, x, scope, want.items[k]),
          )
          return { c: `(${ps.map((p) => p.c).join(", ")})`, t: want }
        }
        const t = item ?? parts[0]?.t
        if (t === undefined) return this.fail(fn, e.start, "annotate the type of an empty array")
        return { c: `[${parts.map((p) => p.c).join(", ")}]`, t: { k: "list", item: t } }
      }
      case "ObjectExpression":
        return this.object(fn, e, scope, want)
      case "CallExpression":
        return this.call(fn, e, scope, want)
      default:
        return this.fail(fn, e.start, `${e.type} is outside the subset`)
    }
  }

  private object(
    fn: Fn,
    e: Extract<Expression, { type: "ObjectExpression" }>,
    scope: Scope,
    want: TsType | undefined,
  ): Out {
    const entries = new Map<string, Expression>()
    for (const p of e.properties) {
      if (p.type !== "Property" || p.kind !== "init" || p.method || p.computed)
        return this.fail(fn, p.start, "only plain properties are in the subset")
      const k =
        p.key.type === "Identifier"
          ? p.key.name
          : p.key.type === "Literal" && typeof p.key.value === "string"
            ? p.key.value
            : this.fail(fn, p.start, "property keys must be names")
      entries.set(k, p.value)
    }
    const fieldsOf = (fields: readonly FieldType[]): string =>
      fields
        .map((f) => {
          const v = entries.get(f.key)
          if (v === undefined) return this.fail(fn, e.start, `the field ${f.key} is missing`)
          const x = this.expr(fn, v, scope, f.type).c
          return `${ident(f.lean)} := ${f.nat ? `(${x}).toNat` : x}`
        })
        .join(", ")
    if (want?.k === "struct") {
      for (const k of entries.keys())
        if (!want.fields.some((f) => f.key === k))
          this.fail(fn, e.start, `${want.ts} has no field ${k}`)
      return { c: `({ ${fieldsOf(want.fields)} } : ${leanType(want)})`, t: want }
    }
    if (want?.k === "ind") {
      const tag = entries.get(want.tagKey)
      if (tag === undefined || tag.type !== "Literal" || typeof tag.value !== "string")
        return this.fail(
          fn,
          e.start,
          `the ${want.tagKey} of an inductive value must be a string literal`,
        )
      const name = tag.value
      const v = want.variants.find((x) => x.name === name)
      if (v === undefined) return this.fail(fn, e.start, `${want.ts} has no constructor ${name}`)
      const args = v.fields.map((f) => {
        const x = entries.get(f.key)
        if (x === undefined) return this.fail(fn, e.start, `the field ${f.key} is missing`)
        const c = this.expr(fn, x, scope, f.type).c
        return f.nat ? `(${c}).toNat` : c
      })
      return {
        c: `(${leanType(want)}.${ident(name)}${args.map((a) => ` ${a}`).join("")})`,
        t: want,
      }
    }
    return this.fail(
      fn,
      e.start,
      "an object literal needs a structure or inductive type from its context",
    )
  }

  private member(fn: Fn, e: Extract<Expression, { type: "MemberExpression" }>, scope: Scope): Out {
    if (e.optional) return this.fail(fn, e.start, "?. is outside the subset")
    const o = this.expr(fn, e.object, scope)
    if (e.computed) {
      if (o.t.k === "tuple") {
        const p = e.property
        if (p.type !== "Literal" || typeof p.value !== "number")
          return this.fail(fn, e.start, "a tuple is indexed by a number literal")
        const t = o.t.items[p.value]
        if (t === undefined) return this.fail(fn, e.start, "the tuple has no such element")
        return { c: tupleProj(o.c, p.value, o.t.items.length), t }
      }
      if (o.t.k === "list") {
        const i = this.expr(fn, e.property, scope)
        if (!isInt(i.t)) return this.fail(fn, e.start, "an array index is a number")
        return {
          c: `(Ts.index ${o.c} ${i.c})`,
          t: { k: "opt", item: o.t.item, absent: "undefined" },
        }
      }
      return this.fail(fn, e.start, "only arrays and tuples are indexed")
    }
    if (e.property.type !== "Identifier") return this.fail(fn, e.start, "outside the subset")
    const name = e.property.name
    if (name === "length") {
      if (o.t.k === "list") return { c: `(Ts.length ${o.c})`, t: NUM }
      if (o.t.k === "str") return { c: `(Ts.strLength ${o.c})`, t: NUM }
    }
    if (o.t.k === "struct") {
      const f = o.t.fields.find((x) => x.key === name)
      if (f === undefined) return this.fail(fn, e.start, `${o.t.ts} has no field ${name}`)
      const read = `${o.c}.${ident(f.lean)}`
      return { c: f.nat ? `(${read} : Int)` : read, t: f.type }
    }
    if (o.t.k === "ind" && o.t.variants.length === 1) {
      const v = o.t.variants[0]
      const f = v?.fields.find((x) => x.key === name)
      if (f !== undefined && e.object.type === "Identifier") {
        const read = ident(`${e.object.name}_${f.key}`)
        return { c: f.nat ? `(${read} : Int)` : read, t: f.type }
      }
    }
    return this.fail(fn, e.start, `the property ${name} is outside the subset`)
  }

  private arrow(
    fn: Fn,
    a: Expression | undefined,
    scope: Scope,
    params: readonly TsType[],
  ): Out & { ps: string } {
    if (a === undefined || a.type !== "ArrowFunctionExpression" || a.async)
      return this.fail(fn, a?.start ?? 0, "the argument must be an arrow function")
    if (a.params.length !== params.length)
      return this.fail(fn, a.start, `the arrow function takes ${params.length} parameters`)
    const inner = new Map(scope)
    const names = a.params.map((p, k) => {
      if (p.type !== "Identifier") return this.fail(fn, p.start, "arrow parameters must be names")
      const t = params[k]
      if (t === undefined) return this.fail(fn, p.start, "outside the subset")
      inner.set(p.name, { t, mutable: false, local: false })
      return ident(p.name)
    })
    let body: Expression
    if (a.body.type === "BlockStatement") {
      const only = a.body.body[0]
      if (a.body.body.length !== 1 || only?.type !== "ReturnStatement" || only.argument === null)
        return this.fail(
          fn,
          a.start,
          "the arrow function body must be one expression or one return",
        )
      body = only.argument
    } else body = a.body
    const out = this.expr(fn, body, inner)
    if (out.c.includes("←")) return this.fail(fn, a.start, "an arrow function must not fail")
    return { ...out, ps: names.join(" ") }
  }

  private args(fn: Fn, c: CallExpression): Expression[] {
    return c.arguments.map((a) =>
      a.type === "SpreadElement"
        ? this.fail(fn, a.start, "spread arguments are outside the subset")
        : a,
    )
  }

  private call(fn: Fn, c: CallExpression, scope: Scope, want?: TsType): Out {
    if (c.optional) return this.fail(fn, c.start, "?. is outside the subset")
    const f = c.callee
    const args = this.args(fn, c)
    if (f.type === "Identifier") {
      if (f.name === "BigInt" || f.name === "Number") {
        const x = args[0]
        if (args.length !== 1 || x === undefined)
          return this.fail(fn, c.start, `${f.name} takes one argument`)
        const o = this.expr(fn, x, scope)
        if (!isInt(o.t)) return this.fail(fn, c.start, `${f.name} converts a number or a bigint`)
        return { c: o.c, t: f.name === "BigInt" ? BIG : NUM }
      }
      if (f.name === "String") {
        const x = args[0]
        if (args.length !== 1 || x === undefined)
          return this.fail(fn, c.start, "String takes one argument")
        const o = this.expr(fn, x, scope)
        return { c: o.t.k === "str" ? o.c : `(Ts.str ${o.c})`, t: STR }
      }
      const target = this.fns.get(f.name)
      if (target === undefined)
        return this.fail(fn, c.start, `${f.name} is not a model function of this module`)
      if (args.length !== target.params.length)
        return this.fail(fn, c.start, `${f.name} takes ${target.params.length} arguments`)
      const parts = args.map((a, k) => {
        const p = target.params[k]
        if (p === undefined) return this.fail(fn, c.start, "outside the subset")
        const x = this.expr(fn, a, scope, p.type).c
        return p.nat ? `(${x}).toNat` : x
      })
      const call = `${ident(target.name)}${parts.map((p) => ` ${p}`).join("")}`
      return { c: target.fails ? this.lifted(fn, call) : `(${call})`, t: target.ret }
    }
    if (f.type !== "MemberExpression" || f.computed || f.property.type !== "Identifier")
      return this.fail(fn, c.start, "this call is outside the subset")
    const m = f.property.name
    if (f.object.type === "Identifier" && f.object.name === "Math" && !scope.has("Math")) {
      if ((m === "floor" || m === "trunc") && args.length === 1) {
        const d = args[0]
        if (d?.type === "BinaryExpression" && d.operator === "/") {
          const a = this.expr(fn, d.left, scope, NUM)
          const b = this.expr(fn, d.right, scope, NUM)
          if (a.t.k !== "num" || b.t.k !== "num")
            return this.fail(fn, c.start, `Math.${m}(a / b) divides numbers`)
          return {
            c: this.lifted(fn, `Ts.${m === "floor" ? "floorDiv" : "truncDiv"} ${a.c} ${b.c}`),
            t: NUM,
          }
        }
        return this.fail(fn, c.start, `Math.${m} is only in the form Math.${m}(a / b)`)
      }
      if ((m === "max" || m === "min") && args.length === 2) {
        const [x, y] = args
        if (x === undefined || y === undefined) return this.fail(fn, c.start, "outside the subset")
        const a = this.expr(fn, x, scope, want)
        const b = this.expr(fn, y, scope, a.t)
        if (a.t.k !== "num" || b.t.k !== "num")
          return this.fail(fn, c.start, `Math.${m} takes numbers`)
        return { c: `(${m} ${a.c} ${b.c})`, t: NUM }
      }
      if (m === "abs" && args.length === 1 && args[0] !== undefined) {
        const a = this.expr(fn, args[0], scope, NUM)
        if (a.t.k !== "num") return this.fail(fn, c.start, "Math.abs takes a number")
        return { c: `(Ts.abs ${a.c})`, t: NUM }
      }
      return this.fail(fn, c.start, `Math.${m} is outside the subset`)
    }
    const o = this.expr(fn, f.object, scope)
    if (
      o.t.k === "str" &&
      (m === "startsWith" || m === "endsWith" || m === "includes") &&
      args.length === 1
    ) {
      const x = args[0]
      if (x === undefined) return this.fail(fn, c.start, "outside the subset")
      const a = this.expr(fn, x, scope, STR)
      if (a.t.k !== "str") return this.fail(fn, c.start, `${m} takes a string`)
      return { c: `(Ts.${m} ${o.c} ${a.c})`, t: BOOL }
    }
    if (o.t.k !== "list") return this.fail(fn, c.start, `the method ${m} is outside the subset`)
    const item = o.t.item
    if (m === "includes" && args.length === 1 && args[0] !== undefined) {
      const a = this.expr(fn, args[0], scope, item)
      return { c: `(${o.c}.contains ${a.c})`, t: BOOL }
    }
    if (m === "map" && args.length === 1) {
      const a = this.arrow(fn, args[0], scope, [item])
      return { c: `(${o.c}.map fun ${a.ps} => ${a.c})`, t: { k: "list", item: a.t } }
    }
    if ((m === "filter" || m === "some" || m === "every") && args.length === 1) {
      const a = this.arrow(fn, args[0], scope, [item])
      if (a.t.k !== "bool")
        return this.fail(fn, c.start, `the arrow function of ${m} returns a boolean`)
      const lean = m === "filter" ? "filter" : m === "some" ? "any" : "all"
      return { c: `(${o.c}.${lean} fun ${a.ps} => ${a.c})`, t: m === "filter" ? o.t : BOOL }
    }
    if (m === "reduce" && args.length === 2 && args[1] !== undefined) {
      const init = this.expr(fn, args[1], scope, want)
      const a = this.arrow(fn, args[0], scope, [init.t, item])
      return { c: `(${o.c}.foldl (fun ${a.ps} => ${a.c}) ${init.c})`, t: init.t }
    }
    return this.fail(fn, c.start, `the method ${m} is outside the subset`)
  }
}

type AnyNode = { readonly type: string } & Readonly<Record<string, unknown>>

function isAnyNode(x: unknown): x is AnyNode {
  return typeof x === "object" && x !== null && typeof Reflect.get(x, "type") === "string"
}

function walk(node: unknown, visit: (n: AnyNode) => void): void {
  if (Array.isArray(node)) {
    for (const x of node) walk(x, visit)
    return
  }
  if (typeof node !== "object" || node === null) return
  if (isAnyNode(node)) visit(node)
  for (const [k, v] of Object.entries(node)) if (k !== "parent") walk(v, visit)
}

function assignedNames(node: unknown): Set<string> {
  const out = new Set<string>()
  walk(node, (n) => {
    const target =
      n.type === "AssignmentExpression"
        ? n["left"]
        : n.type === "UpdateExpression"
          ? n["argument"]
          : null
    if (
      typeof target === "object" &&
      target !== null &&
      Reflect.get(target, "type") === "Identifier"
    ) {
      const name: unknown = Reflect.get(target, "name")
      if (typeof name === "string") out.add(name)
    }
  })
  return out
}

function identifiers(node: unknown): Set<string> {
  const out = new Set<string>()
  walk(node, (n) => {
    if (n.type === "Identifier" && typeof n["name"] === "string") out.add(n["name"])
  })
  return out
}

export function astHash(node: unknown): string {
  return JSON.stringify(node, (k, v: unknown) =>
    k === "start" || k === "end" || k === "parent" || k === "range" || k === "loc"
      ? undefined
      : typeof v === "bigint"
        ? `${v}n`
        : v,
  )
}
