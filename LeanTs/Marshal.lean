import Lean
import LeanTs.EmitTs

open Lean Meta Lean.IR

namespace LeanTs

def tsReserved : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do",
   "else", "enum", "export", "extends", "false", "finally", "for", "function", "if", "import", "in",
   "instanceof", "new", "null", "return", "super", "switch", "this", "throw", "true", "try",
   "typeof", "var", "void", "while", "with", "yield", "let", "static", "implements", "interface",
   "package", "private", "protected", "public", "await", "arguments", "eval", "undefined", "NaN",
   "Infinity", "L"]

def sanitize (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '?' => "_q"
    | '!' => "_bang"
    | '\'' => "_prime"
    | c => if (c.isAlphanum && c.toNat < 128) || c == '_' then c.toString else "_") ""

def tsIdent (s : String) : String :=
  if s.isEmpty then "_"
  else if s.front.isDigit then "_" ++ s
  else if tsReserved.contains s then s ++ "_"
  else s

def camelParts (s : String) : List String :=
  ((sanitize s).splitOn "_").filter (!·.isEmpty)

def camelJoin (s : String) : String :=
  match camelParts s with
    | [] => ""
    | p :: ps => p.decapitalize ++ String.join (ps.map String.capitalize)

def lowerCamel (s : String) : String := tsIdent (camelJoin s)

def memberIdent (s : String) : String :=
  let t := camelJoin s
  if t.isEmpty then "_" else if t.front.isDigit then "_" ++ t else t

def namespaceIdent (s : String) : String :=
  tsIdent <| match camelParts s with
    | [] => ""
    | p :: ps => p ++ String.join (ps.map String.capitalize)

def componentString : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

def stripName (strip n : Name) : Name :=
  if strip != .anonymous && strip.isPrefixOf n && strip != n then n.replacePrefix strip .anonymous else n

def tsPath (strip n : Name) : Array String :=
  let cs := (stripName strip n).components.toArray.map componentString
  match cs.back? with
  | none => #[]
  | some last =>
    if cs.size == 1 then #[lowerCamel last] else cs.pop.map namespaceIdent |>.push (memberIdent last)

structure Settings where
  tagKey : String := "ctor"
  option : String := "null"
  deriving Inhabited

def isJsIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    let start (c : Char) := (c.isAlpha && c.toNat < 128) || c == '_' || c == '$'
    start c && cs.all fun c => start c || (c.isDigit && c.toNat < 128)

def Settings.check (s : Settings) : Except String Unit := do
  unless isJsIdent s.tagKey do throw s!"tagKey must be a JavaScript identifier (got {s.tagKey.quote})"
  unless s.option == "null" || s.option == "undefined" do
    throw s!"option must be \"null\" or \"undefined\" (got {s.option.quote})"

inductive Desc where
  | nat | int | bool | char | string | float | float32 | unit
  | uint (bits : Nat)
  | sint (bits : Nat)
  | usize | isize
  | list (d : Desc)
  | array (d : Desc)
  | option (d : Desc)
  | prod (a b : Desc)
  | except (e a : Desc)
  | fin (n : Nat)
  | named (ident : String)
  | foreign (alias ident : String)
  | model (ident key out inp : String)
  deriving Inhabited, BEq

def arrayElem (s : String) : String :=
  if s.contains '|' || s.contains '&' || s.startsWith "readonly " then s!"({s})" else s

partial def Desc.code (s : Settings) (lazy : Bool) : Desc → String
  | .nat => "L.natDesc"
  | .int => "L.intDesc"
  | .bool => "L.boolDesc"
  | .char => "L.charDesc"
  | .string => "L.stringDesc"
  | .float => "L.floatDesc"
  | .float32 => "L.float32Desc"
  | .unit => "L.unitDesc"
  | .uint b => s!"L.uintDesc({b})"
  | .sint b => s!"L.sintDesc({b})"
  | .usize => "L.usizeDesc"
  | .isize => "L.isizeDesc"
  | .list d => s!"L.listDesc({d.code s lazy})"
  | .array d => s!"L.arrayDesc({d.code s lazy})"
  | .option d => s!"L.optionDesc({d.code s lazy}, {quoteString s.option})"
  | .prod a b => s!"L.prodDesc({a.code s lazy}, {b.code s lazy})"
  | .except e a => s!"L.exceptDesc({e.code s lazy}, {a.code s lazy})"
  | .fin n => s!"L.finDesc({n}n)"
  | .named i => if lazy then s!"L.refDesc(() => $t{i})" else s!"$t{i}"
  | .foreign a i => s!"L.refDesc(() => {a}.{i}.desc)"
  | .model i key o _ =>
    let st := if lazy then s!"L.refDesc(() => $t{i})" else s!"$t{i}"
    s!"L.modelDesc<{o}>({quoteString key}, {quoteString i}, {st})"

def finIsNumber (n : Nat) : Bool := n ≤ 2 ^ 32

partial def Desc.outType (s : Settings) : Desc → String
  | .nat | .int | .usize | .isize => "bigint"
  | .uint b | .sint b => if b == 64 then "bigint" else "number"
  | .bool => "boolean"
  | .char | .string => "string"
  | .float | .float32 => "number"
  | .unit => "undefined"
  | .list d | .array d => s!"{arrayElem (d.outType s)}[]"
  | .option d => s!"{d.outType s} | {s.option}"
  | .prod a b => s!"readonly [{a.outType s}, {b.outType s}]"
  | .except e a => s!"L.Except<{e.outType s}, {a.outType s}>"
  | .fin n => if finIsNumber n then "number" else "bigint"
  | .named i => i
  | .foreign a i => s!"{a}.{i}"
  | .model _ _ o _ => o

partial def Desc.jsonType (s : Settings) : Desc → String
  | .nat | .int | .usize | .isize | .fin _ => "bigint | number | string"
  | .uint b | .sint b => if b == 64 then "bigint | number | string" else "number"
  | .bool => "boolean"
  | .char | .string => "string"
  | .float | .float32 => "number | string"
  | .unit => "L.UnitInput"
  | .list d | .array d => s!"readonly {arrayElem (d.jsonType s)}[]"
  | .option d => s!"{d.jsonType s} | null | undefined"
  | .prod a b => s!"readonly [{a.jsonType s}, {b.jsonType s}]"
  | .except e a => s!"L.ExceptInput<{e.jsonType s}, {a.jsonType s}>"
  | .named i => s!"{i}Input"
  | .foreign a i => s!"{a}.{i}Input"
  | .model _ _ _ inp => inp

partial def Desc.inType (s : Settings) : Desc → String
  | .nat | .int | .fin _ => "bigint | number"
  | .list d | .array d => s!"readonly {arrayElem (d.inType s)}[]"
  | .option d => s!"{d.inType s} | {s.option}"
  | .prod a b => s!"readonly [{a.inType s}, {b.inType s}]"
  | .except e a => s!"L.Except<{e.inType s}, {a.inType s}>"
  | d => d.outType s

def Desc.paramType (s : Settings) : Desc → String
  | .unit => "void"
  | d => d.inType s

def Desc.resultType (s : Settings) : Desc → String
  | .unit => "void"
  | d => d.outType s

structure FieldInfo where
  key : String
  slot : String
  pos : Nat
  desc : Desc
  omitNone : Bool := false
  flat : Bool := false
  bounds : Array (String × Int) := #[]
  deriving Inhabited

structure InvInfo where
  field : String
  prop : String
  decider : Name
  args : Array Nat
  deriving Inhabited

structure VariantInfo where
  name : String
  cidx : Nat
  size : Nat
  usize : Nat
  ssize : Nat
  positional : Bool
  fields : Array FieldInfo
  invariants : Array InvInfo
  deriving Inhabited

inductive TypeKind where
  | struct (v : VariantInfo) (trivial : Option Nat)
  | enum (ctors : Array String)
  | sum (vs : Array VariantInfo)
  | subtype (base : Desc) (inv : InvInfo) (bounds : Array (String × Int))
  deriving Inhabited

structure TypeDef where
  ident : String
  lean : Name
  pretty : String
  kind : TypeKind
  exported : Bool := true
  deriving Inhabited

structure ModelRef where
  ns : Name
  key : String
  module : String := ""
  exportName : String := ""
  deriving Inhabited

structure MarshalCfg where
  strip : Name
  typeModules : Array (Name × String) := #[]
  modelModules : Array ModelRef := #[]
  settings : Settings := {}

structure MarshalState where
  types : Array TypeDef := #[]
  byType : Std.HashMap Lean.Expr Desc := {}
  idents : Std.HashSet String := {}
  deciders : Array Name := #[]
  foreignImports : Array (String × String) := #[]
  modelImports : Array (String × String × String) := #[]
  subtypes : Nat := 0

abbrev MarshalM := StateRefT MarshalState (ReaderT MarshalCfg MetaM)

def tagKeyClash : String := "tagKey clash: "

def typeReserved : List String := ["Obj", "Object"]

def capitalizeIdent (s : String) : String :=
  let parts := camelParts s
  String.join (parts.map String.capitalize)

def typeIdentOf (strip c : Name) (args : Array String) : String :=
  let comps := (stripName strip c).components.map fun n => (sanitize (componentString n)).capitalize
  let base := "_".intercalate (comps.filter (!·.isEmpty))
  let base := base ++ String.join (args.toList.map capitalizeIdent)
  let base := tsIdent base
  if typeReserved.contains base then base ++ "_" else base

def freshIdent (base : String) : MarshalM String := do
  let st ← get
  let mut nm := base
  let mut k := 2
  while st.idents.contains nm do
    nm := s!"{base}_{k}"; k := k + 1
  modify fun s => { s with idents := s.idents.insert nm }
  return nm

def deciderName (ident ctor field : String) : Name :=
  .str (.str (.str (.str .anonymous "LeanTsGen") ident) ctor) (field ++ "_decide")

def compileDecider (name : Name) (args : Array Lean.Expr) (prop : Lean.Expr) : MetaM Unit := do
  if (← getEnv).contains name then return
  let dec ← try mkDecide prop
    catch _ => throwError "no `Decidable` instance for the proposition `{prop}`"
  let value ← instantiateMVars (← mkLambdaFVars args dec)
  if value.hasFVar || value.hasMVar then throwError "the proposition `{prop}` depends on a proof field"
  let type ← inferType value
  addAndCompile (.defnDecl { name, levelParams := [], type, value, hints := .opaque, safety := .safe })

def literalInt? (e : Lean.Expr) : MetaM (Option Int) := do
  let e ← instantiateMVars e
  if let some i := e.int? then return some i
  if let some n ← (evalNat e).run then return some (Int.ofNat n)
  return none

def boundOf (v : Lean.Expr) (p : Lean.Expr) : MetaM (Option (String × Int)) := do
  let p := p.consumeMData
  let (op, a, b) ← match p.getAppFnArgs with
    | (``LT.lt, #[_, _, a, b]) => pure ("lt", a, b)
    | (``LE.le, #[_, _, a, b]) => pure ("le", a, b)
    | (``GT.gt, #[_, _, a, b]) => pure ("gt", a, b)
    | (``GE.ge, #[_, _, a, b]) => pure ("ge", a, b)
    | _ => return none
  let lenKind (e : Lean.Expr) : Option String := match e.getAppFnArgs with
    | (``String.length, #[x]) => if x == v then some "Length" else none
    | (``List.length, #[_, x]) => if x == v then some "Items" else none
    | (``Array.size, #[_, x]) => if x == v then some "Items" else none
    | _ => none
  let flip : String → String
    | "lt" => "gt" | "le" => "ge" | "gt" => "lt" | _ => "le"
  let (op, target, lit) := if a == v || (lenKind a).isSome then (op, a, b) else (flip op, b, a)
  let some c ← literalInt? lit | return none
  if let some k := lenKind target then
    return some <| match op with
      | "lt" => (s!"max{k}", c - 1)
      | "le" => (s!"max{k}", c)
      | "gt" => (s!"min{k}", c + 1)
      | _ => (s!"min{k}", c)
  unless target == v do return none
  return some <| match op with
    | "lt" => ("exclusiveMaximum", c)
    | "le" => ("maximum", c)
    | "gt" => ("exclusiveMinimum", c)
    | _ => ("minimum", c)

def slotOf : Compiler.LCNF.CtorFieldInfo → String × Nat
  | .object i _ => ("obj", i)
  | .usize i => ("usize", i)
  | .scalar sz off ty =>
    let s := match ty.constName?, sz with
      | some ``Float, _ => "f64"
      | some ``Float32, _ => "f32"
      | _, 1 => "u8"
      | _, 2 => "u16"
      | _, 4 => "u32"
      | _, _ => "u64"
    (s, off)
  | _ => ("none", 0)

def ppProp (strip : Name) (e : Lean.Expr) : MetaM String := do
  let f ← withTheReader Core.Context (fun c => { c with currNamespace := strip, openDecls := [] }) <|
    withOptions (fun o => o.setBool `pp.piBinderTypes false |>.setBool `pp.funBinderTypes false) (ppExpr e)
  return toString f

def ppType (e : Lean.Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr e))

def foreignAlias (spec : String) : MarshalM String := do
  match (← get).foreignImports.find? (·.2 == spec) with
  | some (a, _) => return a
  | none =>
    let a := s!"$x{(← get).foreignImports.size}"
    modify fun s => { s with foreignImports := s.foreignImports.push (a, spec) }
    return a

def modelTypes (m : ModelRef) : MarshalM (String × String) := do
  if m.module.isEmpty || m.exportName.isEmpty then return ("unknown", "unknown")
  let a ← match (← get).modelImports.find? (fun (_, s, e) => s == m.module && e == m.exportName) with
    | some (a, _, _) => pure a
    | none =>
      let a := s!"$m{(← get).modelImports.size}"
      modify fun s => { s with modelImports := s.modelImports.push (a, m.module, m.exportName) }
      pure a
  return (s!"L.InferOutput<typeof {a}>", s!"L.InferInput<typeof {a}>")

def unsupportedTypes : List Name :=
  [``ByteArray, ``FloatArray, ``Thunk, ``Task, ``IO.Ref, ``Decidable, ``String.Pos.Raw, ``Substring,
   ``String.Slice]

def unsupportedRoots : List Name := [`Std, `Lean, `IO, `EStateM, `ST, `System]

mutual

partial def descOf (t : Lean.Expr) : MarshalM Desc := do
  let t ← instantiateMVars t
  let t ← whnfR t
  let t := t.consumeMData
  if t.isForall then throwError "function type `{t}`"
  if t.isSort then throwError "type argument `{t}`"
  let args := t.getAppArgs
  let .const c _ := t.getAppFn | throwError "type variable `{t}`"
  match c, args with
  | ``Nat, #[] => return .nat
  | ``Int, #[] => return .int
  | ``Bool, #[] => return .bool
  | ``String, #[] => return .string
  | ``Char, #[] => return .char
  | ``UInt8, #[] => return .uint 8
  | ``UInt16, #[] => return .uint 16
  | ``UInt32, #[] => return .uint 32
  | ``UInt64, #[] => return .uint 64
  | ``USize, #[] => return .usize
  | ``Int8, #[] => return .sint 8
  | ``Int16, #[] => return .sint 16
  | ``Int32, #[] => return .sint 32
  | ``Int64, #[] => return .sint 64
  | ``ISize, #[] => return .isize
  | ``Float, #[] => return .float
  | ``Float32, #[] => return .float32
  | ``Unit, #[] | ``PUnit, #[] => return .unit
  | ``List, #[a] => return .list (← descOf a)
  | ``Array, #[a] => return .array (← descOf a)
  | ``Option, #[a] =>
    match ← descOf a with
    | .option _ => throwError "nested `Option` `{t}` (`none` and `some none` are both `{(← read).settings.option}`)"
    | d => return .option d
  | ``Prod, #[a, b] => return .prod (← descOf a) (← descOf b)
  | ``Except, #[e, a] => return .except (← descOf e) (← descOf a)
  | ``Fin, #[n] =>
    let some v ← (evalNat (← instantiateMVars n)).run
      | throwError "`Fin` with a bound that is not a literal: `{n}`"
    return .fin v
  | _, _ =>
    if t.hasFVar then throwError "type `{t}` of a type parameter"
    if unsupportedTypes.contains c || unsupportedRoots.contains c.getRoot then throwError "unsupported type `{t}`"
    match (← getEnv).find? c with
    | some (.defnInfo _) =>
      let some u ← unfoldDefinition? t | throwError "unsupported type `{t}`"
      let u ← whnfR u
      if u.getAppFn.constName? == some ``Subtype then namedDesc ``Subtype u u.getAppArgs (some c)
      else descOf u
    | some (.inductInfo _) => namedDesc c t args none
    | _ => throwError "unsupported type `{t}`"

partial def namedDesc (c : Name) (t : Lean.Expr) (args : Array Lean.Expr) (alias? : Option Name) :
    MarshalM Desc := do
  if let some d := (← get).byType[t]? then return d
  let env ← getEnv
  let cfg ← read
  let some (.inductInfo ind) := env.find? c | throwError "unsupported type `{t}`"
  if ind.numIndices != 0 then throwError "type family `{t}`"
  if isClass env c then throwError "type class `{t}`"
  if let some m := cfg.modelModules.find? (·.ns == c) then
    let (o, i) ← modelTypes m
    let ident ← freshIdent (typeIdentOf .anonymous c #[])
    let d := Desc.model ident m.key o i
    modify fun s => { s with byType := s.byType.insert t d }
    try
      let td ← typeDef c t args ident alias? false
      modify fun s => { s with types := s.types.push td }
    catch e =>
      modify fun s => { s with byType := s.byType.erase t }
      throw e
    return d
  let paramArgs ← args[:ind.numParams].toArray.filterM fun a => return !(← isProof a)
  if let some (ns, spec) := cfg.typeModules.find? fun (ns, _) => ns.isPrefixOf c && c != ns then
    if paramArgs.isEmpty && c != ``Subtype then
      let saved ← get
      discard <| typeDef c t args (typeIdentOf ns c #[]) alias? true
      set saved
      let a ← foreignAlias spec
      let d := Desc.foreign a (typeIdentOf ns c #[])
      modify fun s => { s with byType := s.byType.insert t d }
      return d
  let base ← if c == ``Subtype then
      match alias? with
      | some n => pure (typeIdentOf cfg.strip n #[])
      | none =>
        let k := (← get).subtypes
        modify fun s => { s with subtypes := k + 1 }
        pure s!"Subtype{k}"
    else
      let names ← paramArgs.mapM fun a => return toString (← ppExpr a)
      pure (typeIdentOf cfg.strip c names)
  let ident ← freshIdent base
  let d := Desc.named ident
  modify fun s => { s with byType := s.byType.insert t d }
  try
    let td ← typeDef c t args ident alias? false
    modify fun s => { s with types := s.types.push td }
  catch e =>
    modify fun s => { s with byType := s.byType.erase t, idents := s.idents.erase ident }
    throw e
  return d

partial def typeDef (c : Name) (t : Lean.Expr) (args : Array Lean.Expr) (ident : String) (alias? : Option Name)
    (external : Bool) : MarshalM TypeDef := do
  let env ← getEnv
  let cfg ← read
  let some (.inductInfo ind) := env.find? c | throwError "unsupported type `{t}`"
  let isStruct := isStructure env c
  let mut variants : Array VariantInfo := #[]
  for ctor in ind.ctors do
    let some (.ctorInfo ci) := env.find? ctor | throwError "unknown constructor {ctor}"
    let layout ← Compiler.LCNF.getCtorLayout ctor
    let ctorTy ← instantiateForall ci.type args[:ci.numParams]
    let ctorName := componentString ctor
    let v ← forallTelescopeReducing ctorTy fun fs _ => do
      let names ← fs.mapM (·.fvarId!.getUserName)
      let named := names.all (!·.hasMacroScopes)
      let mut fields : Array FieldInfo := #[]
      let mut invs : Array InvInfo := #[]
      let mut valueFvars : Array Lean.Expr := #[]
      let mut origIdx : Array Nat := #[]
      for h : i in [0:fs.size] do
        let f := fs[i]
        let ty ← inferType f
        let raw := componentString names[i]!.eraseMacroScopes
        if ← isProp ty then
          let ty := ty.headBeta
          for h : j in [0:valueFvars.size] do
            if let some b ← boundOf valueFvars[j] ty then
              fields := fields.modify j fun fi => { fi with bounds := fi.bounds.push b }
          let fname := if named then raw else s!"h{i}"
          let dn := deciderName ident ctorName (sanitize fname)
          unless external do
            compileDecider dn valueFvars ty
            modify fun s => { s with deciders := s.deciders.push dn }
          let prop ← ppProp cfg.strip ty
          invs := invs.push { field := fname, prop, decider := dn, args := (List.range valueFvars.size).toArray }
          continue
        if (← whnf ty).isSort then throwError "the constructor `{ctor}` has a type field `{raw}`"
        let d ← descOf ty
        let optKey := isStruct && raw.endsWith "?" && raw.length > 1
        let key := if !named then s!"a{fields.size}"
          else if isStruct then (raw.dropEndWhile (· == '?')).copy else raw
        let flat := isStruct && (isSubobjectField? env c names[i]!).isSome
        let isOpt := match d with | .option _ => true | _ => false
        let (slot, pos) := slotOf (layout.fieldInfo[i]?.getD .erased)
        if !isStruct && key == cfg.settings.tagKey then
          throwError "{tagKeyClash}the constructor `{ctor}` of `{t}` has a field `{key}`, which is the tagKey"
        fields := fields.push { key, slot, pos, desc := d, omitNone := optKey && isOpt, flat }
        valueFvars := valueFvars.push f
        origIdx := origIdx.push i
      let info := layout.ctorInfo
      return ({ name := ctorName, cidx := info.cidx, size := info.size, usize := info.usize, ssize := info.ssize,
                positional := !named, fields, invariants := invs : VariantInfo }, origIdx)
    variants := variants.push v.1
    if isStruct then
      let trivial ← Compiler.LCNF.hasTrivialStructure? c
      let tidx := trivial.bind fun ti => v.2.findIdx? (· == ti.fieldIdx)
      if c == ``Subtype then
        let some fi := v.1.fields[0]? | throwError "a subtype without a value: `{t}`"
        let some inv := v.1.invariants[0]? | throwError "a subtype without a property: `{t}`"
        return { ident, lean := alias?.getD c, pretty := ← ppType t, kind := .subtype fi.desc inv fi.bounds }
      return { ident, lean := c, pretty := ← ppType t, kind := .struct v.1 tidx,
               exported := !(cfg.modelModules.any (·.ns == c)) }
  let kind := if variants.all (fun v => v.fields.isEmpty && v.invariants.isEmpty) then
      TypeKind.enum (variants.map (·.name))
    else .sum variants
  return { ident, lean := c, pretty := ← ppType t, kind }

end

inductive ParamKind where
  | value (name : String) (d : Desc)
  | world
  deriving Inhabited

structure PublicSig where
  params : Array ParamKind
  result : Desc
  io : Bool
  type : String

def publicSig (name : Name) (ps : Array Param) : MarshalM PublicSig := do
  let some ci := (← getEnv).find? name | throwError "unknown constant {name}"
  let type := toString (← ppExpr ci.type)
  forallBoundedTelescope ci.type ps.size fun xs body => do
    if xs.size != ps.size then
      throwError "the IR has {ps.size} parameters but the type has {xs.size} binders"
    let body ← whnfR body
    let io := body.getAppFn.constName? == some `EST.Out
    if io then
      let errTy := body.getAppArgs[0]!.constName?
      unless errTy == some ``IO.Error do throwError "`EIO` with an error type other than `IO.Error`"
    let mut params := #[]
    let mut used : Std.HashSet String := {}
    for h : i in [0:xs.size] do
      let x := xs[i]
      let ldecl ← x.fvarId!.getDecl
      if io && i + 1 == xs.size then params := params.push .world; continue
      if ← isProp ldecl.type then throwError "takes a proof argument `{ldecl.userName}`"
      if (← whnf ldecl.type).isSort then throwError "polymorphic (takes the type `{ldecl.userName}`)"
      if ldecl.binderInfo.isInstImplicit then throwError "takes an instance argument `{ldecl.type}`"
      let d ← descOf ldecl.type
      let base := if ldecl.userName.hasMacroScopes then s!"arg{i}"
        else lowerCamel (componentString ldecl.userName.eraseMacroScopes)
      let base := if base == "_" then s!"arg{i}" else base
      let mut nm := base
      let mut k := 1
      while used.contains nm do
        nm := s!"{base}{k}"; k := k + 1
      used := used.insert nm
      params := params.push (.value nm d)
    let result ← if io then descOf body.getAppArgs[2]! else descOf body
    return { params, result, io, type }

end LeanTs
