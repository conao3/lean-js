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

def lowerCamel (s : String) : String :=
  tsIdent <| match camelParts s with
    | [] => ""
    | p :: ps => p.decapitalize ++ String.join (ps.map String.capitalize)

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
  | some last => cs.pop.map namespaceIdent |>.push (lowerCamel last)

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
  deriving Inhabited, BEq

def arrayElem (s : String) : String :=
  if s.contains '|' then s!"({s})" else s

partial def Desc.code : Desc → String
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
  | .list d => s!"L.listDesc({d.code})"
  | .array d => s!"L.arrayDesc({d.code})"
  | .option d => s!"L.optionDesc({d.code})"
  | .prod a b => s!"L.prodDesc({a.code}, {b.code})"
  | .except e a => s!"L.exceptDesc({e.code}, {a.code})"

partial def Desc.outType : Desc → String
  | .nat | .int | .usize | .isize => "bigint"
  | .uint b | .sint b => if b == 64 then "bigint" else "number"
  | .bool => "boolean"
  | .char | .string => "string"
  | .float | .float32 => "number"
  | .unit => "undefined"
  | .list d | .array d => s!"{arrayElem d.outType}[]"
  | .option d => s!"{d.outType} | null"
  | .prod a b => s!"readonly [{a.outType}, {b.outType}]"
  | .except e a => s!"L.Except<{e.outType}, {a.outType}>"

partial def Desc.inType : Desc → String
  | .nat | .int => "bigint | number"
  | .list d | .array d => s!"readonly {arrayElem d.inType}[]"
  | .option d => s!"{d.inType} | null"
  | .prod a b => s!"readonly [{a.inType}, {b.inType}]"
  | .except e a => s!"L.Except<{e.inType}, {a.inType}>"
  | d => d.outType

def Desc.paramType : Desc → String
  | .unit => "void"
  | d => d.inType

def Desc.resultType : Desc → String
  | .unit => "void"
  | d => d.outType

partial def descOf (t : Lean.Expr) : MetaM Desc := do
  let t ← whnfR (← instantiateMVars t)
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
    | .option _ => throwError "nested `Option` `{t}` (`none` and `some none` are both `null`)"
    | d => return .option d
  | ``Prod, #[a, b] => return .prod (← descOf a) (← descOf b)
  | ``Except, #[e, a] => return .except (← descOf e) (← descOf a)
  | _, _ =>
    if t.hasFVar then throwError "type `{t}` of a type parameter"
    throwError "unsupported type `{t}`"

inductive ParamKind where
  | value (name : String) (d : Desc)
  | world
  deriving Inhabited

structure PublicSig where
  params : Array ParamKind
  result : Desc
  io : Bool
  type : String

def publicSig (name : Name) (ps : Array Param) : MetaM PublicSig := do
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
