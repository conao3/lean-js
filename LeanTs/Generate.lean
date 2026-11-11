import Lean
import LeanTs.EmitTs
import LeanTs.Marshal

open Lean Meta

namespace LeanTs

structure Skipped where
  name : Name
  reason : String

structure PublicFn where
  lean : Name
  path : Array String
  decl : IR.Decl
  sig : PublicSig

def PublicFn.ident (f : PublicFn) : String := "$".intercalate f.path.toList

def PublicFn.dotted (f : PublicFn) : String := ".".intercalate f.path.toList

structure Claims where
  fns : Std.HashSet String := {}
  namespaces : Std.HashSet String := {}

def prefixes (path : Array String) : Array String := Id.run do
  let mut out := #[]
  for i in [1:path.size] do
    out := out.push (".".intercalate (path.extract 0 i).toList)
  return out

def Claims.claim (c : Claims) (path : Array String) : Except String Claims := do
  let full := ".".intercalate path.toList
  if c.fns.contains full || c.namespaces.contains full then
    throw s!"the TypeScript name `{full}` is already used"
  for p in prefixes path do
    if c.fns.contains p then throw s!"the TypeScript name `{p}` is a function and a namespace"
  return { fns := c.fns.insert full, namespaces := (prefixes path).foldl (·.insert ·) c.namespaces }

structure Collected where
  publics : Array PublicFn
  skipped : Array Skipped
  fatal : Array String := #[]
  state : MarshalState

def collectPublics (types roots : Array Name) : MarshalM Collected := do
  let env ← getEnv
  let strip := (← read).strip
  let mut publics := #[]
  let mut skipped := #[]
  let mut claims : Claims := {}
  let mut fatal := #[]
  for c in types do
    let saved ← get
    try discard <| descOf (mkConst c)
    catch e =>
      set saved
      skipped := skipped.push { name := c, reason := ← e.toMessageData.toString }
  for r in roots do
    let some decl := IR.findEnvDecl env r
      | skipped := skipped.push { name := r, reason := "no IR" }; continue
    let path := tsPath strip r
    let saved ← get
    let sig ← try pure (Except.ok (← publicSig r decl.params))
      catch e => pure (.error (← e.toMessageData.toString))
    match sig with
    | .error e =>
      set saved
      skipped := skipped.push { name := r, reason := e }
    | .ok sig =>
      match claims.claim path with
      | .error e =>
        set saved
        skipped := skipped.push { name := r, reason := e }
      | .ok c =>
        claims := c
        publics := publics.push { lean := r, path, decl, sig }
  for s in skipped do
    if let some i := (s.reason.splitOn tagKeyClash)[1]? then
      unless fatal.contains i do fatal := fatal.push i
  return { publics, skipped, fatal, state := ← get }

structure DescTable where
  names : Std.HashMap String String := {}
  defs : Array String := #[]

def DescTable.get (s : Settings) (t : DescTable) (d : Desc) : String × DescTable :=
  let code := d.code s false
  match t.names[code]? with
  | some n => (n, t)
  | none =>
    let n := s!"$d{t.defs.size}"
    (n, { names := t.names.insert code n,
          defs := t.defs.push s!"const {n}: L.TypeDesc<{d.outType s}> = {code}" })

def docComment (text : String) : String :=
  s!"/** {text.replace "*/" "*\\/"} */\n"

def emitPublicFn (s : Settings) (f : PublicFn) (tbl : DescTable) (lazyIdx : Nat) : String × DescTable × Nat := Id.run do
  let mut tbl := tbl
  let mut sigParams := #[]
  let mut args := #[]
  for h : i in [0:f.sig.params.size] do
    let live := f.decl.params[i]?.map isLive |>.getD false
    match f.sig.params[i] with
    | .world => pure ()
    | .value nm desc =>
      let (dn, t) := tbl.get s desc
      tbl := t
      sigParams := sigParams.push s!"{nm}: {desc.paramType s}"
      let ty := f.decl.params[i]?.map (·.ty) |>.getD .object
      if live then args := args.push (coerce ty s!"L.toLean({dn}, {nm}, {quoteString nm})")
  let (rn, t) := tbl.get s f.sig.result
  tbl := t
  let target := funRef f.lean
  let (pre, call, lazyIdx) :=
    if f.decl.params.isEmpty then
      let slot := s!"$c{lazyIdx}"
      (s!"const {slot}: () => Obj = L.lazy({target})\n", s!"{slot}()", lazyIdx + 1)
    else ("", s!"{target}({", ".intercalate args.toList})", lazyIdx)
  let ret := if f.sig.io then s!"L.ioResult({rn}, {call})" else s!"L.toTs({rn}, {call})"
  let exported := if f.path.size == 1 then "export " else ""
  let src := pre ++ docComment s!"Lean `{f.lean} : {f.sig.type}`." ++
    s!"{exported}function {f.ident}({", ".intercalate sigParams.toList}): {f.sig.result.resultType s} \{\n  return {ret}\n}\n\n"
  return (src, tbl, lazyIdx)

partial def nsObject (entries : List (List String × String)) (indent : Nat) : String × String :=
  let pad := String.ofList (List.replicate (indent * 2) ' ')
  let inner := String.ofList (List.replicate ((indent + 1) * 2) ' ')
  let heads := entries.foldl (fun acc (p, _) => match p with
    | h :: _ => if acc.contains h then acc else acc ++ [h]
    | [] => acc) []
  let members := heads.map fun h =>
    let sub := entries.filterMap fun (p, v) => match p with
      | h' :: rest => if h' == h then some (rest, v) else none
      | [] => none
    match sub with
    | [([], v)] => (s!"{inner}readonly {h}: typeof {v}", s!"{inner}{h}: {v}")
    | _ =>
      let (ty, val) := nsObject sub (indent + 1)
      (s!"{inner}readonly {h}: {ty}", s!"{inner}{h}: {val}")
  let ty := "{\n" ++ String.join (members.map (·.1 ++ "\n")) ++ pad ++ "}"
  let val := "{\n" ++ String.join (members.map (·.2 ++ ",\n")) ++ pad ++ "}"
  (ty, val)

def schemaType (ident : String) : String := s!"L.LeanSchema<{ident}Input, {ident}>"

def schemaValue (ident : String) : String := s!"L.schema<{ident}Input, {ident}>($t{ident})"

def emitNamespaces (fns : Array PublicFn) (schemas : Std.HashSet String) : String × Std.HashSet String := Id.run do
  let nested := fns.filter (·.path.size > 1)
  let tops := nested.foldl (fun acc f => if acc.contains f.path[0]! then acc else acc.push f.path[0]!) #[]
  let mut out := ""
  let mut merged : Std.HashSet String := {}
  for top in tops do
    let entries := nested.toList.filterMap fun f =>
      if f.path[0]! == top then some (f.path.toList.drop 1, f.ident) else none
    let (ty, val) := nsObject entries 0
    if schemas.contains top then
      merged := merged.insert top
      out := out ++ s!"export const {top}: {schemaType top} & {ty} = L.merge({schemaValue top}, {val})\n\n"
    else
      out := out ++ s!"export const {top}: {ty} = {val}\n\n"
  return (out, merged)

def propName (key : String) : String := if isJsIdent key then key else quoteString key

def objectType (parts : Array String) : String :=
  if parts.isEmpty then "Readonly<Record<string, never>>" else "{ " ++ "; ".intercalate parts.toList ++ " }"

def variantOut (s : Settings) (v : VariantInfo) (tag : Option String) : String :=
  let head := match tag with
    | some n => #[s!"readonly {propName s.tagKey}: {quoteString n}"]
    | none => #[]
  let parts := v.fields.filter (!·.flat) |>.map fun f =>
    match f.desc with
    | .option d =>
      if s.option == "undefined" then s!"readonly {propName f.key}?: {d.outType s}"
      else s!"readonly {propName f.key}: {f.desc.outType s}"
    | d => s!"readonly {propName f.key}: {d.outType s}"
  let flats := v.fields.filter (·.flat) |>.map fun f => f.desc.outType s
  " & ".intercalate (flats.push (objectType (head ++ parts))).toList

def variantIn (s : Settings) (v : VariantInfo) : String :=
  let parts := v.fields.filter (!·.flat) |>.map fun f =>
    match f.desc with
    | .option _ => s!"readonly {propName f.key}?: {f.desc.jsonType s}"
    | d => s!"readonly {propName f.key}: {d.jsonType s}"
  let flats := v.fields.filter (·.flat) |>.map fun f => f.desc.jsonType s
  " & ".intercalate (flats.push (objectType parts)).toList

def unionOf (parts : Array String) : String :=
  if parts.isEmpty then "never" else " | ".intercalate parts.toList

def TypeDef.outType (s : Settings) (td : TypeDef) : String :=
  match td.kind with
  | .struct v _ => variantOut s v none
  | .enum cs => unionOf (cs.map quoteString)
  | .sum vs => unionOf (vs.map fun v => variantOut s v (some v.name))
  | .subtype base _ _ => base.outType s

def TypeDef.inType (s : Settings) (td : TypeDef) : String :=
  match td.kind with
  | .struct v _ => variantIn s v
  | .enum cs => unionOf (cs.map quoteString)
  | .sum vs => unionOf <| vs.map fun v =>
    if v.fields.isEmpty then quoteString v.name
    else
      let payload := if !v.positional then variantIn s v
        else if v.fields.size == 1 then v.fields[0]!.desc.jsonType s
        else s!"readonly [{", ".intercalate (v.fields.toList.map (·.desc.jsonType s))}]"
      s!"\{ readonly {propName v.name}: {payload} }"
  | .subtype base _ _ => base.jsonType s

def boundsLit (bs : Array (String × Int)) : String :=
  if bs.isEmpty then "{}" else "{ " ++ ", ".intercalate (bs.toList.map fun (k, v) => s!"{k}: {v}") ++ " }"

def boolLit (b : Bool) : String := if b then "true" else "false"

def fieldLit (s : Settings) (f : FieldInfo) : String :=
  s!"\{ key: {quoteString f.key}, desc: {f.desc.code s true}, slot: {quoteString f.slot}, at: {f.pos}, omitNone: {boolLit f.omitNone}, flat: {boolLit f.flat}, bounds: {boundsLit f.bounds} }"

def invLit (deciders : Std.HashMap Name String) (inv : InvInfo) : String :=
  let args := ", ".intercalate (inv.args.toList.map toString)
  s!"\{ field: {quoteString inv.field}, prop: {quoteString inv.prop}, args: [{args}], decide: {deciders.getD inv.decider "undefined"} }"

def variantLit (s : Settings) (deciders : Std.HashMap Name String) (v : VariantInfo) : String :=
  let fields := ", ".intercalate (v.fields.toList.map (fieldLit s))
  let invs := ", ".intercalate (v.invariants.toList.map (invLit deciders))
  s!"\{ name: {quoteString v.name}, cidx: {v.cidx}, size: {v.size}, usize: {v.usize}, ssize: {v.ssize}, positional: {boolLit v.positional}, fields: [{fields}], invariants: [{invs}] }"

def typeLit (s : Settings) (deciders : Std.HashMap Name String) (td : TypeDef) : String :=
  let name := quoteString td.ident
  match td.kind with
  | .struct v tr =>
    let tr := match tr with | some i => toString i | none => "null"
    s!"\{ kind: \"struct\", name: {name}, trivial: {tr}, variant: {variantLit s deciders v} }"
  | .enum cs => s!"\{ kind: \"enum\", name: {name}, ctors: [{", ".intercalate (cs.toList.map quoteString)}] }"
  | .sum vs =>
    s!"\{ kind: \"inductive\", name: {name}, tagKey: {quoteString s.tagKey}, variants: [{", ".intercalate (vs.toList.map (variantLit s deciders))}] }"
  | .subtype base inv bs =>
    s!"\{ kind: \"subtype\", name: {name}, base: {base.code s true}, invariant: {invLit deciders inv}, bounds: {boundsLit bs} }"

def emitDecider (d : IR.Decl) (n : Name) (ident : String) : String :=
  let ps := d.params.mapIdx fun i _ => s!"a{i}: Obj"
  let args := d.params.mapIdx (fun i p => (p, s!"a{i}")) |>.filter (isLive ·.1) |>.map fun (p, a) => coerce p.ty a
  s!"const {ident} = ({", ".intercalate ps.toList}): boolean => {funRef n}({", ".intercalate args.toList}) !== 0\n"

structure PublicOut where
  imports : String
  body : String
  types : Array TypeDef

def invariantsOf (td : TypeDef) : Array InvInfo :=
  match td.kind with
  | .struct v _ => v.invariants
  | .sum vs => vs.flatMap (·.invariants)
  | .subtype _ inv _ => #[inv]
  | .enum _ => #[]

def renderPublic (env : Environment) (s : Settings) (fns : Array PublicFn) (st : MarshalState) :
    Except String PublicOut := do
  let imports := String.join (st.foreignImports.toList.map fun (a, m) => s!"import * as {a} from {quoteString m}\n") ++
    String.join (st.modelImports.toList.map fun (a, m, e) => s!"import type \{ {e} as {a} } from {quoteString m}\n")
  let mut deciders : Std.HashMap Name String := {}
  let mut deciderSrc := ""
  for n in st.deciders do
    unless deciders.contains n do
      let some d := IR.findEnvDecl env n | throw s!"{n}: the decider has no IR"
      let ident := s!"$v{deciders.size}"
      deciders := deciders.insert n ident
      deciderSrc := deciderSrc ++ emitDecider d n ident
  for td in st.types do
    for inv in invariantsOf td do
      unless deciders.contains inv.decider do throw s!"{inv.decider}: the decider of {td.lean} was not compiled"
  let mut aliases := ""
  let mut descs := ""
  let mut schemas : Std.HashSet String := {}
  for td in st.types do
    if td.exported then
      aliases := aliases ++ docComment s!"Lean `{td.pretty}`." ++
        s!"export type {td.ident} = {td.outType s}\n" ++
        docComment s!"The JSON form of Lean `{td.pretty}`." ++
        s!"export type {td.ident}Input = {td.inType s}\n\n"
      descs := descs ++ s!"const $t{td.ident}: L.TypeDesc<{td.ident}> = L.typeDesc({typeLit s deciders td})\n"
      schemas := schemas.insert td.ident
    else
      descs := descs ++ s!"const $t{td.ident}: L.TypeDesc = L.typeDesc({typeLit s deciders td})\n"
  let mut tbl : DescTable := {}
  let mut lazyIdx := 0
  let mut src := ""
  for f in fns do
    let (out, t, k) := emitPublicFn s f tbl lazyIdx
    src := src ++ out
    tbl := t
    lazyIdx := k
  let (nsSrc, merged) := emitNamespaces fns schemas
  let mut schemaSrc := ""
  for td in st.types do
    if td.exported && !merged.contains td.ident then
      schemaSrc := schemaSrc ++ s!"export const {td.ident}: {schemaType td.ident} = {schemaValue td.ident}\n"
  let part (x : String) := if x.isEmpty then "" else x ++ "\n"
  let fnDescs := String.join (tbl.defs.toList.map (· ++ "\n"))
  let body := part aliases ++ part deciderSrc ++ part descs ++ part schemaSrc ++ part fnDescs ++ src ++ nsSrc
  return { imports, body, types := st.types.filter (·.exported) }

end LeanTs
