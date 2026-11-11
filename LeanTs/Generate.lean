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

def collectPublics (roots : Array Name) (strip : Name) : MetaM (Array PublicFn × Array Skipped) := do
  let env ← getEnv
  let mut publics := #[]
  let mut skipped := #[]
  let mut claims : Claims := {}
  for r in roots do
    let some decl := IR.findEnvDecl env r
      | skipped := skipped.push { name := r, reason := "no IR" }; continue
    let path := tsPath strip r
    let sig ← try pure (Except.ok (← publicSig r decl.params))
      catch e => pure (.error (← e.toMessageData.toString))
    match sig with
    | .error e => skipped := skipped.push { name := r, reason := e }
    | .ok sig =>
      match claims.claim path with
      | .error e => skipped := skipped.push { name := r, reason := e }
      | .ok c =>
        claims := c
        publics := publics.push { lean := r, path, decl, sig }
  return (publics, skipped)

structure DescTable where
  names : Std.HashMap String String := {}
  defs : Array String := #[]

def DescTable.get (t : DescTable) (d : Desc) : String × DescTable :=
  match t.names[d.code]? with
  | some n => (n, t)
  | none =>
    let n := s!"$d{t.defs.size}"
    (n, { names := t.names.insert d.code n,
          defs := t.defs.push s!"const {n}: L.TypeDesc<{d.outType}> = {d.code}" })

def docComment (f : PublicFn) : String :=
  let text := s!"Lean `{f.lean} : {f.sig.type}`."
  s!"/** {text.replace "*/" "*\\/"} */\n"

def emitPublicFn (f : PublicFn) (tbl : DescTable) (lazyIdx : Nat) : String × DescTable × Nat := Id.run do
  let mut tbl := tbl
  let mut sigParams := #[]
  let mut args := #[]
  for h : i in [0:f.sig.params.size] do
    let live := f.decl.params[i]?.map isLive |>.getD false
    match f.sig.params[i] with
    | .world => pure ()
    | .value nm desc =>
      let (dn, t) := tbl.get desc
      tbl := t
      sigParams := sigParams.push s!"{nm}: {desc.paramType}"
      let ty := f.decl.params[i]?.map (·.ty) |>.getD .object
      if live then args := args.push (coerce ty s!"L.toLean({dn}, {nm}, {quoteString nm})")
  let (rn, t) := tbl.get f.sig.result
  tbl := t
  let target := funRef f.lean
  let (pre, call, lazyIdx) :=
    if f.decl.params.isEmpty then
      let slot := s!"$c{lazyIdx}"
      (s!"const {slot}: () => Obj = L.lazy({target})\n", s!"{slot}()", lazyIdx + 1)
    else ("", s!"{target}({", ".intercalate args.toList})", lazyIdx)
  let ret := if f.sig.io then s!"L.ioResult({rn}, {call})" else s!"L.toTs({rn}, {call})"
  let exported := if f.path.size == 1 then "export " else ""
  let src := pre ++ docComment f ++
    s!"{exported}function {f.ident}({", ".intercalate sigParams.toList}): {f.sig.result.resultType} \{\n  return {ret}\n}\n\n"
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

def emitNamespaces (fns : Array PublicFn) : String := Id.run do
  let nested := fns.filter (·.path.size > 1)
  let tops := nested.foldl (fun acc f => if acc.contains f.path[0]! then acc else acc.push f.path[0]!) #[]
  let mut out := ""
  for top in tops do
    let entries := nested.toList.filterMap fun f =>
      if f.path[0]! == top then some (f.path.toList.drop 1, f.ident) else none
    let (ty, val) := nsObject entries 0
    out := out ++ s!"export const {top}: {ty} = {val}\n\n"
  return out

def renderPublic (fns : Array PublicFn) : String := Id.run do
  let mut tbl : DescTable := {}
  let mut lazyIdx := 0
  let mut src := ""
  for f in fns do
    let (s, t, k) := emitPublicFn f tbl lazyIdx
    src := src ++ s
    tbl := t
    lazyIdx := k
  let descs := String.join (tbl.defs.toList.map (· ++ "\n"))
  return descs ++ (if descs.isEmpty then "" else "\n") ++ src ++ emitNamespaces fns

end LeanTs
