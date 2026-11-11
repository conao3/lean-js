import Lean

open Lean Meta

namespace LeanTs

def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

structure ObligationRef where
  model : Name
  label : String

def ObligationRef.labelName (o : ObligationRef) : Name :=
  (o.label.splitOn ".").foldl Name.str .anonymous

def ObligationRef.statement (o : ObligationRef) : Name := o.model ++ `obligation ++ o.labelName

def ObligationRef.theorem (o : ObligationRef) : Name := o.model ++ `proof ++ o.labelName

def moduleFile (mod : Name) : String :=
  "/".intercalate (mod.components.map toString) ++ ".lean"

def checkObligation (o : ObligationRef) : MetaM Json := do
  let env ← getEnv
  let base := [("model", toJson o.model.toString), ("label", toJson o.label)]
  let stmt := o.statement
  let thm := o.theorem
  unless env.contains stmt do
    return Json.mkObj (base ++ [("status", toJson "unextracted"), ("detail", toJson s!"{stmt} is not defined")])
  let some ci := env.find? thm | return Json.mkObj (base ++ [("status", toJson "missing")])
  let mod := match env.getModuleIdxFor? thm with
    | some idx => moduleFile env.header.moduleNames[idx.toNat]!
    | none => ""
  let line := match ← findDeclarationRanges? thm with
    | some r => r.range.pos.line
    | none => 0
  let place := [("file", toJson mod), ("line", toJson line)]
  let expected := mkConst stmt
  let same ← if ci.type == expected then pure true
    else try withTransparency .default (isDefEq ci.type expected) catch _ => pure false
  unless same do
    return Json.mkObj (base ++ place ++ [("status", toJson "mismatch"), ("detail", toJson s!"{thm} : {← ppExpr ci.type}")])
  let axioms := (← collectAxioms thm).toList.map (·.toString) |>.mergeSort (· ≤ ·)
  let status :=
    if axioms.contains "sorryAx" then "sorry"
    else if axioms.all (fun a => standardAxioms.contains a.toName) then "proved"
    else "axioms"
  return Json.mkObj (base ++ place ++ [("status", toJson status), ("axioms", toJson axioms)])

def parseObligations (j : Json) : Except String (Array ObligationRef) := do
  let arr ← j.getArr?
  arr.mapM fun e => do
    let model := (← e.getObjValAs? String "model").toName
    let label ← e.getObjValAs? String "label"
    return { model, label }

end LeanTs
