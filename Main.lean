import Lean.Compiler.IR

open Lean Lean.IR

/-! # lean2ts: a Lean IR -> TypeScript backend (PoC), mirroring EmitC.

We obtain the IR `Decl` via `Lean.IR.findEnvDecl`, then walk `FnBody`/`Expr`
and emit TypeScript. Reference-counting nodes (inc/dec/del/reset/reuse) are
omitted because the JS engine has a tracing GC. -/

namespace Lean2ts

/-- Emission state: a buffer of output lines and an indent level. -/
structure EmitState where
  out    : String := ""
  indent : Nat    := 0

abbrev EmitM := StateM EmitState

def line (s : String) : EmitM Unit := do
  let st ← get
  let pad := String.mk (List.replicate (st.indent * 2) ' ')
  set { st with out := st.out ++ pad ++ s ++ "\n" }

def withIndent (act : EmitM Unit) : EmitM Unit := do
  modify (fun st => { st with indent := st.indent + 1 })
  act
  modify (fun st => { st with indent := st.indent - 1 })

/-- TS identifier for an IR variable. -/
def varName (x : VarId) : String := s!"x_{x.idx}"
def jpName  (j : JoinPointId) : String := s!"block_{j.idx}"

def argStr : Arg → String
  | .var id => varName id
  | .erased => "undefined"

/-- Map a Lean extern FunId (as used in `fap`) to a TS runtime expression.
    Returns `some applied` when the call is a known builtin we can inline. -/
def emitKnownFap (c : FunId) (ys : Array Arg) : Option String :=
  let a := ys.map argStr
  let bin (op : String) : Option String :=
    if h : a.size = 2 then some s!"({a[0]} {op} {a[1]})" else none
  match c with
  | `Nat.add => bin "+"
  | `Nat.mul => bin "*"
  | `Nat.sub =>
    if h : a.size = 2 then some s!"({a[0]} > {a[1]} ? {a[0]} - {a[1]} : 0n)" else none
  | `Nat.div =>
    if h : a.size = 2 then some s!"({a[1]} === 0n ? 0n : {a[0]} / {a[1]})" else none
  | `Nat.mod =>
    if h : a.size = 2 then some s!"({a[1]} === 0n ? {a[0]} : {a[0]} % {a[1]})" else none
  | `Nat.decEq =>
    if h : a.size = 2 then some s!"({a[0]} === {a[1]} ? 1 : 0)" else none
  | `Nat.decLt =>
    if h : a.size = 2 then some s!"({a[0]} < {a[1]} ? 1 : 0)" else none
  | `Nat.decLe =>
    if h : a.size = 2 then some s!"({a[0]} <= {a[1]} ? 1 : 0)" else none
  | _ => none

/-- TS function reference for an arbitrary (non-builtin) FunId. -/
def funRef (c : FunId) : String :=
  -- replace dots with _ to make a valid identifier
  (toString c).replace "." "_"

def ctorLit (i : CtorInfo) (ys : Array Arg) : String :=
  let fields := String.intercalate ", " (ys.toList.map argStr)
  let sz : Nat := i.size
  if sz == 0 && i.usize == 0 && i.ssize == 0 then
    -- nullary ctor / enum: mirror lean_box(cidx)
    s!"{i.cidx}"
  else
    "{ tag: " ++ toString i.cidx ++ ", fields: [" ++ fields ++ "] }"

def emitExpr : IR.Expr → String
  | .ctor i ys      => ctorLit i ys
  | .reset _ _      => "null"          -- GC: reuse token unused
  | .reuse _ i _ ys => ctorLit i ys    -- GC: identical to a fresh ctor
  | .proj i x       => s!"{varName x}.fields[{i}]"
  | .uproj i x      => s!"{varName x}.fields[{i}]"
  | .sproj n _ x    => s!"{varName x}.fields[{n}]"
  | .fap c ys       =>
    match emitKnownFap c ys with
    | some s => s
    | none   =>
      let args := String.intercalate ", " (ys.toList.map argStr)
      s!"{funRef c}({args})"
  | .pap c ys       =>
    let args := String.intercalate ", " (ys.toList.map argStr)
    "{ fn: " ++ funRef c ++ ", args: [" ++ args ++ "] }"
  | .ap x ys        =>
    let args := String.intercalate ", " (ys.toList.map argStr)
    s!"lean_apply({varName x}, [{args}])"
  | .box _ x        => varName x        -- GC: identity
  | .unbox x        => varName x        -- GC: identity
  | .lit (.num v)   => s!"{v}n"         -- Nat -> bigint
  | .lit (.str v)   => "\"" ++ v ++ "\""  -- JS string literal (naive)
  | .isShared _     => "0"  -- GC: never shared; Bool.false has cidx 0 (scalar switch matches)

/-- Emit a `FnBody` as TS statements appended to the buffer. -/
partial def emitFnBody : FnBody → EmitM Unit
  | .vdecl x _ e b => do
    line s!"const {varName x} = {emitExpr e};"
    emitFnBody b
  | .jdecl j xs v b => do
    -- join point as a local closure
    let params := String.intercalate ", " (xs.toList.map (fun p => varName p.x))
    line ("const " ++ jpName j ++ " = (" ++ params ++ ") => {")
    withIndent (emitFnBody v)
    line "};"
    emitFnBody b
  | .set x i y b => do
    line s!"{varName x}.fields[{i}] = {argStr y};"
    emitFnBody b
  | .setTag x cidx b => do
    line s!"{varName x}.tag = {cidx};"
    emitFnBody b
  | .uset x i y b => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitFnBody b
  | .sset x i _ y _ b => do
    line s!"{varName x}.fields[{i}] = {varName y};"
    emitFnBody b
  -- RC bookkeeping: omit under GC
  | .inc _ _ _ _ b => emitFnBody b
  | .dec _ _ _ _ b => emitFnBody b
  | .del _ b       => emitFnBody b
  | .ret x => line s!"return {argStr x};"
  | .jmp j ys =>
    let args := String.intercalate ", " (ys.toList.map argStr)
    line s!"return {jpName j}({args});"
  | .unreachable => line "throw new Error(\"unreachable\");"
  | .case _ x xType alts => do
    -- scalar scrutinee -> switch on value; object -> switch on .tag
    let scrut := if xType.isScalar then varName x else s!"{varName x}.tag"
    line ("switch (" ++ scrut ++ ") {")
    withIndent do
      let mut sawDefault := false
      for alt in alts do
        match alt with
        | .ctor info b => do
          line ("case " ++ toString info.cidx ++ ": {")
          withIndent (emitFnBody b)
          line "}"
        | .default b => do
          sawDefault := true
          line "default: {"
          withIndent (emitFnBody b)
          line "}"
      unless sawDefault do
        line "default: { throw new Error(\"no matching case\"); }"
    line "}"

/-- Emit a full top-level `Decl` as a TS function. -/
def emitDecl : Decl → EmitM Unit
  | .fdecl f xs _ body _ => do
    -- filter out erased/void params (mirrors EmitC void-arg filtering)
    let params := xs.toList.filter (fun p => !p.ty.isErased && !p.ty.isVoid)
    let paramStr := String.intercalate ", " (params.map (fun p => varName p.x))
    line ("function " ++ funRef f ++ "(" ++ paramStr ++ ") {")
    withIndent (emitFnBody body)
    line "}"
  | .extern f _ _ _ =>
    line s!"// extern {funRef f} (not emitted)"

/-- Run the emitter, returning the produced TS source. -/
def render (decls : Array Decl) : String := Id.run do
  let act : EmitM Unit := do
    for d in decls do
      emitDecl d
      line ""
  let (_, st) := act.run {}
  return st.out

end Lean2ts

-- ===========================================================================
-- Target functions to compile. Defining them here triggers Lean.compileDecl
-- so their IR lands in the environment and findEnvDecl returns it.
-- ===========================================================================

def double (n : Nat) : Nat := n + n

structure Point where
  x : Nat
  y : Nat

def mkShifted (p : Point) : Point := { x := p.x + 1, y := p.y + p.x }

def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    acc := acc + i
  return acc

/-- Collect IR for a name plus any auxiliary decls the compiler emitted that
    we also need (to keep it simple, we just emit the named decls). -/
def collectDecls (env : Environment) (names : Array Name) : Array Decl := Id.run do
  let mut acc := #[]
  for n in names do
    match Lean.IR.findEnvDecl env n with
    | some d => acc := acc.push d
    | none   => acc := acc
  return acc

def runtimePrelude : String :=
"// ---- lean2ts runtime prelude (minimal) ----
function lean_apply(clo, more) {
  if (typeof clo === 'function') return clo(...more);
  const all = clo.args.concat(more);
  return clo.fn(...all);
}
"

run_meta do
  let env ← getEnv
  let names := #[`double, `mkShifted]
  let decls := collectDecls env names
  IO.println s!"// collected {decls.size} decls"
  for d in decls do
    IO.println s!"// --- IR for {d.name} ---"
    IO.println (toString d)
  IO.println "// ================ GENERATED TS ================"
  IO.println (Lean2ts.render decls)

def main (args : List String) : IO Unit := do
  -- Args: output path; default ./out.ts
  let outPath := args.headD "out.ts"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Main }] {} (loadExts := true)
  let names := #[`double, `mkShifted]
  let decls := collectDecls env names
  let ts := runtimePrelude ++ "\n" ++ Lean2ts.render decls
  IO.FS.writeFile outPath ts
  IO.println s!"wrote {decls.size} decls to {outPath}"
