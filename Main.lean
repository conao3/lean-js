import LeanJs.EmitJS
import LeanJs.Demo
import LeanJs.DemoHO
import LeanJs.DemoIO
import LeanJs.DemoInit
import LeanJs.DemoStress
import LeanJs.DemoStress2
import LeanJs.DemoStress3
import LeanJs.Fuzz
import LeanTodo.Basic

open Lean Lean.IR

/-! # lean-js CLI

Thin driver around `LeanJs.EmitJS`. Target functions live in imported library
modules so their IR is persisted in the `.olean` and visible to
`Lean.IR.findEnvDecl` when we re-import; we transitively collect dependencies
and emit a self-contained TypeScript module (prelude + generated functions). -/

/-- Root names to extract. LeanTodo functions exercise List, String, ctor/proj,
    Bool, and transitive helper-decl collection together. -/
def rootNames : Array Name := #[
  `LeanJs.Demo.double, `LeanJs.Demo.mkShifted, `LeanJs.Demo.sumTo, `LeanJs.Demo.fact,
  `LeanJs.Demo.mkMixed, `LeanJs.Demo.mixedSum,
  `LeanJs.Demo.u32wrap, `LeanJs.Demo.u8wrap,
  `LeanJs.Demo.intEdiv, `LeanJs.Demo.intEmod, `LeanJs.Demo.intNeg,
  `LeanJs.Demo.floatCalc,
  `LeanJs.Demo.strLen, `LeanJs.Demo.strBytes, `LeanJs.Demo.strGet0,
  `LeanJs.Demo.strGet1, `LeanJs.Demo.strExtract,
  `LeanJs.Demo.arrSum, `LeanJs.Demo.arrMapSum, `LeanJs.Demo.arrRange,
  `LeanJs.Demo.arrGetD, `LeanJs.Demo.arrAppend,
  `LeanJs.Demo.listSum, `LeanJs.Demo.listLen, `LeanJs.Demo.listRev,
  `LeanJs.Demo.listMapSum,
  `LeanJs.Demo.parityEven, `LeanJs.Demo.parityOdd, `LeanJs.Demo.cycle3,
  `LeanJs.Demo.i8wrap, `LeanJs.Demo.i8neg, `LeanJs.Demo.i8div, `LeanJs.Demo.i8mod,
  `LeanJs.Demo.i8shr, `LeanJs.Demo.i16wrap, `LeanJs.Demo.i32wrap, `LeanJs.Demo.i64mul,
  `LeanJs.Demo.i8toInt, `LeanJs.Demo.i32toInt,
  `LeanJs.Demo.floatStr, `LeanJs.Demo.float32Str,
  `LeanJs.Demo.mkSPack, `LeanJs.Demo.spackA, `LeanJs.Demo.spackB, `LeanJs.Demo.spackC,
  `LeanJs.Demo.spackE, `LeanJs.Demo.spackF, `LeanJs.Demo.spackG, `LeanJs.Demo.spackSum,
  `LeanJs.Demo.chainHead, `LeanJs.Demo.pingN,
  `LeanJs.Demo.ftan, `LeanJs.Demo.fasin, `LeanJs.Demo.facos, `LeanJs.Demo.fatan,
  `LeanJs.Demo.fatan2, `LeanJs.Demo.fsinh, `LeanJs.Demo.fcosh, `LeanJs.Demo.ftanh,
  `LeanJs.Demo.fexp2, `LeanJs.Demo.flog2, `LeanJs.Demo.flog10, `LeanJs.Demo.fcbrt,
  `LeanJs.Demo.ftoBits, `LeanJs.Demo.fofBits, `LeanJs.Demo.ffrExpM, `LeanJs.Demo.ffrExpE,
  `LeanJs.Demo.f32tan, `LeanJs.Demo.f32exp, `LeanJs.Demo.f32log, `LeanJs.Demo.f32cbrt,
  `LeanJs.Demo.f32toBits,
  `LeanJs.Demo.nbits, `LeanJs.Demo.uszOfU64, `LeanJs.Demo.uszAdd,
  `LeanJs.Demo.uszCompl, `LeanJs.Demo.uszToNat,
  `LeanJs.DemoHO.hofApply,
  `LeanJs.DemoHO.listMapLam, `LeanJs.DemoHO.listFilterLam, `LeanJs.DemoHO.listFoldlLam,
  `LeanJs.DemoHO.arrMapLam,
  `LeanJs.DemoHO.applyAdders, `LeanJs.DemoHO.currySplit,
  `LeanJs.DemoHO.optSeq, `LeanJs.DemoHO.exSeq, `LeanJs.DemoHO.fmapList,
  `LeanJs.DemoHO.safeDivStr, `LeanJs.DemoHO.hmDemo,
  `LeanJs.DemoHO.cpsCount, `LeanJs.DemoHO.cpsSum,
  `LeanTodo.TodoList.add,
  `LeanTodo.TodoList.toggle,
  `LeanTodo.TodoList.remove,
  `LeanTodo.TodoList.step,
  `LeanJs.Fuzz.fNat, `LeanJs.Fuzz.fInt, `LeanJs.Fuzz.fU32, `LeanJs.Fuzz.fU8,
  `LeanJs.Fuzz.fStr, `LeanJs.Fuzz.fHash, `LeanJs.Fuzz.fListNat, `LeanJs.Fuzz.fArrNat
]

def main (args : List String) : IO Unit := do
  let outPath := args.headD "out.ts"
  let preludePath := args.getD 1 "prelude.ts"
  let progPath := args.getD 2 "out-io.mjs"
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `LeanJs.Demo }, { module := `LeanJs.DemoHO },
      { module := `LeanJs.DemoIO }, { module := `LeanJs.DemoInit },
      { module := `LeanJs.DemoStress }, { module := `LeanJs.DemoStress2 },
      { module := `LeanJs.DemoStress3 }, { module := `LeanJs.Fuzz },
      { module := `LeanTodo.Basic }] {}
    (loadExts := true)
  let prelude ← IO.FS.readFile preludePath
  let decls := LeanJs.collectTransitive env rootNames
  -- Fail loud (non-zero exit, no output written) if any reached extern has no
  -- prelude symbol — the analogue of a C linker rejecting an unresolved symbol.
  let body ← match LeanJs.renderChecked env decls with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"lean-js: {e}")
  let ts := prelude ++ "\n// ================ GENERATED ================\n\n" ++ body
  IO.FS.writeFile outPath ts
  IO.println s!"wrote {decls.size} decls to {outPath}"
  let progBody ← match LeanJs.renderProgramChecked env `LeanJs.DemoIO.main with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"lean-js: {e}")
  let prog := prelude ++ "\n// ================ GENERATED PROGRAM ================\n\n" ++ progBody
  IO.FS.writeFile progPath prog
  IO.println s!"wrote runnable program to {progPath}"
  -- Extra IO programs: stdin echo + an error-throwing program, each a
  -- self-contained runnable module diff-tested against `lean --run`.
  let emitProg (root : Name) (path : String) : IO Unit := do
    match LeanJs.renderProgramChecked env root with
    | .ok body =>
      IO.FS.writeFile path
        (prelude ++ "\n// ================ GENERATED PROGRAM ================\n\n" ++ body)
      IO.println s!"wrote runnable program to {path}"
    | .error e => throw (IO.userError s!"lean-js: {e}")
  emitProg `LeanJs.DemoIO.stdinEcho "out-stdin.mjs"
  emitProg `LeanJs.DemoIO.errMain "out-err.mjs"
  emitProg `LeanJs.DemoIO.panicMain "out-panic.mjs"
  emitProg `LeanJs.DemoInit.main "out-init.mjs"
  emitProg `LeanJs.DemoStress.stressMain "out-stress.mjs"
  emitProg `LeanJs.DemoStress2.stress2Main "out-stress2.mjs"
  emitProg `LeanJs.DemoStress3.stress3Main "out-stress3.mjs"
