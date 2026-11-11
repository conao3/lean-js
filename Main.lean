import LeanTs.EmitTs
import LeanTs.Demo
import LeanTs.DemoHO
import LeanTs.DemoIO
import LeanTs.DemoInit
import LeanTs.DemoStress
import LeanTs.DemoStress2
import LeanTs.DemoStress3
import LeanTs.DemoStress4
import LeanTs.DemoVerify
import LeanTs.Fuzz
import LeanTodo.Basic

open Lean Lean.IR

/-! # lean-typescript CLI

Thin driver around `LeanTs.EmitTs`. Target functions live in imported library
modules so their IR is persisted in the `.olean` and visible to
`Lean.IR.findEnvDecl` when we re-import; we transitively collect dependencies
and emit a self-contained TypeScript module (prelude + generated functions). -/

/-- Root names to extract. LeanTodo functions exercise List, String, ctor/proj,
    Bool, and transitive helper-decl collection together. -/
def rootNames : Array Name := #[
  `LeanTs.Demo.double, `LeanTs.Demo.mkShifted, `LeanTs.Demo.sumTo, `LeanTs.Demo.fact,
  `LeanTs.Demo.mkMixed, `LeanTs.Demo.mixedSum,
  `LeanTs.Demo.u32wrap, `LeanTs.Demo.u8wrap,
  `LeanTs.Demo.intEdiv, `LeanTs.Demo.intEmod, `LeanTs.Demo.intNeg,
  `LeanTs.Demo.floatCalc,
  `LeanTs.Demo.strLen, `LeanTs.Demo.strBytes, `LeanTs.Demo.strGet0,
  `LeanTs.Demo.strGet1, `LeanTs.Demo.strExtract,
  `LeanTs.Demo.arrSum, `LeanTs.Demo.arrMapSum, `LeanTs.Demo.arrRange,
  `LeanTs.Demo.arrGetD, `LeanTs.Demo.arrAppend,
  `LeanTs.Demo.listSum, `LeanTs.Demo.listLen, `LeanTs.Demo.listRev,
  `LeanTs.Demo.listMapSum,
  `LeanTs.Demo.parityEven, `LeanTs.Demo.parityOdd, `LeanTs.Demo.cycle3,
  `LeanTs.Demo.i8wrap, `LeanTs.Demo.i8neg, `LeanTs.Demo.i8div, `LeanTs.Demo.i8mod,
  `LeanTs.Demo.i8shr, `LeanTs.Demo.i16wrap, `LeanTs.Demo.i32wrap, `LeanTs.Demo.i64mul,
  `LeanTs.Demo.i8toInt, `LeanTs.Demo.i32toInt,
  `LeanTs.Demo.floatStr, `LeanTs.Demo.float32Str,
  `LeanTs.Demo.mkSPack, `LeanTs.Demo.spackA, `LeanTs.Demo.spackB, `LeanTs.Demo.spackC,
  `LeanTs.Demo.spackE, `LeanTs.Demo.spackF, `LeanTs.Demo.spackG, `LeanTs.Demo.spackSum,
  `LeanTs.Demo.chainHead, `LeanTs.Demo.pingN,
  `LeanTs.Demo.ftan, `LeanTs.Demo.fasin, `LeanTs.Demo.facos, `LeanTs.Demo.fatan,
  `LeanTs.Demo.fatan2, `LeanTs.Demo.fsinh, `LeanTs.Demo.fcosh, `LeanTs.Demo.ftanh,
  `LeanTs.Demo.fexp2, `LeanTs.Demo.flog2, `LeanTs.Demo.flog10, `LeanTs.Demo.fcbrt,
  `LeanTs.Demo.ftoBits, `LeanTs.Demo.fofBits, `LeanTs.Demo.ffrExpM, `LeanTs.Demo.ffrExpE,
  `LeanTs.Demo.f32tan, `LeanTs.Demo.f32exp, `LeanTs.Demo.f32log, `LeanTs.Demo.f32cbrt,
  `LeanTs.Demo.f32toBits,
  `LeanTs.Demo.nbits, `LeanTs.Demo.uszOfU64, `LeanTs.Demo.uszAdd,
  `LeanTs.Demo.uszCompl, `LeanTs.Demo.uszToNat,
  `LeanTs.DemoHO.hofApply,
  `LeanTs.DemoHO.listMapLam, `LeanTs.DemoHO.listFilterLam, `LeanTs.DemoHO.listFoldlLam,
  `LeanTs.DemoHO.arrMapLam,
  `LeanTs.DemoHO.applyAdders, `LeanTs.DemoHO.currySplit,
  `LeanTs.DemoHO.optSeq, `LeanTs.DemoHO.exSeq, `LeanTs.DemoHO.fmapList,
  `LeanTs.DemoHO.safeDivStr, `LeanTs.DemoHO.hmDemo,
  `LeanTs.DemoHO.cpsCount, `LeanTs.DemoHO.cpsSum,
  `LeanTodo.TodoList.add,
  `LeanTodo.TodoList.toggle,
  `LeanTodo.TodoList.remove,
  `LeanTodo.TodoList.step,
  `LeanTs.Fuzz.fNat, `LeanTs.Fuzz.fInt, `LeanTs.Fuzz.fU32, `LeanTs.Fuzz.fU8,
  `LeanTs.Fuzz.fStr, `LeanTs.Fuzz.fHash, `LeanTs.Fuzz.fListNat, `LeanTs.Fuzz.fArrNat
]

def main (args : List String) : IO Unit := do
  let outPath := args.headD "out.ts"
  let preludePath := args.getD 1 "prelude.ts"
  let progPath := args.getD 2 "out-io.mjs"
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `LeanTs.Demo }, { module := `LeanTs.DemoHO },
      { module := `LeanTs.DemoIO }, { module := `LeanTs.DemoInit },
      { module := `LeanTs.DemoStress }, { module := `LeanTs.DemoStress2 },
      { module := `LeanTs.DemoStress3 }, { module := `LeanTs.DemoStress4 },
      { module := `LeanTs.DemoVerify },
      { module := `LeanTs.Fuzz },
      { module := `LeanTodo.Basic }] {}
  let prelude ← IO.FS.readFile preludePath
  let decls := LeanTs.collectTransitive env rootNames
  -- Fail loud (non-zero exit, no output written) if any reached extern has no
  -- prelude symbol — the analogue of a C linker rejecting an unresolved symbol.
  let body ← match LeanTs.renderChecked env decls with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"lean-typescript: {e}")
  let ts := prelude ++ "\n// ================ GENERATED ================\n\n" ++ body
  IO.FS.writeFile outPath ts
  IO.println s!"wrote {decls.size} decls to {outPath}"
  let progBody ← match LeanTs.renderProgramChecked env `LeanTs.DemoIO.main with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"lean-typescript: {e}")
  let prog := prelude ++ "\n// ================ GENERATED PROGRAM ================\n\n" ++ progBody
  IO.FS.writeFile progPath prog
  IO.println s!"wrote runnable program to {progPath}"
  -- Extra IO programs: stdin echo + an error-throwing program, each a
  -- self-contained runnable module diff-tested against `lean --run`.
  let emitProg (root : Name) (path : String) : IO Unit := do
    match LeanTs.renderProgramChecked env root with
    | .ok body =>
      IO.FS.writeFile path
        (prelude ++ "\n// ================ GENERATED PROGRAM ================\n\n" ++ body)
      IO.println s!"wrote runnable program to {path}"
    | .error e => throw (IO.userError s!"lean-typescript: {e}")
  emitProg `LeanTs.DemoIO.stdinEcho "out-stdin.mjs"
  emitProg `LeanTs.DemoIO.errMain "out-err.mjs"
  emitProg `LeanTs.DemoIO.panicMain "out-panic.mjs"
  emitProg `LeanTs.DemoInit.main "out-init.mjs"
  emitProg `LeanTs.DemoStress.stressMain "out-stress.mjs"
  emitProg `LeanTs.DemoStress2.stress2Main "out-stress2.mjs"
  emitProg `LeanTs.DemoStress3.stress3Main "out-stress3.mjs"
  emitProg `LeanTs.DemoStress4.stress4Main "out-stress4.mjs"
  emitProg `LeanTs.DemoVerify.verifyMain "out-verify.mjs"
