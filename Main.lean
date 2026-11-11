import LeanTs.EmitTs
import LeanTsTest.Vectors
import LeanTsTest.HigherOrder
import LeanTsTest.Io
import LeanTsTest.Init
import LeanTsTest.Stress
import LeanTsTest.Stress2
import LeanTsTest.Stress3
import LeanTsTest.Stress4
import LeanTsTest.Verify
import LeanTsTest.Fuzz

open Lean Lean.IR

/-! # lean-typescript CLI

Thin driver around `LeanTs.EmitTs`. Target functions live in imported library
modules so their IR is persisted in the `.olean` and visible to
`Lean.IR.findEnvDecl` when we re-import; we transitively collect dependencies
and emit a self-contained TypeScript module (prelude + generated functions). -/

/-- Root names to extract. TodoList functions exercise List, String, ctor/proj,
    Bool, and transitive helper-decl collection together. -/
def rootNames : Array Name := #[
  `LeanTsTest.Vectors.double, `LeanTsTest.Vectors.mkShifted, `LeanTsTest.Vectors.sumTo, `LeanTsTest.Vectors.fact,
  `LeanTsTest.Vectors.mkMixed, `LeanTsTest.Vectors.mixedSum,
  `LeanTsTest.Vectors.u32wrap, `LeanTsTest.Vectors.u8wrap,
  `LeanTsTest.Vectors.intEdiv, `LeanTsTest.Vectors.intEmod, `LeanTsTest.Vectors.intNeg,
  `LeanTsTest.Vectors.floatCalc,
  `LeanTsTest.Vectors.strLen, `LeanTsTest.Vectors.strBytes, `LeanTsTest.Vectors.strGet0,
  `LeanTsTest.Vectors.strGet1, `LeanTsTest.Vectors.strExtract,
  `LeanTsTest.Vectors.arrSum, `LeanTsTest.Vectors.arrMapSum, `LeanTsTest.Vectors.arrRange,
  `LeanTsTest.Vectors.arrGetD, `LeanTsTest.Vectors.arrAppend,
  `LeanTsTest.Vectors.listSum, `LeanTsTest.Vectors.listLen, `LeanTsTest.Vectors.listRev,
  `LeanTsTest.Vectors.listMapSum,
  `LeanTsTest.Vectors.parityEven, `LeanTsTest.Vectors.parityOdd, `LeanTsTest.Vectors.cycle3,
  `LeanTsTest.Vectors.i8wrap, `LeanTsTest.Vectors.i8neg, `LeanTsTest.Vectors.i8div, `LeanTsTest.Vectors.i8mod,
  `LeanTsTest.Vectors.i8shr, `LeanTsTest.Vectors.i16wrap, `LeanTsTest.Vectors.i32wrap, `LeanTsTest.Vectors.i64mul,
  `LeanTsTest.Vectors.i8toInt, `LeanTsTest.Vectors.i32toInt,
  `LeanTsTest.Vectors.floatStr, `LeanTsTest.Vectors.float32Str,
  `LeanTsTest.Vectors.mkSPack, `LeanTsTest.Vectors.spackA, `LeanTsTest.Vectors.spackB, `LeanTsTest.Vectors.spackC,
  `LeanTsTest.Vectors.spackE, `LeanTsTest.Vectors.spackF, `LeanTsTest.Vectors.spackG, `LeanTsTest.Vectors.spackSum,
  `LeanTsTest.Vectors.chainHead, `LeanTsTest.Vectors.pingN,
  `LeanTsTest.Vectors.ftan, `LeanTsTest.Vectors.fasin, `LeanTsTest.Vectors.facos, `LeanTsTest.Vectors.fatan,
  `LeanTsTest.Vectors.fatan2, `LeanTsTest.Vectors.fsinh, `LeanTsTest.Vectors.fcosh, `LeanTsTest.Vectors.ftanh,
  `LeanTsTest.Vectors.fexp2, `LeanTsTest.Vectors.flog2, `LeanTsTest.Vectors.flog10, `LeanTsTest.Vectors.fcbrt,
  `LeanTsTest.Vectors.ftoBits, `LeanTsTest.Vectors.fofBits, `LeanTsTest.Vectors.ffrExpM, `LeanTsTest.Vectors.ffrExpE,
  `LeanTsTest.Vectors.f32tan, `LeanTsTest.Vectors.f32exp, `LeanTsTest.Vectors.f32log, `LeanTsTest.Vectors.f32cbrt,
  `LeanTsTest.Vectors.f32toBits,
  `LeanTsTest.Vectors.nbits, `LeanTsTest.Vectors.uszOfU64, `LeanTsTest.Vectors.uszAdd,
  `LeanTsTest.Vectors.uszCompl, `LeanTsTest.Vectors.uszToNat,
  `LeanTsTest.HigherOrder.hofApply,
  `LeanTsTest.HigherOrder.listMapLam, `LeanTsTest.HigherOrder.listFilterLam, `LeanTsTest.HigherOrder.listFoldlLam,
  `LeanTsTest.HigherOrder.arrMapLam,
  `LeanTsTest.HigherOrder.applyAdders, `LeanTsTest.HigherOrder.currySplit,
  `LeanTsTest.HigherOrder.optSeq, `LeanTsTest.HigherOrder.exSeq, `LeanTsTest.HigherOrder.fmapList,
  `LeanTsTest.HigherOrder.safeDivStr, `LeanTsTest.HigherOrder.hmDemo,
  `LeanTsTest.HigherOrder.cpsCount, `LeanTsTest.HigherOrder.cpsSum,
  `LeanTsTest.Vectors.TodoList.add,
  `LeanTsTest.Vectors.TodoList.toggle,
  `LeanTsTest.Vectors.TodoList.remove,
  `LeanTsTest.Vectors.TodoList.step,
  `LeanTsTest.Fuzz.fNat, `LeanTsTest.Fuzz.fInt, `LeanTsTest.Fuzz.fU32, `LeanTsTest.Fuzz.fU8,
  `LeanTsTest.Fuzz.fStr, `LeanTsTest.Fuzz.fHash, `LeanTsTest.Fuzz.fListNat, `LeanTsTest.Fuzz.fArrNat
]

def main (args : List String) : IO Unit := do
  let outPath := args.headD "out.ts"
  let preludePath := args.getD 1 "prelude.ts"
  let progPath := args.getD 2 "out-io.mjs"
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `LeanTsTest.Vectors }, { module := `LeanTsTest.HigherOrder },
      { module := `LeanTsTest.Io }, { module := `LeanTsTest.Init },
      { module := `LeanTsTest.Stress }, { module := `LeanTsTest.Stress2 },
      { module := `LeanTsTest.Stress3 }, { module := `LeanTsTest.Stress4 },
      { module := `LeanTsTest.Verify },
      { module := `LeanTsTest.Fuzz },
      { module := `LeanTsTest.Vectors }] {}
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
  let progBody ← match LeanTs.renderProgramChecked env `LeanTsTest.Io.main with
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
  emitProg `LeanTsTest.Io.stdinEcho "out-stdin.mjs"
  emitProg `LeanTsTest.Io.errMain "out-err.mjs"
  emitProg `LeanTsTest.Io.panicMain "out-panic.mjs"
  emitProg `LeanTsTest.Init.main "out-init.mjs"
  emitProg `LeanTsTest.Stress.stressMain "out-stress.mjs"
  emitProg `LeanTsTest.Stress2.stress2Main "out-stress2.mjs"
  emitProg `LeanTsTest.Stress3.stress3Main "out-stress3.mjs"
  emitProg `LeanTsTest.Stress4.stress4Main "out-stress4.mjs"
  emitProg `LeanTsTest.Verify.verifyMain "out-verify.mjs"
