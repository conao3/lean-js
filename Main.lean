import LeanJs.EmitJS
import LeanJs.Demo
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
  `LeanTodo.TodoList.add,
  `LeanTodo.TodoList.toggle,
  `LeanTodo.TodoList.remove,
  `LeanTodo.TodoList.step
]

def main (args : List String) : IO Unit := do
  let outPath := args.headD "out.ts"
  let preludePath := args.getD 1 "prelude.ts"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanJs.Demo }, { module := `LeanTodo.Basic }] {}
    (loadExts := true)
  let prelude ← IO.FS.readFile preludePath
  let decls := LeanJs.collectTransitive env rootNames
  let body := LeanJs.render decls
  let ts := prelude ++ "\n// ================ GENERATED ================\n\n" ++ body
  IO.FS.writeFile outPath ts
  IO.println s!"wrote {decls.size} decls to {outPath}"
