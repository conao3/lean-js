import { lean } from "lean-ts"
import * as m from "./_lean/code.ts"

export const block = lean(
  "m",
  String.raw`
def countLines (path : String) : IO Nat := do
  let h ← IO.FS.Handle.mk path .read
  let s ← h.readToEnd
  return (s.splitOn "\n").length - 1

def appendLine (path line : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line

def greet (name : String) : IO Unit := do
  let greeting := (← IO.getEnv "GREETING").getD "Hello"
  IO.println s!"{greeting}, {name}!"
`,
)

export { m }
