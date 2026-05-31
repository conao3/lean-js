import LeanTodo.Basic

/-! IO demo program extracted by the lean-js CLI to prove end-to-end effectful
programs run under node and match Lean. Kept in a library module so its IR is
persisted and visible to `findEnvDecl` on re-import. -/

namespace LeanJs.DemoIO

open LeanTodo

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

def showTodo (t : Todo) : String :=
  let mark := if t.done then "x" else " "
  s!"{t.id}:{t.title}:{mark}"

def showList (l : TodoList) : String :=
  "[" ++ String.intercalate "," (l.items.map showTodo) ++ "]@" ++ toString l.nextId

def main : IO Unit := do
  IO.println "lean-js IO demo"
  IO.println s!"fib 10 = {fib 10}"
  IO.println s!"2 + 3 = {2 + 3}"
  let r ← IO.mkRef (0 : Nat)
  r.set 41
  r.modify (· + 1)
  let v ← r.get
  IO.println s!"ref = {v}"
  let l0 := TodoList.empty
  let l1 := l0.add "buy milk"
  let l2 := l1.add "walk dog"
  let l3 := l2.toggle 0
  IO.println s!"todo = {showList l3}"
  IO.eprintln "diagnostic to stderr"

end LeanJs.DemoIO
