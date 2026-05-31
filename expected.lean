import LeanTodo.Basic

open LeanTodo

def double (n : Nat) : Nat := n + n

structure Point where
  x : Nat
  y : Nat

def mkShifted (p : Point) : Point := { x := p.x + 1, y := p.y + p.x }

def sumTo (n : Nat) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i+1 => go i (acc + (i+1))
  go n 0

def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

def showTodo (t : Todo) : String :=
  let mark := if t.done then "x" else " "
  s!"{t.id}:{t.title}:{mark}"

def showList (l : TodoList) : String :=
  "[" ++ String.intercalate "," (l.items.map showTodo) ++ "]@" ++ toString l.nextId

def main : IO Unit := do
  IO.println s!"double 0 = {double 0}"
  IO.println s!"double 7 = {double 7}"
  IO.println s!"double 1000000 = {double 1000000}"
  let a := mkShifted { x := 3, y := 4 }
  IO.println s!"mkShifted(3,4) = ({a.x},{a.y})"
  let b := mkShifted { x := 0, y := 0 }
  IO.println s!"mkShifted(0,0) = ({b.x},{b.y})"
  let c := mkShifted { x := 10, y := 100 }
  IO.println s!"mkShifted(10,100) = ({c.x},{c.y})"
  IO.println s!"sumTo 0 = {sumTo 0}"
  IO.println s!"sumTo 5 = {sumTo 5}"
  IO.println s!"sumTo 100 = {sumTo 100}"
  IO.println s!"sumTo 100000 = {sumTo 100000}"
  IO.println s!"fact 0 = {fact 0}"
  IO.println s!"fact 5 = {fact 5}"
  IO.println s!"fact 10 = {fact 10}"
  -- TodoList sequence: add, add, add, toggle, remove
  let l0 := TodoList.empty
  let l1 := l0.add "buy milk"
  IO.println s!"add1 = {showList l1}"
  let l2 := l1.add "walk dog"
  IO.println s!"add2 = {showList l2}"
  let l3 := l2.add "write code"
  IO.println s!"add3 = {showList l3}"
  let l4 := l3.toggle 1
  IO.println s!"toggle1 = {showList l4}"
  let l5 := l4.toggle 0
  IO.println s!"toggle0 = {showList l5}"
  let l6 := l5.remove 1
  IO.println s!"remove1 = {showList l6}"
  let l7 := l6.step (.add "new task")
  IO.println s!"step-add = {showList l7}"
  let l8 := l7.step (.toggle 2)
  IO.println s!"step-toggle = {showList l8}"
  let l9 := l8.step (.remove 0)
  IO.println s!"step-remove = {showList l9}"
