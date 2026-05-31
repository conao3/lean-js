import Lean.Compiler.IR

def double (n : Nat) : Nat := n + n

structure Point where
  x : Nat
  y : Nat

def mkShifted (p : Point) : Point := { x := p.x + 1, y := p.y + p.x }

def main : IO Unit := do
  -- double
  IO.println s!"double 0 = {double 0}"
  IO.println s!"double 7 = {double 7}"
  IO.println s!"double 1000000 = {double 1000000}"
  -- mkShifted
  let a := mkShifted { x := 3, y := 4 }
  IO.println s!"mkShifted(3,4) = ({a.x},{a.y})"
  let b := mkShifted { x := 0, y := 0 }
  IO.println s!"mkShifted(0,0) = ({b.x},{b.y})"
  let c := mkShifted { x := 10, y := 100 }
  IO.println s!"mkShifted(10,100) = ({c.x},{c.y})"
