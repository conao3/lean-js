/-! Demo target functions extracted by the lean-js CLI. Kept in a library
module (not the executable root) so their IR is persisted in the `.olean` and
visible to `Lean.IR.findEnvDecl` when the CLI re-imports the modules. -/

namespace LeanJs.Demo

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

end LeanJs.Demo
