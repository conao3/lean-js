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

/-- A ctor mixing one object pointer field (`label : Nat`) with three packed
    sub-word scalars sharing one machine word (`b c : UInt8`, `d : UInt16`).
    Region layout: size=1 (object), ssize=4 bytes. A single `fields[]` keyed by
    the word-slot index would map all three scalars to the same slot and
    collide; the byte-addressed region S keeps them distinct. -/
structure Mixed where
  label : Nat
  b : UInt8
  c : UInt8
  d : UInt16

def mkMixed (label : Nat) (b c : UInt8) (d : UInt16) : Mixed :=
  { label := label, b := b, c := c, d := d }

def mixedSum (m : Mixed) : Nat :=
  m.label + m.b.toNat + m.c.toNat + m.d.toNat

/-- UInt32 wrap-around: 4000000000 + 1000000000 overflows 2^32. -/
def u32wrap (a b : UInt32) : UInt32 := a + b

/-- UInt8 wrap-around on subtraction (modular). -/
def u8wrap (a b : UInt8) : UInt8 := a - b

/-- Int Euclidean div/mod with a negative dividend. -/
def intEdiv (a b : Int) : Int := a / b
def intEmod (a b : Int) : Int := a % b
def intNeg (a : Int) : Int := -a

/-- A Float computation exercising add/mul/div. -/
def floatCalc (a b : Float) : Float := (a + b) * 2.0 / b

end LeanJs.Demo
