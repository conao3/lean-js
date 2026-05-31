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

structure Mixed where
  label : Nat
  b : UInt8
  c : UInt8
  d : UInt16

def mkMixed (label : Nat) (b c : UInt8) (d : UInt16) : Mixed :=
  { label := label, b := b, c := c, d := d }

def mixedSum (m : Mixed) : Nat :=
  m.label + m.b.toNat + m.c.toNat + m.d.toNat

def u32wrap (a b : UInt32) : UInt32 := a + b
def u8wrap (a b : UInt8) : UInt8 := a - b
def intEdiv (a b : Int) : Int := a / b
def intEmod (a b : Int) : Int := a % b
def intNeg (a : Int) : Int := -a
def floatCalc (a b : Float) : Float := (a + b) * 2.0 / b
def strLen (s : String) : Nat := s.length
def strBytes (s : String) : Nat := s.utf8ByteSize
def strGet0 (s : String) : Char := String.Pos.Raw.get s ⟨0⟩
def strGet1 (s : String) : Char := String.Pos.Raw.get s (String.Pos.Raw.next s ⟨0⟩)
def strExtract (s : String) (lo hi : Nat) : String :=
  String.Pos.Raw.extract s ⟨lo⟩ ⟨hi⟩
def arrSum (xs : Array Nat) : Nat := xs.foldl (· + ·) 0
def arrMapSum (xs : Array Nat) : Nat := (xs.map (· * 2)).foldl (· + ·) 0
def arrRange (n : Nat) : Array Nat := (Array.range n)
def arrGetD (xs : Array Nat) (i : Nat) : Nat := xs.getD i 0
def arrAppend (xs ys : Array Nat) : Array Nat := xs ++ ys
def listSum (xs : List Nat) : Nat := xs.foldl (· + ·) 0
def listLen (xs : List Nat) : Nat := xs.length
def listRev (xs : List Nat) : List Nat := xs.reverse
def listMapSum (xs : List Nat) : Nat := (xs.map (· + 1)).foldl (· + ·) 0

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
  let m := mkMixed 100 7 9 1000
  IO.println s!"mixed b = {m.b}"
  IO.println s!"mixed c = {m.c}"
  IO.println s!"mixed d = {m.d}"
  IO.println s!"mixedSum = {mixedSum m}"
  -- packed scalars stay distinct (no fields[] collision)
  let m2 := mkMixed 0 255 1 65535
  IO.println s!"mixed2 b = {m2.b}"
  IO.println s!"mixed2 c = {m2.c}"
  IO.println s!"mixed2 d = {m2.d}"
  IO.println s!"mixedSum2 = {mixedSum m2}"
  IO.println s!"u32wrap = {u32wrap 4000000000 1000000000}"
  IO.println s!"u8wrap = {u8wrap 3 10}"
  IO.println s!"intEdiv = {intEdiv (-12) 7}"
  IO.println s!"intEmod = {intEmod (-12) 7}"
  IO.println s!"intEdiv2 = {intEdiv 12 (-7)}"
  IO.println s!"intEmod2 = {intEmod 12 (-7)}"
  IO.println s!"intNeg = {intNeg 42}"
  IO.println s!"floatCalc = {floatCalc 3.0 4.0}"
  let jp := "あいう"
  IO.println s!"strLen = {strLen jp}"
  IO.println s!"strBytes = {strBytes jp}"
  IO.println s!"strGet0 = {strGet0 jp}"
  IO.println s!"strGet1 = {strGet1 jp}"
  IO.println s!"strExtract03 = {strExtract jp 0 3}"
  IO.println s!"strExtract39 = {strExtract jp 3 9}"
  let arr := #[1, 2, 3, 4, 5]
  IO.println s!"arrSum = {arrSum arr}"
  IO.println s!"arrMapSum = {arrMapSum arr}"
  IO.println s!"arrRange = {arrRange 5}"
  IO.println s!"arrGetD2 = {arrGetD arr 2}"
  IO.println s!"arrGetD9 = {arrGetD arr 9}"
  IO.println s!"arrAppend = {arrAppend arr #[6, 7]}"
  let lst := [10, 20, 30]
  IO.println s!"listSum = {listSum lst}"
  IO.println s!"listLen = {listLen lst}"
  IO.println s!"listRev = {listRev lst}"
  IO.println s!"listMapSum = {listMapSum lst}"
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
