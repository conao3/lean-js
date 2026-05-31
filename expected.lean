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

mutual
  def isEvenM : Nat → Bool
    | 0 => true
    | n+1 => isOddM n
  def isOddM : Nat → Bool
    | 0 => false
    | n+1 => isEvenM n
end
def parityEven (n : Nat) : Bool := isEvenM n
def parityOdd (n : Nat) : Bool := isOddM n
mutual
  def m3a : Nat → Nat
    | 0 => 0
    | n+1 => m3b n
  def m3b : Nat → Nat
    | 0 => 1
    | n+1 => m3c n
  def m3c : Nat → Nat
    | 0 => 2
    | n+1 => m3a n
end
def cycle3 (n : Nat) : Nat := m3a n
def i8wrap (a b : Int8) : Int8 := a + b
def i8neg (a : Int8) : Int8 := -a
def i8div (a b : Int8) : Int8 := a / b
def i8mod (a b : Int8) : Int8 := a % b
def i8shr (a : Int8) (n : Int8) : Int8 := a >>> n
def i16wrap (a b : Int16) : Int16 := a * b
def i32wrap (a b : Int32) : Int32 := a + b
def i64mul (a b : Int64) : Int64 := a * b
def i8toInt (a : Int8) : Int := a.toInt
def i32toInt (a : Int32) : Int := a.toInt
def floatStr (x : Float) : String := toString x
def float32Str (x : Float32) : String := toString x

structure SPack where
  label : Nat
  a : Int8
  b : Int16
  c : Int32
  e : Int64
  f : Float
  g : Float32
def mkSPack (label : Nat) (a : Int8) (b : Int16) (c : Int32) (e : Int64)
    (f : Float) (g : Float32) : SPack :=
  { label, a, b, c, e, f, g }
def spackA (s : SPack) : Int8  := s.a
def spackB (s : SPack) : Int16 := s.b
def spackC (s : SPack) : Int32 := s.c
def spackE (s : SPack) : Int64 := s.e
def spackF (s : SPack) : Float := s.f
def spackG (s : SPack) : Float32 := s.g
def spackSum (s : SPack) : Int :=
  s.a.toInt + s.b.toInt + s.c.toInt + s.e.toInt

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
  -- Mutual / cross-function TCO correctness (deep no-overflow is checked
  -- node-side in test-tco.mjs at N=1000000; the Lean interpreter caps recursion
  -- well below the naive-JS overflow point, so the diff-test uses a safe N).
  IO.println s!"parityEven 7 = {parityEven 7}"
  IO.println s!"parityOdd 7 = {parityOdd 7}"
  IO.println s!"parityEven 3000 = {parityEven 3000}"
  IO.println s!"parityOdd 3000 = {parityOdd 3000}"
  IO.println s!"cycle3 0 = {cycle3 0}"
  IO.println s!"cycle3 1 = {cycle3 1}"
  IO.println s!"cycle3 2 = {cycle3 2}"
  IO.println s!"cycle3 3000 = {cycle3 3000}"
  -- Signed fixed-width ints: two's-complement wrap, trunc div, dividend-sign mod.
  IO.println s!"i8wrap = {(i8wrap 127 1).toInt}"
  IO.println s!"i8neg = {(i8neg (-128)).toInt}"
  IO.println s!"i8div = {(i8div (-128) (-1)).toInt}"
  IO.println s!"i8div0 = {(i8div 5 0).toInt}"
  IO.println s!"i8mod = {(i8mod (-7) 2).toInt}"
  IO.println s!"i8mod2 = {(i8mod 7 (-2)).toInt}"
  IO.println s!"i8shr = {(i8shr (-8) 1).toInt}"
  IO.println s!"i16wrap = {(i16wrap 256 256).toInt}"
  IO.println s!"i32wrap = {(i32wrap 2147483647 1).toInt}"
  IO.println s!"i64mul = {(i64mul 4294967296 4294967296).toInt}"
  IO.println s!"i8toInt = {i8toInt (-5)}"
  IO.println s!"i32toInt = {i32toInt (-100)}"
  -- Float.toString edge cases: NaN, +/-inf, -0.0, finite rounding, 1e21 boundary.
  IO.println s!"fstr0 = {floatStr 0.0}"
  IO.println s!"fstrPi = {floatStr 3.14}"
  IO.println s!"fstrNeg0 = {floatStr (-0.0)}"
  IO.println s!"fstrInf = {floatStr (1.0/0.0)}"
  IO.println s!"fstrNInf = {floatStr (-1.0/0.0)}"
  IO.println s!"fstrNaN = {floatStr (0.0/0.0)}"
  IO.println s!"fstrBig = {floatStr 123456789.123456789}"
  IO.println s!"fstr1e20 = {floatStr 1e20}"
  IO.println s!"fstr1e21 = {floatStr 1e21}"
  IO.println s!"fstrNeg = {floatStr (-2.5)}"
  IO.println s!"f32str = {float32Str 16777217.0}"
  IO.println s!"f32strPi = {float32Str 3.14}"
  -- Packed signed-scalar + float ctor fields (region S)
  let sp := mkSPack 100 (-5) (-300) (-70000) (-5000000000) (-2.5) 1.5
  IO.println s!"spackA = {(spackA sp).toInt}"
  IO.println s!"spackB = {(spackB sp).toInt}"
  IO.println s!"spackC = {(spackC sp).toInt}"
  IO.println s!"spackE = {(spackE sp).toInt}"
  IO.println s!"spackF = {floatStr (spackF sp)}"
  IO.println s!"spackG = {float32Str (spackG sp)}"
  IO.println s!"spackSum = {spackSum sp}"
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
