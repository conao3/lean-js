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

/-- UTF-8 byte semantics over a multibyte string. `length` counts code points,
    `utf8ByteSize` counts bytes; `get`/`next` index byte offsets. -/
def strLen (s : String) : Nat := s.length
def strBytes (s : String) : Nat := s.utf8ByteSize
def strGet0 (s : String) : Char := String.Pos.Raw.get s ⟨0⟩
/-- Char at the byte offset reached by advancing once from 0 (skips a multibyte
    char's bytes), proving positions are byte offsets not code-point indices. -/
def strGet1 (s : String) : Char := String.Pos.Raw.get s (String.Pos.Raw.next s ⟨0⟩)
/-- Extract bytes [lo, hi) by raw byte offset. -/
def strExtract (s : String) (lo hi : Nat) : String :=
  String.Pos.Raw.extract s ⟨lo⟩ ⟨hi⟩

/-- Array building and querying. -/
def arrSum (xs : Array Nat) : Nat := xs.foldl (· + ·) 0
def arrMapSum (xs : Array Nat) : Nat := (xs.map (· * 2)).foldl (· + ·) 0
def arrRange (n : Nat) : Array Nat := (Array.range n)
def arrGetD (xs : Array Nat) (i : Nat) : Nat := xs.getD i 0
def arrAppend (xs ys : Array Nat) : Array Nat := xs ++ ys

/-- List operations (List is a ctor inductive). -/
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

end LeanJs.Demo
