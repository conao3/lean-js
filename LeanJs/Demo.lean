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

def floatStr (x : Float) : String := toString x
def float32Str (x : Float32) : String := toString x

/-- A ctor packing SIGNED fixed-width scalars (Int8/Int16/Int32/Int64) plus a
    Float and a Float32 in region S, alongside one object field (`label : Nat`).
    At Lean 4.29.1 the signed Int* types share the storage IRType of their UInt*
    counterparts (no signed IRType exists), so the layout pass packs them via the
    uint8/16/32/64/float/float32 sproj/sset paths; the two's-complement bit
    pattern is preserved, so reading the same bytes back yields the signed value
    once reinterpreted at the arithmetic boundary. -/
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

/-- Read each packed signed/float field back (sproj), exercising the signed
    round-trip through the unsigned/float DataView accessors. -/
def spackA (s : SPack) : Int8  := s.a
def spackB (s : SPack) : Int16 := s.b
def spackC (s : SPack) : Int32 := s.c
def spackE (s : SPack) : Int64 := s.e
def spackF (s : SPack) : Float := s.f
def spackG (s : SPack) : Float32 := s.g
/-- Sum the integer fields back at Int precision: proves the bytes decode to the
    right signed values (negatives included). -/
def spackSum (s : SPack) : Int :=
  s.a.toInt + s.b.toInt + s.c.toInt + s.e.toInt

/-! Acyclic cross-function tail chain (a DAG, not a cycle): each step
    tail-calls a DISTINCT next function, so every node is its own size-1 SCC with
    no self-edge. The old SCC trampoline (which only fired for SCC ≥ 2) would
    emit a stacking JS call per link; the uniform thunk-target mechanism wraps
    each chain link as a `__tc` core so the chain runs in constant JS stack. -/
def cs0 (n : Nat) : Nat := n
def cs1 (n : Nat) : Nat := cs0 (n + 1)
def cs2 (n : Nat) : Nat := cs1 (n + 1)
def cs3 (n : Nat) : Nat := cs2 (n + 1)
def chainHead (n : Nat) : Nat := cs3 n

/-- A self-looping driver (already TCO'd) whose per-step body performs a
    cross-function tail edge `viaB → viaA`. At large N the cross edge must not
    stack: `pingN` loops, and each `viaB acc` evaluates through the trampoline. -/
def viaA (n : Nat) : Nat := n + 1
def viaB (n : Nat) : Nat := viaA n
def pingN (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n+1 => pingN n (viaB acc)

-- Float/Float32 libm transcendentals. Compared through `Float.toString` (C `%f`,
-- 6 fixed decimals), which absorbs the <=1-ULP JS-Math-vs-libm noise; sqrt and
-- the arithmetic/comparison ops are IEEE-correctly-rounded (bit-exact). frExp /
-- ofBits / toBits are EXACT bit reinterpretations and compared as integers.
def ftan (x : Float) : Float := x.tan
def fasin (x : Float) : Float := x.asin
def facos (x : Float) : Float := x.acos
def fatan (x : Float) : Float := x.atan
def fatan2 (y x : Float) : Float := Float.atan2 y x
def fsinh (x : Float) : Float := x.sinh
def fcosh (x : Float) : Float := x.cosh
def ftanh (x : Float) : Float := x.tanh
def fexp2 (x : Float) : Float := x.exp2
def flog2 (x : Float) : Float := x.log2
def flog10 (x : Float) : Float := x.log10
def fcbrt (x : Float) : Float := x.cbrt
def ftoBits (x : Float) : UInt64 := x.toBits
def fofBits (b : UInt64) : Float := Float.ofBits b
def ffrExpM (x : Float) : Float := x.frExp.1
def ffrExpE (x : Float) : Int := x.frExp.2
def f32tan (x : Float32) : Float32 := x.tan
def f32exp (x : Float32) : Float32 := x.exp
def f32log (x : Float32) : Float32 := x.log
def f32cbrt (x : Float32) : Float32 := x.cbrt
def f32toBits (x : Float32) : UInt32 := x.toBits

-- USize / platform-word width. On the host (64-bit) profile these match the
-- native oracle; under a WORD_BITS=32 profile, getNumBits reports 32 and USize
-- arithmetic wraps at 2^32 (asserted node-side in test-usize32.mjs).
def nbits : Nat := System.Platform.numBits
def uszOfU64 (x : UInt64) : USize := x.toUSize
def uszAdd (a b : USize) : USize := a + b
def uszCompl (a : USize) : USize := ~~~a
def uszToNat (a : USize) : Nat := a.toNat

end LeanJs.Demo
