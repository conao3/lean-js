/-! Functions called through the generated public API by `test/public.test.ts`. -/

namespace LeanTsTest.Public

def double (n : Nat) : Nat := n + n

def negate (i : Int) : Int := -i

def isEven : Nat → Bool
  | 0 => true
  | n + 1 => !isEven n

def flip (b : Bool) : Bool := !b

def mix (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) (e : USize) : UInt64 :=
  a.toUInt64 + b.toUInt64 + c.toUInt64 + d + e.toUInt64

def wrapU8 (a : UInt8) : UInt8 := a + 200

def signed (a : Int8) (b : Int16) (c : Int32) (d : Int64) (e : ISize) : Int64 :=
  a.toInt64 + b.toInt64 + c.toInt64 + d + e.toInt64

def negI8 (a : Int8) : Int8 := -a

def negI32 (a : Int32) : Int32 := -a

def halve (x : Float) : Float := x / 2

def halve32 (x : Float32) : Float32 := x / 2

def nextChar (c : Char) : Char := Char.ofNat (c.toNat + 1)

def greet (name : String) : String := s!"こんにちは, {name}! ({name.length})"

def unit (_ : Unit) : Unit := ()

def answer : Nat := 42

def big : Nat := 2 ^ 100

def sumList (xs : List Nat) : Nat := xs.foldl (· + ·) 0

def range (n : Nat) : List Nat := List.range n

def squares (xs : Array Int) : Array Int := xs.map (fun x => x * x)

def firstEven? (xs : List Nat) : Option Nat := xs.find? (· % 2 == 0)

def orDefault (o : Option String) : String := o.getD "default"

def swap (p : Nat × String) : String × Nat := (p.2, p.1)

def indexed (xs : List String) : List (String × Nat) := xs.zipIdx

def rotate (t : Nat × Bool × String) : String × Nat × Bool := (t.2.2, t.1, t.2.1)

def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "division by zero" else .ok (a / b)

def fromExcept (e : Except String Nat) : Nat :=
  match e with
  | .ok n => n
  | .error s => s.length

def nested (xs : List (Option (Nat × String))) : Array (List Nat) :=
  xs.toArray.map fun
    | some (n, s) => [n, s.length]
    | none => []

def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

def ioEcho (s : String) : IO String := pure (s ++ "!")

def ioUnit (_ : Unit) : IO Unit := pure ()

def failing (_ : Unit) : IO Nat := throw (IO.userError "nope")

def openMissing (path : String) : IO Unit := do
  let _ ← IO.FS.Handle.mk path .read

namespace Calc

def add (a b : Nat) : Nat := a + b

def mul (a b : Int) : Int := a * b

end Calc

def applyTwice (f : α → α) (x : α) : α := f (f x)

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def optOpt (o : Option (Option Nat)) : Nat := (o.getD none).getD 0

structure Point where
  x : Nat
  y : Nat

def Point.sum (p : Point) : Nat := p.x + p.y

def Point.new (n : Nat) : Point := ⟨n, n⟩

def below (n : Nat) (_h : n < 10) : Nat := n

structure Range where
  lo : Nat
  hi : Nat
  ok : lo ≤ hi

def width (r : Range) : Nat := r.hi - r.lo

def mkRange (a b : Nat) : Range :=
  if h : a ≤ b then ⟨a, b, h⟩ else ⟨b, a, by omega⟩

inductive Discount where
  | none
  | percent (p : Nat) (h : p ≤ 100)
  | fixed (amount : Nat)
  | coupon : String → Nat → Discount

def applyDiscount (d : Discount) (price : Nat) : Nat :=
  match d with
  | .none => price
  | .percent p _ => price - price * p / 100
  | .fixed a => price - a
  | .coupon _ a => price - a

def halfOff : Discount := .percent 50 (by decide)

inductive Color where
  | red
  | green
  | blue

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

structure Labeled extends Point where
  label : String
  note? : Option String := none
  tag : Option Nat

def describe (l : Labeled) : String :=
  s!"{l.label}@{l.x},{l.y}:{l.note?.getD "-"}:{l.tag.getD 0}"

def relabel (l : Labeled) (s : String) : Labeled := { l with label := s, note? := some l.label }

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def Tree.sum : Tree → Nat
  | .leaf => 0
  | .node l v r => l.sum + v + r.sum

def Tree.build : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node .leaf (n + 1) (Tree.build n)

def Small := { n : Nat // n < 10 }

def smallDouble (s : Small) : Nat := s.val * 2

def toSmall (n : Nat) : Option Small := if h : n < 10 then some ⟨n, h⟩ else none

structure Flags where
  a : Bool
  b : UInt8
  c : UInt16
  d : UInt32
  e : UInt64
  f : Float
  g : USize
  h : Int8
  k : Color
  ch : Char

def bump (f : Flags) : Flags :=
  { f with a := !f.a, b := f.b + 1, c := f.c + 1, d := f.d + 1, e := f.e + 1, f := f.f * 2,
           g := f.g + 1, h := f.h - 1, k := f.k.next, ch := Char.ofNat (f.ch.toNat + 1) }

structure Pos where
  n : Nat
  pos : 0 < n

def Pos.pred (p : Pos) : Nat := p.n - 1

def finSucc (i : Fin 5) : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

structure Names where
  xs : List String
  short : xs.length ≤ 3

def Names.count (n : Names) : Nat := n.xs.length

structure Pair (α β : Type) where
  fst : α
  snd : β

def swapPair (p : Pair Nat Bool) : Pair Bool Nat := ⟨p.snd, p.fst⟩

def roundTrip (d : Discount) (l : Labeled) (t : Tree) (f : Flags) : Discount × Labeled × Tree × Flags :=
  (d, l, t, f)

end LeanTsTest.Public
