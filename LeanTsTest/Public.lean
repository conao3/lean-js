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

def below (n : Nat) (_h : n < 10) : Nat := n

end LeanTsTest.Public
