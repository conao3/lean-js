import Std.Data.HashMap

/-! Coverage-breadth probes (round 7): exercise stdlib surface the existing
suite does not reach. Each `*Prog : IO Unit` prints deterministic output. -/

namespace LeanJs.DemoStress2

/-! ByteArray + UTF-8 round-trips. -/

def baProg : IO Unit := do
  let s := "héllo, 世界!"
  let bytes := s.toUTF8
  IO.println s!"utf8 size = {bytes.size}"
  let back := String.fromUTF8! bytes
  IO.println s!"roundtrip = {back}"
  let ba := (((ByteArray.empty.push 104).push 105).push 33)
  IO.println s!"ba size = {ba.size} b0 = {ba.get! 0} b2 = {ba.get! 2}"
  let ba2 := ba ++ (ByteArray.emptyWithCapacity 2 |>.push 63)
  IO.println s!"append size = {ba2.size} last = {ba2.get! 3}"
  IO.println s!"fromUTF8 = {String.fromUTF8! ba}"

/-! Generic derived ToString/Repr over Option / Except / tuples / Prod. -/

def gtsProg : IO Unit := do
  let o1 : Option Nat := some 42
  let o2 : Option Nat := none
  IO.println s!"opt = {o1} {o2}"
  let e1 : Except String Nat := .ok 7
  let e2 : Except String Nat := .error "boom"
  IO.println s!"exc = {e1} {e2}"
  let p : Nat × String := (3, "x")
  IO.println s!"prod = {p}"
  let l : List (Option Nat) := [some 1, none, some 3]
  IO.println s!"lopt = {l}"

/-! Array index with `a[i]!` (panic-on-oob get). -/

def aidxProg : IO Unit := do
  let a := #[10, 20, 30, 40]
  let mut s := 0
  for i in [0:a.size] do
    s := s + a[i]!
  IO.println s!"sum = {s}"
  IO.println s!"a[2]! = {a[2]!}"

def stress2Main : IO Unit := do
  baProg; gtsProg; aidxProg

end LeanJs.DemoStress2
