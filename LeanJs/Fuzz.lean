/-! Property-based fuzz functions: deterministic pure renderings of the
divergence-prone numeric / string / container paths. Each returns a canonical
String so the native oracle and node only have to agree on text. -/

namespace LeanJs.Fuzz

def fNat (n : Nat) : String :=
  s!"{n + n}|{n * n}|{n % 1000}|{Nat.log2 n}|{n / 7}|{n <<< 1}"

def fInt (a b : Int) : String :=
  s!"{a / b}|{a % b}|{-a}|{a * b}|{a + b}|{a.tdiv b}|{a.tmod b}"

def fU32 (a b : UInt32) : String :=
  s!"{a + b}|{a - b}|{a * b}|{a &&& b}|{a ||| b}|{a <<< 1}"

def fU8 (a b : UInt8) : String :=
  s!"{a + b}|{a - b}|{a * b}|{a / (if b == 0 then 1 else b)}"

def fStr (s : String) : String :=
  s!"{s.length}|{s.utf8ByteSize}|{s.toList.length}|{s.toUTF8.size}|{s.toUpper.length}"

def fListNat (xs : List Nat) : String :=
  s!"{xs.foldl (·+·) 0}|{xs.length}|{(xs.reverse).foldl (fun a x => a*31+x) 0}|{(xs.filter (· % 2 == 0)).length}"

def fArrNat (xs : Array Nat) : String :=
  s!"{xs.foldl (·+·) 0}|{xs.size}|{(xs.map (·*2)).foldl (·+·) 0}|{xs.toList.length}"

/-! Parse helpers shared by the oracle exe and (mirrored in) the node runner. -/

def parseInt (s : String) : Int :=
  if s.startsWith "-" then -(Int.ofNat (s.drop 1).toNat!) else Int.ofNat s.toNat!

def unescape (s : String) : String :=
  (s.replace "\\t" "\t").replace "\\n" "\n" |>.replace "\\\\" "\\"

def parseNats (parts : List String) : List Nat :=
  (parts.filter (· ≠ "")).map String.toNat!

end LeanJs.Fuzz
