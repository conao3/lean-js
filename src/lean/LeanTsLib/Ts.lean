namespace Ts

inductive Exc where
  | error (name : String) (message : String)
  | undefinedValue
  | zeroDivision
  deriving Repr, DecidableEq

abbrev M := Except Exc

def index (xs : List α) (i : Int) : Option α :=
  if i < 0 then none else xs[i.toNat]?

def get (xs : List α) (i : Int) : M α :=
  match index xs i with
  | some v => pure v
  | none => throw .undefinedValue

def unwrap (o : Option α) : M α :=
  match o with
  | some v => pure v
  | none => throw .undefinedValue

def floorDiv (a b : Int) : M Int := if b = 0 then throw .zeroDivision else pure (Int.fdiv a b)

def truncDiv (a b : Int) : M Int := if b = 0 then throw .zeroDivision else pure (Int.tdiv a b)

def rem (a b : Int) : M Int := if b = 0 then throw .zeroDivision else pure (Int.tmod a b)

def range (a b : Int) : List Int := (List.range (b - a).toNat).map fun (k : Nat) => a + (k : Int)

def abs (a : Int) : Int := if a < 0 then -a else a

def length (xs : List α) : Int := xs.length

def strLength (s : String) : Int :=
  (s.toList.map fun c => if c.toNat ≥ 0x10000 then (2 : Int) else 1).sum

def startsWith (s t : String) : Bool := t.toList.isPrefixOf s.toList

def endsWith (s t : String) : Bool := t.toList.isSuffixOf s.toList

def includes (s t : String) : Bool :=
  (List.range (s.length + 1)).any fun i => t.toList.isPrefixOf (s.toList.drop i)

class Str (α : Type) where
  str : α → String

instance : Str Int := ⟨fun n => toString n⟩
instance : Str String := ⟨id⟩
instance : Str Bool := ⟨fun b => if b then "true" else "false"⟩

def str [Str α] (a : α) : String := Str.str a

@[simp] theorem str_string (s : String) : str s = s := rfl

@[simp] theorem length_eq (xs : List α) : length xs = (xs.length : Int) := rfl

@[simp] theorem range_mem (a b i : Int) : i ∈ range a b ↔ a ≤ i ∧ i < b := by
  simp only [range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨(i - a).toNat, by omega, by omega⟩

theorem range_succ (a b : Int) (h : a ≤ b) : range a (b + 1) = range a b ++ [b] := by
  simp only [range]
  have h1 : (b + 1 - a).toNat = (b - a).toNat + 1 := by omega
  rw [h1, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
  omega

@[simp] theorem index_nil (i : Int) : index ([] : List α) i = none := by
  unfold index; split <;> simp

theorem abs_nonneg (a : Int) : 0 ≤ abs a := by
  unfold abs; split <;> omega

end Ts
