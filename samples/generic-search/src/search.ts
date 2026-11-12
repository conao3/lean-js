import { lean } from "lean-ts"
import * as search from "./_lean/search.ts"

export const block = lean(
  "search",
  String.raw`
def member [BEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => x == y || member x ys

theorem member_head [BEq α] [LawfulBEq α] (x : α) (xs : List α) : member x (x :: xs) = true := by
  simp [member]

theorem member_nil [BEq α] (x : α) : member x [] = false := rfl

theorem member_iff [BEq α] [LawfulBEq α] (x : α) (xs : List α) : member x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [member]
  | cons y ys ih =>
    simp only [member, Bool.or_eq_true, beq_iff_eq, ih, List.mem_cons]

def maxOf [Max α] : List α → Option α
  | [] => none
  | x :: xs => some (xs.foldl max x)

theorem maxOf_isSome [Max α] (x : α) (xs : List α) : (maxOf (x :: xs)).isSome := rfl

def memberInt (x : Int) (xs : List Int) : Bool := member x xs

def memberString (x : String) (xs : List String) : Bool := member x xs

def maxNat (xs : List Nat) : Option Nat := maxOf xs

def maxInt (xs : Array Int) : Option Int := maxOf xs.toList
`,
)

export { search }
