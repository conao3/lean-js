import { lean } from "lean-ts"
import * as wc from "./_lean/count.ts"

export const block = lean(
  "wc",
  String.raw`
structure Counts where
  lines : Nat
  words : Nat
  chars : Nat

def words (s : String) : List String :=
  (s.splitOn " ").flatMap (·.splitOn "\n") |>.filter (· ≠ "")

def count (s : String) : Counts :=
  { lines := (s.toList.filter (· = '\n')).length, words := (words s).length, chars := s.length }

def insertCount (w : String) : List (String × Nat) → List (String × Nat)
  | [] => [(w, 1)]
  | (v, n) :: rest => if v = w then (v, n + 1) :: rest else (v, n) :: insertCount w rest

def frequencies (s : String) : List (String × Nat) :=
  (words s).foldl (fun acc w => insertCount w acc) []

def top (s : String) (k : Nat) : List (String × Nat) :=
  ((frequencies s).toArray.qsort (fun a b => decide (a.2 > b.2) || (a.2 == b.2 && decide (a.1 < b.1)))).toList.take k

theorem insertCount_length (w : String) (xs : List (String × Nat)) :
    (insertCount w xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [insertCount]
  | cons p rest ih =>
    obtain ⟨v, n⟩ := p
    simp only [insertCount]
    split <;> simp <;> omega

theorem count_lines (s : String) : (count s).lines = (s.toList.filter (· = '\n')).length := rfl
`,
)

export { wc }
