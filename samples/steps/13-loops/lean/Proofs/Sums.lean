import LeanTsModel.sums

namespace LeanTsModel.sums

theorem loop_square (n : Nat) :
    (Ts.range 0 (n : Int)).foldl (fun t i => t + (2 * i + 1)) 0 = (n : Int) * n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega]
    rw [Ts.range_succ 0 (n : Int) (by omega), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, Int.mul_add, Int.add_mul]
    omega

theorem sumOdd.proof.refines : sumOdd.obligation.refines := by
  intro n
  simp only [sumOdd, LeanTsEmbed.sums.spec.square]
  simp
  exact loop_square n

theorem sumOdd.proof.returnsNat : sumOdd.obligation.returnsNat := by
  intro n
  rw [sumOdd.proof.refines n]
  omega

theorem foldl_abs_nonneg (xs : List Int) (init : Int) (h : 0 ≤ init) :
    0 ≤ xs.foldl (fun acc x => acc + Ts.abs x) init := by
  induction xs generalizing init with
  | nil => simpa
  | cons x xs ih =>
    apply ih
    show 0 ≤ init + Ts.abs x
    have := Ts.abs_nonneg x
    omega

theorem sumAbs.proof.nonneg : sumAbs.obligation.nonneg := by
  intro xs
  simp only [LeanTsEmbed.sums.spec.nonneg, sumAbs]
  simp
  exact foldl_abs_nonneg xs 0 (Int.le_refl 0)

end LeanTsModel.sums
