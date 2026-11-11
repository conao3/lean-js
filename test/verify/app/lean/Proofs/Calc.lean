import LeanTsModel.calc

namespace LeanTsModel.calc

theorem clamp.proof.refines : clamp.obligation.refines := by
  intro x lo hi h
  simp only [LeanTsEmbed.calc.spec.ordered, decide_eq_true_eq] at h
  simp only [clamp, LeanTsEmbed.calc.spec.clampSpec]
  split <;> (try split) <;> simp_all <;> omega

theorem clamp.proof.inRange : clamp.obligation.inRange := by
  intro x lo hi h
  simp only [LeanTsEmbed.calc.spec.ordered, decide_eq_true_eq] at h
  simp only [clamp, LeanTsEmbed.calc.spec.inRange]
  split <;> (try split) <;> simp_all <;> omega

theorem firstOr.proof.refines : firstOr.obligation.refines := by
  intro xs d
  cases xs <;> simp [firstOr, Ts.index, LeanTsEmbed.calc.spec.firstOr]


theorem sumTo.proof.refines : sumTo.obligation.refines := by
  sorry
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
  simp only [LeanTsEmbed.calc.spec.nonneg, sumAbs]
  simp
  exact foldl_abs_nonneg xs 0 (Int.le_refl 0)


axiom twice_eq (x : Int) : twice x = LeanTsEmbed.calc.spec.double x

theorem twice.proof.refines : twice.obligation.refines := by
  intro x
  exact twice_eq x

theorem addOne.proof.refines : addOne.obligation.refines := by
  intro x
  simp [addOne, LeanTsEmbed.calc.spec.succ]

end LeanTsModel.calc
