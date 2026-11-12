import LeanTsModel.sum

namespace LeanTsModel.sum

theorem two_mul_loop (n : Nat) :
    2 * (Ts.range 0 ((n : Int) + 1)).foldl (· + ·) 0 = (n : Int) * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega]
    rw [Ts.range_succ 0 ((n : Int) + 1) (by omega), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Int.mul_add, ih, Int.add_mul]
    omega

theorem sumTo.proof.refines : sumTo.obligation.refines := by
  intro n
  simp only [sumTo]
  simp
  have h : (2 * LeanTsEmbed.sum.sums.sumTo n : Int) = (n : Int) * (n + 1) := by
    exact_mod_cast LeanTsEmbed.sum.sums.two_mul_sumTo n
  have := two_mul_loop n
  omega

theorem sumTo.proof.returnsNat : sumTo.obligation.returnsNat := by
  intro n
  rw [sumTo.proof.refines n]
  omega

end LeanTsModel.sum
