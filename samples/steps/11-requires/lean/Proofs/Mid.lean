import LeanTsModel.mid

namespace LeanTsModel.mid

theorem midpoint.proof.between : midpoint.obligation.between := by
  intro lo hi h r hr
  simp only [LeanTsEmbed.mid.spec.ordered, decide_eq_true_eq] at h
  simp only [midpoint, Ts.floorDiv] at hr
  simp at hr
  have hr : lo + (hi - lo).fdiv 2 = r := Except.ok.inj hr
  subst hr
  simp only [LeanTsEmbed.mid.spec.between, Bool.and_eq_true, decide_eq_true_eq]
  rw [Int.fdiv_eq_ediv]
  simp
  omega

end LeanTsModel.mid
