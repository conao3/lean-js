import LeanTsModel.account

namespace LeanTsModel.account

theorem withdraw.proof.inLimits : withdraw.obligation.inLimits := by
  intro a n
  have := a.balance_le
  simp only [withdraw, LeanTsEmbed.account.spec.inLimits]
  by_cases h1 : n < 0 <;> by_cases h2 : n > (a.balance : Int) <;> simp [h1, h2] <;> omega

end LeanTsModel.account
