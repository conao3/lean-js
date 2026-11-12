import LeanTsModel.dist

namespace LeanTsModel.dist

theorem distance.proof.nonneg : distance.obligation.nonneg := by
  intro a b
  simp only [distance, LeanTsEmbed.dist.spec.nonneg]
  by_cases h : a > b <;> simp [h] <;> omega

theorem distance.proof.symmetric : distance.obligation.symmetric := by
  intro a b
  simp only [distance, LeanTsEmbed.dist.spec.symmetric]
  by_cases h : a > b <;> simp [h]

end LeanTsModel.dist
