import LeanTsModel.search

namespace LeanTsModel.search

theorem sortedIncludes.proof.refines : sortedIncludes.obligation.refines := by
  intro xs x h
  simp only [LeanTsEmbed.search.spec.sortedInput, LeanTsEmbed.search.spec.sorted,
    decide_eq_true_eq] at h
  simp only [sortedIncludes, LeanTsEmbed.search.spec.includes]
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [List.pairwise_cons] at h
    by_cases hyx : y = x
    · simp [hyx]
    · by_cases hlt : x < y
      · have : x ∉ ys := fun hx => by have := h.1 x hx; omega
        simp [hyx, hlt, this]
        omega
      · have hxy : ¬x = y := fun e => hyx e.symm
        simp [hyx, hlt] at ih ⊢
        simp [hxy, ih h.2]

end LeanTsModel.search
