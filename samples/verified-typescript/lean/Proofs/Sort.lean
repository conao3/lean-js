import LeanTsModel.sort

namespace LeanTsModel.sort

theorem forIn_push_filter (p : Int → Bool) (xs acc : List Int) :
    forIn (m := Id) xs acc (fun y s =>
      if p y = true then pure (ForInStep.yield (s ++ [y])) else pure (ForInStep.yield s)) =
      pure (acc ++ xs.filter p) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
    by_cases hp : p y = true <;> simp [hp, ih]

theorem insertSorted_eq (x : Int) (xs : List Int) :
    insertSorted x xs = xs.filter (fun y => decide (y < x)) ++ [x] ++ xs.filter (fun y => decide (x ≤ y)) := by
  simp only [insertSorted, forIn_push_filter]
  rfl

theorem sorted_split (x : Int) (xs : List Int) (h : xs.Pairwise (· ≤ ·)) :
    (xs.filter (fun y => decide (y < x)) ++ [x] ++ xs.filter (fun y => decide (x ≤ y))).Pairwise (· ≤ ·) := by
  simp only [List.pairwise_append, List.pairwise_singleton, List.mem_append, List.mem_singleton,
    List.mem_filter, decide_eq_true_eq, true_and]
  refine ⟨⟨h.filter _, fun a ha b hb => ?_⟩, h.filter _, fun a ha b hb => ?_⟩
  · rw [hb]; exact Int.le_of_lt ha.2
  · rcases ha with ha | ha
    · exact Int.le_trans (Int.le_of_lt ha.2) hb.2
    · rw [ha]; exact hb.2

theorem length_split (x : Int) (xs : List Int) :
    (xs.filter (fun y => decide (y < x))).length + (xs.filter (fun y => decide (x ≤ y))).length =
      xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases hy : y < x
    · simp [hy, Int.not_le.mpr hy]; omega
    · simp [hy, Int.not_lt.mp hy]; omega

theorem insertSorted.proof.sorted : insertSorted.obligation.sorted := by
  intro x xs h
  simp only [LeanTsEmbed.sort.spec.resultSorted, LeanTsEmbed.sort.spec.inputSorted,
    LeanTsEmbed.sort.spec.sorted, decide_eq_true_eq] at h ⊢
  rw [insertSorted_eq]
  exact sorted_split x xs h

theorem insertSorted.proof.length : insertSorted.obligation.length := by
  intro x xs _
  simp only [LeanTsEmbed.sort.spec.oneMore, beq_iff_eq, insertSorted_eq, List.length_append,
    List.length_singleton]
  have := length_split x xs
  omega

end LeanTsModel.sort
