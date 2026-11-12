import LeanTsModel.stock

namespace LeanTsModel.stock

open LeanTsEmbed.stock.spec

theorem foldl_qty (stock : List Item) (a : Int) :
    stock.foldl (fun t i => t + (i.qty : Int)) a = a + LeanTsEmbed.stock.spec.total stock := by
  induction stock generalizing a with
  | nil => simp [LeanTsEmbed.stock.spec.total]
  | cons i is ih => simp [LeanTsEmbed.stock.spec.total, ih] at *; omega

theorem total.proof.refines : total.obligation.refines := by
  intro stock
  simp only [total]
  simp [foldl_qty]

theorem forIn_push_map (p : Item → Bool) (g : Item → Item) (xs acc : List Item) :
    forIn (m := Id) xs acc (fun i s =>
      if p i = true then pure (ForInStep.yield (s ++ [g i])) else pure (ForInStep.yield (s ++ [i]))) =
      pure (acc ++ xs.map fun i => if p i = true then g i else i) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih => by_cases hp : p y = true <;> simp [hp, ih]

def bump (name : String) (n : Nat) (i : Item) : Item :=
  if (i.name == name) = true then { name := i.name, kind := i.kind, qty := ((i.qty : Int) + n).toNat } else i

theorem restock_eq (stock : List Item) (name : String) (n : Nat) :
    restock stock name n = stock.map (bump name n) := by
  simp only [restock, forIn_push_map (fun i => i.name == name)
    (fun i => { name := i.name, kind := i.kind, qty := ((i.qty : Int) + n).toNat })]
  rfl

theorem total_bump (stock : List Item) (name : String) (n : Nat) :
    LeanTsEmbed.stock.spec.total stock ≤ LeanTsEmbed.stock.spec.total (stock.map (bump name n)) := by
  induction stock with
  | nil => simp
  | cons i is ih =>
    simp only [LeanTsEmbed.stock.spec.total, List.map_cons, List.sum_cons] at ih ⊢
    have : (i.qty : Int) ≤ ((bump name n i).qty : Int) := by
      unfold bump; split <;> simp <;> omega
    omega

theorem restock.proof.sameLength : restock.obligation.sameLength := by
  intro stock name n
  simp [LeanTsEmbed.stock.spec.sameLength, restock_eq]

theorem restock.proof.grows : restock.obligation.grows := by
  intro stock name n
  simp only [LeanTsEmbed.stock.spec.grows, restock_eq, decide_eq_true_eq]
  intro _
  exact total_bump stock name n

theorem total_filter (stock : List Item) (p : Item → Bool) :
    LeanTsEmbed.stock.spec.total (stock.filter p) ≤ LeanTsEmbed.stock.spec.total stock := by
  induction stock with
  | nil => simp
  | cons i is ih =>
    simp only [LeanTsEmbed.stock.spec.total, List.filter_cons] at ih ⊢
    split <;> simp at ih ⊢ <;> omega

theorem discard.proof.shrinks : discard.obligation.shrinks := by
  intro stock kind
  simp only [LeanTsEmbed.stock.spec.shrinks, discard, Id.run_pure]
  exact decide_eq_true (total_filter stock _)

theorem discard.proof.without : discard.obligation.without := by
  intro stock kind
  simp [LeanTsEmbed.stock.spec.without, discard]

end LeanTsModel.stock
