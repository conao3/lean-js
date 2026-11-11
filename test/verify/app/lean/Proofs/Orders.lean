import LeanTsModel.orders

namespace LeanTsModel.orders

theorem lineTotal.proof.refines : lineTotal.obligation.refines := by
  intro l
  simp [lineTotal, LeanTsEmbed.orders.orders.lineTotal]

theorem quantity.proof.positive : quantity.obligation.positive := by
  intro l
  have := l.qty_ge
  simp [quantity, LeanTsEmbed.orders.orders.positive]
  omega

end LeanTsModel.orders
