import LeanTsModel.more

namespace LeanTsModel.more

theorem code.proof.refines : code.obligation.refines := by
  intro c
  cases c <;> rfl

theorem area.proof.refines : area.obligation.refines := by
  intro s
  cases s <;> simp [area, LeanTsEmbed.more.more.area]

theorem describe.proof.refines : describe.obligation.refines := by
  intro o
  cases o <;> rfl

theorem shift.proof.refines : shift.obligation.refines := by
  intro p d
  rfl

theorem swap.proof.refines : swap.obligation.refines := by
  intro p
  rfl

theorem label.proof.refines : label.obligation.refines := by
  intro n
  rfl

end LeanTsModel.more
