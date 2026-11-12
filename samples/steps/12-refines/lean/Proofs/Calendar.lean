import LeanTsModel.calendar

namespace LeanTsModel.calendar

theorem tmod_eq_zero (y k : Int) : y.tmod k = 0 ↔ y % k = 0 := by
  rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]

theorem tmod_beq (y k : Int) : (y.tmod k == 0) = (y % k == 0) := by
  have := tmod_eq_zero y k
  cases h1 : (y.tmod k == 0) <;> cases h2 : (y % k == 0) <;> simp_all

theorem isLeap.proof.refines : isLeap.obligation.refines := by
  intro year
  simp only [isLeap, Ts.rem, LeanTsEmbed.calendar.calendar.leap]
  simp
  by_cases h4 : year % 4 = 0 <;> by_cases h100 : year % 100 = 0 <;>
    simp_all [tmod_eq_zero, tmod_beq, pure, Except.pure]

end LeanTsModel.calendar
