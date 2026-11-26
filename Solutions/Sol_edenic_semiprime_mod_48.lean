import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_48
import Theorems.Thm_edenic_semiprime_mod_sixteen
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 48 = 35 ∨ n % 48 = 47 ∨ n = 15 := by
  rcases edenic_semiprime_mod_sixteen n h with h16 | h16
  · rcases edenic_semiprime_mod_six n h with h6 | h15
    · left
      omega
    · right
      right
      exact h15
  · rcases edenic_semiprime_mod_six n h with h6 | h15
    · right
      left
      omega
    · right
      right
      exact h15

-- #43
