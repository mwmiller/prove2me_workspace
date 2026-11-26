import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_twenty_four
import Theorems.Thm_edenic_semiprime_mod_eight
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 24 = 11 ∨ n % 24 = 23 ∨ n = 15 := by
  rcases edenic_semiprime_mod_eight n h with h8 | h8
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

-- #42
