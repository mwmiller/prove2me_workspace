import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_twelve
import Theorems.Thm_edenic_semiprime_mod_four
import Theorems.Thm_edenic_semiprime_mod_six

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 12 = 11 ∨ n = 15 := by
  have h4 := edenic_semiprime_mod_four n h
  rcases edenic_semiprime_mod_six n h with h6 | h15
  · left
    omega
  · right
    exact h15

-- #48
