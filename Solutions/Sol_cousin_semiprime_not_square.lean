import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_square

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ x, x ^ 2 = n :=
  gap_semiprime_not_square 4 n (by norm_num) ((gap_semiprime_four_iff n).mp h)
