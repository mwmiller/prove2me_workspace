import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_not_prime
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_prime

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ¬n.Prime :=
  gap_semiprime_not_prime 4 n ((gap_semiprime_four_iff n).mp h)
