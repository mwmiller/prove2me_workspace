import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_isSemiprime
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_semiprime

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    Nat.IsSemiprime n :=
  gap_semiprime_semiprime 4 n ((gap_semiprime_four_iff n).mp h)
