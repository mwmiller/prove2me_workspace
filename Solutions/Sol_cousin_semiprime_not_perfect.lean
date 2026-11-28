import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_ge_21
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_perfect

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ¬Nat.Perfect n := by
  have h21 : 21 ≤ n := cousin_semiprime_ge_21 n h
  exact gap_semiprime_not_perfect 4 n (by omega) ((gap_semiprime_four_iff n).mp h)
