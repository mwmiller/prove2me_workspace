import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_ge_21

theorem solution (n : ℕ) (h : IsCousinSemiprime n) : n ≠ 0 := by
  have h21 : 21 ≤ n := cousin_semiprime_ge_21 n h
  omega

/-! # Family C: semiprime counting (C1–C6) -/
