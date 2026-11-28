import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_ge_21
import Theorems.Thm_gap_semiprime_four_iff
import Theorems.Thm_gap_semiprime_not_perfect

/-! # A cousin semiprime is never a perfect number

Published as `cousin_semiprime_not_perfect` (prove2.me, theorem id
`64ef0cb4-446f-454a-aa40-0a8b1f9d4390`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_not_perfect.lean`. -/

theorem cousin_semiprime_not_perfect (n : ℕ) (h : IsCousinSemiprime n) :
    ¬Nat.Perfect n := by
  have h21 : 21 ≤ n := cousin_semiprime_ge_21 n h
  exact gap_semiprime_not_perfect 4 n (by omega) ((gap_semiprime_four_iff n).mp h)
