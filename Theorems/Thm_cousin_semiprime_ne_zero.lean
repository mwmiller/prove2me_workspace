import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_ge_21

/-! # A cousin semiprime is nonzero

Published as `cousin_semiprime_ne_zero` (prove2.me, theorem id
`a60c1881-181c-558e-a1cc-9816c894100e`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_ne_zero.lean`. -/

theorem cousin_semiprime_ne_zero (n : ℕ) (h : IsCousinSemiprime n) : n ≠ 0 := by
  have h21 : 21 ≤ n := cousin_semiprime_ge_21 n h
  omega

/-! # Family C: semiprime counting (C1–C6) -/
