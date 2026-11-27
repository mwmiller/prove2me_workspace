import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is nonzero

Published as `cousin_semiprime_ne_zero` (prove2.me, theorem id
`a60c1881-181c-558e-a1cc-9816c894100e`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_ne_zero.lean`. -/

theorem cousin_semiprime_ne_zero (n : ℕ) (h : IsCousinSemiprime n) : n ≠ 0 := by
  sorry
