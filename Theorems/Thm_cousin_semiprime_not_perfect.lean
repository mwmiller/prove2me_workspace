import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is never a perfect number

Published as `cousin_semiprime_not_perfect` (prove2.me, theorem id
`64ef0cb4-446f-454a-aa40-0a8b1f9d4390`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_not_perfect.lean`. -/

theorem cousin_semiprime_not_perfect (n : ℕ) (h : IsCousinSemiprime n) :
    ¬Nat.Perfect n := by
  sorry
