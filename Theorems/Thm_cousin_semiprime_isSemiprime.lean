import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Every cousin semiprime is a semiprime

Published as `cousin_semiprime_isSemiprime` (prove2.me, theorem id
`1e415b59-5830-41e6-9ed8-2b556d71169e`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_isSemiprime.lean`. -/

theorem cousin_semiprime_isSemiprime (n : ℕ) (h : IsCousinSemiprime n) :
    Nat.IsSemiprime n := by
  sorry
