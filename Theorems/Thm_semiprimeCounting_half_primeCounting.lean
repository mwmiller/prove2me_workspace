import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # primeCounting(n/2) is at most semiprimeCounting(n)

Published as `semiprimeCounting_half_primeCounting` (prove2.me, theorem id
`d6944171-72e4-5c72-9566-e40e8d2401b6`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprimeCounting_half_primeCounting.lean`. -/

theorem semiprimeCounting_half_primeCounting (n : ℕ) :
    Nat.primeCounting (n / 2) ≤ semiprimeCounting n := by
  sorry
