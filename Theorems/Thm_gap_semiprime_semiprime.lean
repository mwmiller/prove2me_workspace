import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Every gap semiprime is a semiprime

Published as `gap_semiprime_semiprime` (prove2.me, theorem id
`a91b6de2-51d6-5357-aeaa-02b49c1919b3`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_semiprime.lean`. -/

theorem gap_semiprime_semiprime (k n : ℕ) (h : IsGapSemiprime k n) :
    Nat.IsSemiprime n := by
  sorry
