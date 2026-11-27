import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is odd

Published as `cousin_semiprime_odd` (prove2.me, theorem id
`030c390c-f60d-53e1-a7cc-c6c55fafd83c`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_odd.lean`. -/

theorem cousin_semiprime_odd (n : ℕ) (h : IsCousinSemiprime n) : Odd n := by
  sorry
