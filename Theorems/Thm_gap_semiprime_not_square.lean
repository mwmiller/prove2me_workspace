import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is never a perfect square

Published as `gap_semiprime_not_square` (prove2.me, theorem id
`5f579cd8-9369-5b69-a4ea-1fa87a430157`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_not_square.lean`. -/

theorem gap_semiprime_not_square (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ¬∃ x, x ^ 2 = n := by
  sorry
