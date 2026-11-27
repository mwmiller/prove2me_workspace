import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is never a perfect number

Published as `gap_semiprime_not_perfect` (prove2.me, theorem id
`a56c1bd6-7cac-4bba-bb70-4680551f9243`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_not_perfect.lean`. -/

theorem gap_semiprime_not_perfect (k n : ℕ) (hn : n ≠ 6) (h : IsGapSemiprime k n) :
    ¬Nat.Perfect n := by
  sorry
