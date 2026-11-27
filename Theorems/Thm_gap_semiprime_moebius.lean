import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The Möbius function of a gap semiprime is 1

Published as `gap_semiprime_moebius` (prove2.me, theorem id
`bd4e4be6-d971-5aeb-851c-2fca332e3a7d`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_moebius.lean`. -/

theorem gap_semiprime_moebius (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ArithmeticFunction.moebius n = 1 := by
  sorry
