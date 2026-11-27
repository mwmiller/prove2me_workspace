import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is at least 2k + 4

Published as `gap_semiprime_ge` (prove2.me, theorem id
`8f0a0b8c-46f1-44e2-8198-67417fae78a3`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_ge.lean`. -/

theorem gap_semiprime_ge (k n : ℕ) (h : IsGapSemiprime k n) : 2 * k + 4 ≤ n := by
  sorry
