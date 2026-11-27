import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # An even-gap semiprime is at least 3(k + 3)

Published as `gap_semiprime_ge_even` (prove2.me, theorem id
`862404e4-c5ab-4667-be2e-239085673772`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_ge_even.lean`. -/

theorem gap_semiprime_ge_even (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) : 3 * (k + 3) ≤ n := by
  sorry
