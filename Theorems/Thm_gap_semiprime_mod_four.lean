import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Even-gap semiprimes are 1 mod 4 exactly when the gap is 0 mod 4

Published as `gap_semiprime_mod_four` (prove2.me, theorem id
`92d077c2-67c6-4113-abc2-6d2af6c3ec7e`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_mod_four.lean`. -/

theorem gap_semiprime_mod_four (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) : n % 4 = 1 ↔ k % 4 = 0 := by
  sorry
