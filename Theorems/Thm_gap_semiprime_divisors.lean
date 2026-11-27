import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The divisors of a gap semiprime

Published as `gap_semiprime_divisors` (prove2.me, theorem id
`08695295-8dd0-5063-844b-180512b7cc33`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_divisors.lean`. -/

theorem gap_semiprime_divisors (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.divisors = {1, p, p + k, n} := by
  sorry
