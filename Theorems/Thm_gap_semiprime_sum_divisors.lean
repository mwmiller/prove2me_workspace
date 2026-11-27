import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The sum-of-divisors of a gap semiprime

Published as `gap_semiprime_sum_divisors` (prove2.me, theorem id
`c93ab500-1e4b-41ef-af4c-5b86be2d57e4`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_sum_divisors.lean`. -/

theorem gap_semiprime_sum_divisors (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + k + 1) := by
  sorry
