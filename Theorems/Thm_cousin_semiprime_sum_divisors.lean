import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The sum-of-divisors of a cousin semiprime

Published as `cousin_semiprime_sum_divisors` (prove2.me, theorem id
`7f900f18-47c1-43ae-831c-93c234c4a183`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_sum_divisors.lean`. -/

theorem cousin_semiprime_sum_divisors (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + 5) := by
  sorry
