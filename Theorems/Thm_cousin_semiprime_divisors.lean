import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The divisors of a cousin semiprime

Published as `cousin_semiprime_divisors` (prove2.me, theorem id
`d14b6d61-b380-503b-ba2f-6c2648862acd`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_divisors.lean`. -/

theorem cousin_semiprime_divisors (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      n.divisors = {1, p, p + 4, n} := by
  sorry
