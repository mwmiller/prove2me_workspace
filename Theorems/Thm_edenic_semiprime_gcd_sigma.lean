import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # An Edenic semiprime is coprime to its divisor sum, except 15

Published as `edenic_semiprime_gcd_sigma` (prove2.me, theorem id
`cd5454ed-8d24-4d71-9faa-2199a3458ed7`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_gcd_sigma.lean`. -/

theorem edenic_semiprime_gcd_sigma (n : ℕ) (h : IsEdenicSemiprime n) :
    n.Coprime (∑ d ∈ n.divisors, d) ∨ n = 15 := by
  sorry
