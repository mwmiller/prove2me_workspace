import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # The divisor sum of an Edenic semiprime is divisible by 8

Published as `edenic_semiprime_sigma_eight` (prove2.me, theorem id
`d7ae974e-f6a7-4f46-801a-1ff3e1be1c63`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_sigma_eight.lean`. -/

theorem edenic_semiprime_sigma_eight (n : ℕ) (h : IsEdenicSemiprime n) :
    (∑ d ∈ n.divisors, d) % 8 = 0 := by
  sorry
