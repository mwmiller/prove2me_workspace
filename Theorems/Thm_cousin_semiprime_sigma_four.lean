import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The sum-of-divisors of a cousin semiprime is 0 modulo 4

Published as `cousin_semiprime_sigma_four` (prove2.me, theorem id
`bceb39ff-0845-5917-a09f-11edc5d51c35`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_sigma_four.lean`. -/

theorem cousin_semiprime_sigma_four (n : ℕ) (h : IsCousinSemiprime n) :
    (∑ d ∈ n.divisors, d) % 4 = 0 := by
  sorry
