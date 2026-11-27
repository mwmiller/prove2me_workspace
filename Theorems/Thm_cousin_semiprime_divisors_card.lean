import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime has exactly four divisors

Published as `cousin_semiprime_divisors_card` (prove2.me, theorem id
`b5ca1856-4e1d-55a2-8826-256f295b98ec`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_divisors_card.lean`. -/

theorem cousin_semiprime_divisors_card (n : ℕ) (h : IsCousinSemiprime n) :
    (Nat.divisors n).card = 4 := by
  sorry
