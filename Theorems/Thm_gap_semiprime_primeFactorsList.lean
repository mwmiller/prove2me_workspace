import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The prime factor list of a gap semiprime

Published as `gap_semiprime_primeFactorsList` (prove2.me, theorem id
`b1c550c0-a711-4e3d-8bd7-06a588bedb9d`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_primeFactorsList.lean`. -/

theorem gap_semiprime_primeFactorsList (k n : ℕ) (hk : k ≠ 0)
    (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.primeFactorsList = [p, p + k] := by
  sorry
