import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is a sum of two squares exactly when p = 1 mod 4

Published as `cousin_semiprime_sum_two_squares` (prove2.me, theorem id
`43952879-1f7b-4f86-96d9-22394fb00563`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_sum_two_squares.lean`. -/

theorem cousin_semiprime_sum_two_squares (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      ((∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ p % 4 = 1) := by
  sorry
