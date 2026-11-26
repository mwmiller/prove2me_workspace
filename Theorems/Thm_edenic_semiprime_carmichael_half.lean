import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # An Edenic semiprime fails the Korselt divisibility p + 1 ∣ n − 1

Published as `edenic_semiprime_carmichael_half` (prove2.me, theorem id
`d8c19cc7-5eab-468a-af1c-25731d5f53c0`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_carmichael_half.lean`. -/

theorem edenic_semiprime_carmichael_half (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ ¬(p + 1 ∣ n - 1) := by
  sorry
