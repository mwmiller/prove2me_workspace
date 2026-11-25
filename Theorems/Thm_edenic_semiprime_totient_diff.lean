import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # The totient deficit of an Edenic semiprime is 2p+1

Published as `edenic_semiprime_totient_diff` (prove2.me, theorem id
`999a82fc-bb2f-5565-8bbb-c357bbe13388`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_totient_diff.lean`. -/

theorem edenic_semiprime_totient_diff (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ n - n.totient = 2 * p + 1 := by
  sorry
