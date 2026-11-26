import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # The successor of an Edenic semiprime divides 36 only for 35

Published as `edenic_semiprime_succ_div_36` (prove2.me, theorem id
`cc90b55d-5c17-5669-91d2-1948aa67a0f1`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_succ_div_36.lean`. -/

theorem edenic_semiprime_succ_div_36 (n : ℕ) (h : IsEdenicSemiprime n) :
    (n + 1 ∣ 36) ↔ n = 35 := by
  sorry
