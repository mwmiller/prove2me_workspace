import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Edenic semiprimes modulo 7

Published as `edenic_semiprime_mod_seven` (prove2.me, theorem id
`55cc6a31-b31b-4d21-aa8a-4003994e525c`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_mod_seven.lean`. -/

theorem edenic_semiprime_mod_seven (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 7 = 1 ∨ n % 7 = 3 ∨ n % 7 = 6 ∨ n = 35 := by
  sorry
