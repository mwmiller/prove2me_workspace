import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Edenic semiprimes are 3 or 15 modulo 16

Published as `edenic_semiprime_mod_sixteen` (prove2.me, theorem id
`f0408b6e-1d88-415b-a970-3461d6f9004a`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_mod_sixteen.lean`. -/

theorem edenic_semiprime_mod_sixteen (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 16 = 3 ∨ n % 16 = 15 := by
  sorry
