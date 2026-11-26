import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Edenic semiprimes are 35 or 47 modulo 48, except 15

Published as `edenic_semiprime_mod_48` (prove2.me, theorem id
`a9c6c810-9f52-4ba3-8b21-6450f150bed7`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_mod_48.lean`. -/

theorem edenic_semiprime_mod_48 (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 48 = 35 ∨ n % 48 = 47 ∨ n = 15 := by
  sorry
