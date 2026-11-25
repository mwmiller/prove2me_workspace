import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Edenic semiprimes modulo 5

Published as `edenic_semiprime_mod_five` (prove2.me, theorem id
`118a0431-f6a4-515a-9fb7-a9fadff9d0d1`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_mod_five.lean`. -/

theorem edenic_semiprime_mod_five (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 5 = 3 ∨ n % 5 = 4 ∨ n = 15 ∨ n = 35 := by
  sorry
