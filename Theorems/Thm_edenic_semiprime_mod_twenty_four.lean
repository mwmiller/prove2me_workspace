import Mathlib
import Definitions.Def_IsEdenicSemiprime

/-! # Edenic semiprimes are 11 or 23 modulo 24, except 15

Published as `edenic_semiprime_mod_twenty_four` (prove2.me, theorem id
`3614f0a8-f997-5591-b355-fddbfe16f9b8`). Statement skeleton; the proof
lives in `Solutions/Sol_edenic_semiprime_mod_twenty_four.lean`. -/

theorem edenic_semiprime_mod_twenty_four (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 24 = 11 ∨ n % 24 = 23 ∨ n = 15 := by
  sorry
