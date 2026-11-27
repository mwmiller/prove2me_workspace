import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Cousin semiprimes are 5 modulo 12, except 21

Published as `cousin_semiprime_mod_twelve` (prove2.me, theorem id
`a6b24519-7747-5c2f-971d-7fdb3251fdab`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_mod_twelve.lean`. -/

theorem cousin_semiprime_mod_twelve (n : ℕ) (h : IsCousinSemiprime n) :
    n % 12 = 5 ∨ n = 21 := by
  sorry
