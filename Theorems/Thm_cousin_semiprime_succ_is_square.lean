import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Four more than a cousin semiprime is a perfect square

Published as `cousin_semiprime_succ_is_square` (prove2.me, theorem id
`ed7da193-f578-515f-8cb0-96aba747426a`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_succ_is_square.lean`. -/

theorem cousin_semiprime_succ_is_square (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ k, n + 4 = k ^ 2 := by
  sorry
