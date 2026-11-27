import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is never a perfect power

Published as `cousin_semiprime_not_perfect_power` (prove2.me, theorem id
`5bb8b89b-cdff-48f2-9918-9978502f1310`). Statement skeleton; the proof
lives in `Solutions/Sol_cousin_semiprime_not_perfect_power.lean`. -/

theorem cousin_semiprime_not_perfect_power (n : ℕ) (h : IsCousinSemiprime n) :
    ¬∃ a m : ℕ, 2 ≤ m ∧ a ^ m = n := by
  sorry
