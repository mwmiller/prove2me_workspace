import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is never a perfect power

Published as `gap_semiprime_not_perfect_power` (prove2.me, theorem id
`041206f7-2e6f-4342-91aa-99db52e150d9`). Statement skeleton; the proof
lives in `Solutions/Sol_gap_semiprime_not_perfect_power.lean`. -/

theorem gap_semiprime_not_perfect_power (k n : ℕ) (hk : k ≠ 0)
    (h : IsGapSemiprime k n) : ¬∃ a m : ℕ, 2 ≤ m ∧ a ^ m = n := by
  sorry
