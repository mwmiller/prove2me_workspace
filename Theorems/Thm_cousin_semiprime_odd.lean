import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A cousin semiprime is odd

Published as `cousin_semiprime_odd` (prove2.me, theorem id
`030c390c-f60d-53e1-a7cc-c6c55fafd83c`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_cousin_semiprime_odd.lean`. -/

theorem cousin_semiprime_odd (n : ℕ) (h : IsCousinSemiprime n) : Odd n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  exact Odd.mul (Nat.odd_iff.mpr hpe) (Nat.odd_iff.mpr (by omega))
