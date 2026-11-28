import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (n : ℕ) (h : IsCousinSemiprime n) : Odd n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  exact Odd.mul (Nat.odd_iff.mpr hpe) (Nat.odd_iff.mpr (by omega))
