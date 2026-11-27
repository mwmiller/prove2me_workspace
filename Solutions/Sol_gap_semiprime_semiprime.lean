import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_semiprime

theorem solution (k n : ℕ) (h : IsGapSemiprime k n) :
    Nat.IsSemiprime n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  exact hp.mul_isAlmostPrime_two hq
