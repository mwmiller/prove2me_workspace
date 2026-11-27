import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_succ_is_square

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ k, n + 4 = k ^ 2 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  exact ⟨p + 2, by ring⟩
