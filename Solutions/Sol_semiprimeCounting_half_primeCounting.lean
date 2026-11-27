import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_semiprimeCounting_half_primeCounting
import Theorems.Thm_semiprimeCounting_even

theorem solution (n : ℕ) :
    Nat.primeCounting (n / 2) ≤ semiprimeCounting n := by
  rw [← semiprimeCounting_even n]
  simp only [semiprimeCounting]
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩
