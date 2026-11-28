import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution : Monotone semiprimeCounting := by
  intro m n hmn
  simp only [semiprimeCounting]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨Nat.lt_of_lt_of_le hx.1 (Nat.succ_le_succ hmn), hx.2⟩
