import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_semiprimeCounting_even

/-! # primeCounting(n/2) is at most semiprimeCounting(n)

Published as `semiprimeCounting_half_primeCounting` (prove2.me, theorem id
`d6944171-72e4-5c72-9566-e40e8d2401b6`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_semiprimeCounting_half_primeCounting.lean`. -/

theorem semiprimeCounting_half_primeCounting (n : ℕ) :
    Nat.primeCounting (n / 2) ≤ semiprimeCounting n := by
  rw [← semiprimeCounting_even n]
  simp only [semiprimeCounting]
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩
