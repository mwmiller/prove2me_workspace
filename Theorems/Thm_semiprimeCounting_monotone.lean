import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The semiprime counting function is monotone

Published as `semiprimeCounting_monotone` (prove2.me, theorem id
`15f81efe-a75e-4842-817f-8e58e7d2bc83`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_semiprimeCounting_monotone.lean`. -/

theorem semiprimeCounting_monotone : Monotone semiprimeCounting := by
  intro m n hmn
  simp only [semiprimeCounting]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨Nat.lt_of_lt_of_le hx.1 (Nat.succ_le_succ hmn), hx.2⟩
