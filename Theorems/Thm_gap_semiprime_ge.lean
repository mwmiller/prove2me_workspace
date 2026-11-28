import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is at least 2k + 4

Published as `gap_semiprime_ge` (prove2.me, theorem id
`8f0a0b8c-46f1-44e2-8198-67417fae78a3`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_ge.lean`. -/

theorem gap_semiprime_ge (k n : ℕ) (h : IsGapSemiprime k n) : 2 * k + 4 ≤ n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : 2 * (2 + k) ≤ p * (p + k) := Nat.mul_le_mul (by omega) (by omega)
  rw [show 2 * k + 4 = 2 * (2 + k) from by ring]
  exact h1
