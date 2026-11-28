import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (h : IsGapSemiprime k n) : 2 * k + 4 ≤ n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have h1 : 2 * (2 + k) ≤ p * (p + k) := Nat.mul_le_mul (by omega) (by omega)
  rw [show 2 * k + 4 = 2 * (2 + k) from by ring]
  exact h1
