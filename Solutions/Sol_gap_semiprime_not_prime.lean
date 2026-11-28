import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (h : IsGapSemiprime k n) : ¬n.Prime := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  exact Nat.not_prime_mul hp.ne_one (by omega)
