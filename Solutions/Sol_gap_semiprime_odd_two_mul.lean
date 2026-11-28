import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (hk : k % 2 = 1)
    (h : IsGapSemiprime k n) : n = 2 * (2 + k) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  rcases hp.eq_two_or_odd with h2 | hodd
  · rw [h2]
  · have hk2 : (p + k) % 2 = 0 := by omega
    rcases hq.eq_two_or_odd with h2' | hodd'
    · omega
    · omega
