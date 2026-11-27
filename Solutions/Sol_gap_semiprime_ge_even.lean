import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_ge_even

theorem solution (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) : 3 * (k + 3) ≤ n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      have hk2 : (2 + k) % 2 = 0 := by omega
      rcases hq.eq_two_or_odd with h2' | hodd'
      · omega
      · omega
    · exact hodd
  have h1 : 3 * (3 + k) ≤ p * (p + k) := Nat.mul_le_mul (by omega) (by omega)
  rw [show 3 * (k + 3) = 3 * (3 + k) from by ring]
  exact h1
