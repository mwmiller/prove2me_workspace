import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    n % 12 = 5 ∨ n = 21 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 by omega) with hc0 | hc1 | hc2
  · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hc0
    rcases hp.eq_one_or_self_of_dvd 3 hd with h1 | h2
    · omega
    · subst h2
      right
      norm_num
  · have hp12 : p % 12 = 1 ∨ p % 12 = 7 := by omega
    rcases hp12 with h12 | h7
    · have hq12 : (p + 4) % 12 = 5 := by omega
      left
      rw [Nat.mul_mod, h12, hq12]
    · have hq12 : (p + 4) % 12 = 11 := by omega
      left
      rw [Nat.mul_mod, h7, hq12]
  · have hd : 3 ∣ p + 4 := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hq.eq_one_or_self_of_dvd 3 hd with h1 | h2
    · omega
    · omega
