import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_not_perfect_power
import Theorems.Thm_gap_semiprime_squarefree

theorem solution (k n : ℕ) (hk : k ≠ 0)
    (h : IsGapSemiprime k n) : ¬∃ a m : ℕ, 2 ≤ m ∧ a ^ m = n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  rintro ⟨a, m, hm2, ham⟩
  have hp2le : 2 ≤ p := hp.two_le
  have ha2 : 2 ≤ a := by
    rcases (by omega : a < 2 ∨ 2 ≤ a) with ha | ha
    · have h01 : a = 0 ∨ a = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [zero_pow (by omega)] at ham
        nlinarith
      · rw [one_pow] at ham
        nlinarith
    · exact ha
  obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd (n := a) (by omega)
  have hrm : r ^ m ∣ a ^ m := pow_dvd_pow_of_dvd hra m
  have hr2 : r ^ 2 ∣ r ^ m := pow_dvd_pow r hm2
  have hr2n : r ^ 2 ∣ p * (p + k) := by
    rw [← ham]
    exact dvd_trans hr2 hrm
  have hsq : Squarefree (p * (p + k)) :=
    gap_semiprime_squarefree k _ hk ⟨p, hp, hq, rfl⟩
  have hru : IsUnit r := hsq r (by rw [pow_two] at hr2n; exact hr2n)
  exact absurd (Nat.isUnit_iff.mp hru) hr.ne_one
