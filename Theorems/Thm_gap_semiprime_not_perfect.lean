import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_sum_divisors

/-! # A gap semiprime is never a perfect number

Published as `gap_semiprime_not_perfect` (prove2.me, theorem id
`a56c1bd6-7cac-4bba-bb70-4680551f9243`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_not_perfect.lean`. -/

theorem gap_semiprime_not_perfect (k n : ℕ) (hn : n ≠ 6) (h : IsGapSemiprime k n) :
    ¬Nat.Perfect n := by
  rintro hperf
  by_cases hk : k = 0
  · -- n = p², never a perfect number
    obtain ⟨p, hp, hq, rfl⟩ := h
    subst hk
    have hp2 : 2 ≤ p := hp.two_le
    have hpow : p * (p + 0) = p ^ 2 := by ring
    have h0 : 0 < p * (p + 0) := mul_pos hp.pos (by omega)
    have hsum : ∑ d ∈ (p * (p + 0)).divisors, d = 2 * (p * (p + 0)) :=
      (Nat.perfect_iff_sum_divisors_eq_two_mul h0).mp hperf
    rw [hpow] at hsum
    have hσ : ∑ d ∈ (p ^ 2).divisors, d = 1 + p + p ^ 2 := by
      rw [Nat.sum_divisors_prime_pow hp]
      simp [Finset.sum_range_succ]
    rw [hσ] at hsum
    have hge : 2 * p ≤ p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hp2 (le_refl p)
    nlinarith
  · -- k ≠ 0: perfectness forces (p+1)(p+k+1) = 2p(p+k), whence k ≤ 1
    obtain ⟨p, hp, hq, rfl, hσ⟩ := gap_semiprime_sum_divisors k n hk h
    have hp2 : 2 ≤ p := hp.two_le
    have hsum : ∑ d ∈ (p * (p + k)).divisors, d = 2 * (p * (p + k)) :=
      (Nat.perfect_iff_sum_divisors_eq_two_mul (mul_pos hp.pos (by omega))).mp hperf
    rw [hσ] at hsum
    have hexpand : (p + 1) * (p + k + 1) = p * (p + k) + p + (p + k) + 1 := by ring
    have hlin : p + (p + k) + 1 = p * (p + k) := by nlinarith
    have hL : p ∣ p + (p + k) + 1 := by
      rw [hlin]
      exact dvd_mul_right p (p + k)
    have hM : (p + k) ∣ p + (p + k) + 1 := by
      rw [hlin]
      exact dvd_mul_left (p + k) p
    have hp1 : p ∣ (p + k) + 1 := by
      have h := Nat.dvd_sub hL (dvd_refl p)
      rwa [show p + (p + k) + 1 - p = (p + k) + 1 from by omega] at h
    have hpk1 : (p + k) ∣ p + 1 := by
      have h := Nat.dvd_sub hM (dvd_refl (p + k))
      rwa [show p + (p + k) + 1 - (p + k) = p + 1 from by omega] at h
    have hkle : k ≤ 1 := by
      have hle : p + k ≤ p + 1 := Nat.le_of_dvd (by omega) hpk1
      omega
    rcases (by omega : k = 0 ∨ k = 1) with hkz | hk1
    · rw [hkz] at hp1
      simp only [Nat.add_zero] at hp1
      have hp1' : p ∣ 1 := by
        have h := Nat.dvd_sub hp1 (dvd_refl p)
        rwa [Nat.add_sub_cancel_left] at h
      exact absurd (Nat.dvd_one.mp hp1') hp.ne_one
    · rw [hk1] at hp1
      have hp1' : p ∣ p + 2 := by
        rwa [show (p + 1) + 1 = p + 2 from by ring] at hp1
      have h2 : p ∣ 2 := by
        have h := Nat.dvd_sub hp1' (dvd_refl p)
        rwa [Nat.add_sub_cancel_left] at h
      have hple : p ≤ 2 := Nat.le_of_dvd (by omega) h2
      have hp2' : p = 2 := by omega
      rw [hp2', hk1] at hn
      omega
