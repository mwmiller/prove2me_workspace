import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_sigma_four

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    (∑ d ∈ n.divisors, d) % 4 = 0 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  have hc : p.Coprime (p + 4) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · omega
  have hσ : ∑ d ∈ (p * (p + 4)).divisors, d = (p + 1) * (p + 5) := by
    rw [Nat.Coprime.sum_divisors_mul hc, Nat.Prime.divisors hp, Nat.Prime.divisors hq,
      Finset.sum_pair hp.ne_one.symm, Finset.sum_pair hq.ne_one.symm]
    ring
  rw [hσ]
  have h2a : 2 ∣ p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h2b : 2 ∣ p + 5 := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨c, hc1⟩ := h2a
  obtain ⟨d, hd1⟩ := h2b
  have h4 : 4 ∣ (p + 1) * (p + 5) := ⟨c * d, by rw [hc1, hd1]; ring⟩
  exact Nat.dvd_iff_mod_eq_zero.mp h4
