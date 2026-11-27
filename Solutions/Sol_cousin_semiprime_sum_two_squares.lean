import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_cousin_semiprime_sum_two_squares

theorem solution (n : ℕ) (h : IsCousinSemiprime n) :
    ∃ p, p.Prime ∧ (p + 4).Prime ∧ n = p * (p + 4) ∧
      ((∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ p % 4 = 1) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  refine ⟨p, hp, hq, rfl, ?_⟩
  rw [Nat.eq_sq_add_sq_iff]
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      exact absurd hq (by norm_num)
    · exact hodd
  have hpp : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hc : p.Coprime (p + 4) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · omega
  constructor
  · intro hf
    rcases hpp with hp4 | hp4
    · exact hp4
    · have hmem : p ∈ (p * (p + 4)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p (p + 4),
          mul_ne_zero hp.ne_zero (by omega)⟩
      have hE := hf p hmem hp4
      have hpk4 : ¬p ∣ (p + 4) := fun hd => by
        have h1 : p ∣ 1 := by
          rw [← hc]
          exact Nat.dvd_gcd (dvd_refl p) hd
        exact absurd (Nat.dvd_one.mp h1) hp.ne_one
      have hval : padicValNat p (p * (p + 4)) = 1 := by
        have hfact : Fact (Nat.Prime p) := ⟨hp⟩
        have hp2 : 2 ≤ p := hp.two_le
        rw [padicValNat.mul, padicValNat.self, padicValNat.eq_zero_of_not_dvd hpk4]
        all_goals omega
      rw [hval] at hE
      rcases hE with ⟨t, ht⟩
      omega
  · intro hp4 q hqmem hq4
    have hq' : q = p ∨ q = p + 4 := by
      rcases Nat.mem_primeFactors.mp hqmem with ⟨hqP, hd, -⟩
      rw [Nat.Prime.dvd_mul hqP] at hd
      rcases hd with hd | hd
      · rcases (Nat.dvd_prime hp).mp hd with h1 | h2
        · exact absurd h1 hqP.ne_one
        · exact Or.inl h2
      · rcases (Nat.dvd_prime hq).mp hd with h1 | h2
        · exact absurd h1 hqP.ne_one
        · exact Or.inr h2
    rcases hq' with rfl | rfl <;> omega
