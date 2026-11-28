import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ArithmeticFunction.moebius n = 1 := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  have h1 : ArithmeticFunction.moebius (p * (p + k)) =
      ArithmeticFunction.moebius p * ArithmeticFunction.moebius (p + k) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
  rw [ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq] at h1
  norm_num at h1
  exact h1
