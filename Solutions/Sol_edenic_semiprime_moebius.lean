import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_moebius
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ArithmeticFunction.moebius n = 1 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have h1 : ArithmeticFunction.moebius (p * (p + 2)) =
      ArithmeticFunction.moebius p * ArithmeticFunction.moebius (p + 2) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (twin_primes_coprime p hp hp2)
  rw [ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hp2] at h1
  norm_num at h1
  exact h1

-- #44
