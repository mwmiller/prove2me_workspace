import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

-- Proof mirrored from accepted submission 2f78df9e-550c-40a2-9f26-2164d52d8f70 (by WillR).
theorem Kyprianou.Ch08.StageB.source_stable_integrated_term_factor (α q β : ℝ) (hβ : 0 < β) :
    ∀ n : ℕ,
      q ^ n * β ^ (-(α * ((n : ℝ) + 1) + 1)) =
        β ^ (-(α + 1)) * (q / β ^ α) ^ n := by
  intro n
  have hexp : -(α * ((n : ℝ) + 1) + 1) =
      -(α + 1) + (-α) * (n : ℝ) := by ring
  rw [hexp, Real.rpow_add hβ, Real.rpow_mul_natCast hβ.le]
  rw [div_eq_mul_inv, mul_pow]
  simp only [Real.rpow_neg hβ.le]
  ring
