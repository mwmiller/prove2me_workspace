import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The integral of a nonnegative L1 renewal series equals the sum of masses. -/
-- Proof mirrored from accepted submission f00248b4-7fcf-4570-bcb1-e391631a80d6 (by WillR).
theorem AvramDividend.Classical.nonnegative_renewal_integral_tsum_exchange
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ)
    (hFi : ∀ n : ℕ, Integrable (F n) μ)
    (hpos : ∀ n : ℕ, ∀ x : α, 0 ≤ F n x)
    (hmass : Summable (fun n : ℕ => ∫ x : α, F n x ∂μ)) :
    (∫ x : α, ∑' n : ℕ, F n x ∂μ) =
      ∑' n : ℕ, ∫ x : α, F n x ∂μ := by
  have hnorm (n : ℕ) :
      (fun x : α => ‖F n x‖) = F n := by
    funext x
    simp [Real.norm_eq_abs, abs_of_nonneg (hpos n x)]
  have hIntEq :
      (fun n : ℕ => ∫ x : α, ‖F n x‖ ∂μ) =
        (fun n : ℕ => ∫ x : α, F n x ∂μ) := by
    funext n
    rw [hnorm n]
  have hsumNorm :
      Summable (fun n : ℕ => ∫ x : α, ‖F n x‖ ∂μ) := by
    rw [hIntEq]
    exact hmass
  exact (integral_tsum_of_summable_integral_norm hFi hsumNorm).symm
