import Theorems.Thm_AvramDividend_Classical_causal_geometric_laplace_series_integral
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open AvramDividend.Classical MeasureTheory Set
-- Proof mirrored from accepted submission d7bd21fc-2630-4661-a5be-018f72525db9 (by fizzyinc3).
theorem AvramDividend.Classical.causal_geometric_laplace_resolvent_series
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) * (∑' n : ℕ, F n x) ∂volume) =
        ρ / (1 - ρ) := by 
  simp_rw [← tsum_mul_left]
  exact causal_geometric_laplace_series_integral F θ ρ hρ0 hρ1 hFi hpos hmass
