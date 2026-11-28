import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product

open AvramDividend.Classical MeasureTheory Set
-- Proof mirrored from accepted submission 92c94bf0-fbb8-4f4f-8def-b8ff4933ef2b (by fizzyinc3).
theorem AvramDividend.Classical.causal_convolution_powers_laplace_geometric
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (θ A : ℝ)
    (hκi : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * κ t)
      (Ioi (0 : ℝ)) volume)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) * F n t)
      (Ioi (0 : ℝ)) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) = fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume)
    (hκmass : (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * κ t ∂volume) = A) :
    ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * F n t ∂volume) =
        A ^ (n + 1) := by 
  intro n
  induction n with
  | zero => rw [hF0, hκmass]; ring
  | succ n ih =>
    rw [hFsucc n, positive_causal_convolution_laplace_product κ (F n) θ hκi (hFi n), hκmass, ih]
    ring
