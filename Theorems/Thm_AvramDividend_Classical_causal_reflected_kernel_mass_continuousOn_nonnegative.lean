import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_continuousOn_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

-- Proof mirrored from accepted submission 3e7ce57f-9bd4-4af1-9830-413b8cdb5872 (by WillR).
theorem AvramDividend.Classical.causal_reflected_kernel_mass_continuousOn_nonnegative
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume)
      (Ici (0 : ℝ)) := by
  have hPrimitive :=
    causal_l1_primitive_continuousOn_nonnegative K hK
  have hEq : ∀ x : ℝ, x ∈ Ici (0 : ℝ) →
      (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, K s ∂volume) := by
    intro x hx
    simpa only [mul_one] using
      (causal_convolution_time_reversal
        K (fun _ : ℝ => (1 : ℝ)) x hx)
  exact hPrimitive.congr hEq
