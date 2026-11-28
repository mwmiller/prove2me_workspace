import Mathlib.Analysis.Analytic.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_coeff_majorant
import Theorems.Thm_Kyprianou_Ch08_StageB_factorial_bounded_complex_series_entire

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch08.StageB

/-- Entire complex dependence of the scale-function causal convolution series. -/
-- Proof mirrored from accepted submission e5d5fe4c-4e59-4141-99b1-e28bfc1c9733 (by WillR).
theorem source_scale_convolution_series_entire :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x : ℝ), 0 ≤ x →
        Differentiable ℂ (fun z : ℂ =>
          ∑' n : ℕ, z ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)) := by
  intro ψ W hW x hx
  have hmono := source_family_positive_monotone ψ W hW 0
      (le_refl (0 : ℝ))
  have hM : 0 ≤ W 0 x := hmono.1 x
  have hR : 0 ≤ x * W 0 x := mul_nonneg hx hM
  have hint := source_scale_all_power_local_integrability ψ W hW
  have hbound := source_scale_convolution_coeff_majorant ψ W hW hint x hx
  exact factorial_bounded_complex_series_entire
      (fun n => scaleConvolutionPower (W 0) n x)
      (W 0 x) (x * W 0 x) hM hR hbound

end Kyprianou.Ch08.StageB
