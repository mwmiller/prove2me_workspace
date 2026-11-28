import Mathlib.Analysis.Analytic.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_positive_x
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_at_zero

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch08.StageB

/-- Identification (8.24) of actual q-scale functions with causal convolution series. -/
-- Proof mirrored from accepted submission 6cff7e71-d702-498b-a512-bfd6e3aeabb4 (by WillR).
theorem source_scale_discount_convolution_series :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      HasSourceScaleFamily ψ W →
      ∀ (x q : ℝ), 0 ≤ x → 0 ≤ q →
        ((W q x : ℝ) : ℂ) =
          ∑' n : ℕ, (q : ℂ) ^ n *
            ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ) := by
  intro ψ W hW x q hx hq
  by_cases hzero : x = 0
  · simpa only [hzero] using source_scale_discount_series_at_zero ψ W hW q hq
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    exact source_scale_discount_series_positive_x ψ W hW x q hxpos hq

end Kyprianou.Ch08.StageB
