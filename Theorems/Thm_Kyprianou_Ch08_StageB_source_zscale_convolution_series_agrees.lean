import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_interval_convolution_tsum

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch08.StageB

/-- Real restriction of the integrated causal-convolution Z-scale series. -/
-- Proof mirrored from accepted submission daba9ca4-6873-49c0-aeaa-e69897543e72 (by WillR).
theorem source_zscale_convolution_series_agrees
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) (hx : 0 < x)
    (q : ℝ) (hq : 0 ≤ q) :
    (fun z : ℂ => 1 + z * ∑' n : ℕ,
        z ^ n * (((∫ y in (0 : ℝ)..x,
          scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) (q : ℂ) = (Zscale q (W q) x : ℂ) := by
  have h := source_scale_interval_convolution_tsum ψ W hW x hx q hq
  change (1 : ℂ) + (q : ℂ) *
      (∑' n : ℕ, (q : ℂ) ^ n *
        (((∫ y in (0 : ℝ)..x, scaleConvolutionPower (W 0) n y) : ℝ) : ℂ)) =
      ((1 + q * (∫ y in (0 : ℝ)..x, W q y) : ℝ) : ℂ)
  rw [h.2]
  simp only [Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_tsum, Complex.ofReal_pow, Complex.ofReal_one]

end Kyprianou.Ch08.StageB
