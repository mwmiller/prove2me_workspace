import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_nonnegative_all_real

set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08.StageB

-- Proof mirrored from accepted submission 54f4d07f-f04f-4f59-853b-5f250d2f1ccb (by WillR).
theorem Kyprianou.Ch08.StageB.source_real_discount_series_nonnegative (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, 0 ≤
      (∑' n : ℕ, q ^ n * scaleConvolutionPower (W 0) n x) := by
  intro x
  apply tsum_nonneg
  intro n
  exact mul_nonneg (pow_nonneg hq _)
    (source_scale_power_nonnegative_all_real ψ W hW n x)
