import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant

set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

-- Proof mirrored from accepted submission 85d3fd7b-2eca-48ae-912d-6ee80b02fe7c (by WillR).
theorem Kyprianou.Ch08.StageB.source_scale_discount_series_at_zero (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ((W q 0 : ℝ) : ℂ) =
      ∑' n : ℕ, (q : ℂ) ^ n *
        ((scaleConvolutionPower (W 0) n 0 : ℝ) : ℂ) := by
  have hzero : ∀ n : ℕ,
      scaleConvolutionPower (W 0) (n + 1) 0 = 0 := by
    intro n
    change (∫ s in Set.Ioc (0 : ℝ) 0, W 0 s *
      scaleConvolutionPower (W 0) n (0 - s) ∂volume) = 0
    simp
  have hsingle :
      (∑' n : ℕ, (q : ℂ) ^ n *
          ((scaleConvolutionPower (W 0) n 0 : ℝ) : ℂ)) =
      (q : ℂ) ^ 0 * ((scaleConvolutionPower (W 0) 0 0 : ℝ) : ℂ) := by
    apply tsum_eq_single 0
    intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [hzero n]
  rw [hsingle]
  simpa only [pow_zero, one_mul, scaleConvolutionPower] using
    congrArg (fun t : ℝ => (t : ℂ))
      (source_scale_origin_discount_invariant ψ W hW q hq)
