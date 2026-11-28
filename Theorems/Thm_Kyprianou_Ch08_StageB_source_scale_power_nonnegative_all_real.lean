import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone

set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08.StageB

-- Proof mirrored from accepted submission bb6ae61b-8a4e-4a37-baba-4a07422cc890 (by WillR).
theorem Kyprianou.Ch08.StageB.source_scale_power_nonnegative_all_real (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) :
    ∀ (n : ℕ) (x : ℝ),
      0 ≤ scaleConvolutionPower (W 0) n x := by
  have hpos := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).1
  intro n
  induction n with
  | zero =>
      intro x
      simpa only [scaleConvolutionPower] using hpos x
  | succ n ih =>
      intro x
      change 0 ≤ ∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * scaleConvolutionPower (W 0) n (x - s) ∂volume
      apply integral_nonneg_of_ae
      filter_upwards [] with s
      exact mul_nonneg (hpos s) (ih (x - s))
