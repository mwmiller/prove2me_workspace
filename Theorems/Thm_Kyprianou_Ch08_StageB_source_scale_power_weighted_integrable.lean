import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_weighted_integrable

set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

-- Proof mirrored from accepted submission fe8f70f3-be59-4749-b6a6-f1f6deeb2f08 (by WillR).
theorem Kyprianou.Ch08.StageB.source_scale_power_weighted_integrable (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (β : ℝ)
    (hβ : 0 ≤ β) (hroot : Phi ψ 0 < β) :
    ∀ n : ℕ, IntegrableOn (fun t : ℝ =>
      Real.exp (-β * t) * scaleConvolutionPower (W 0) n t)
      (Set.Ioi (0 : ℝ)) volume := by
  have hscale := hW 0 (le_refl (0 : ℝ))
  have hκ : IntegrableOn (fun t : ℝ => Real.exp (-β * t) * W 0 t)
      (Set.Ioi (0 : ℝ)) volume :=
    (hscale.2.2.2.2.2 β hβ hroot).1
  have hresult := AvramDividend.Classical.causal_convolution_powers_weighted_integrable
    (W 0) (scaleConvolutionPower (W 0)) β (by simpa only [neg_mul] using hκ) rfl (fun n => rfl)
  intro n
  simpa only [neg_mul] using hresult n
