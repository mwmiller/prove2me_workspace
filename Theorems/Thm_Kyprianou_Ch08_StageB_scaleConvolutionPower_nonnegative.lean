import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Order.Interval.Set.Defs

set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB Set

-- Proof mirrored from accepted submission 00eda309-85d5-4ea5-af4f-ec44aba54fd8 (by WillR).
theorem Kyprianou.Ch08.StageB.scaleConvolutionPower_nonnegative (W : ℝ → ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ scaleConvolutionPower W n x := by
  induction n generalizing x with
  | zero => simpa only [scaleConvolutionPower] using hW x hx
  | succ n ih =>
    change 0 ≤ ∫ s in Set.Ioc (0 : ℝ) x,
      W s * scaleConvolutionPower W n (x - s) ∂volume
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (hW s hs.1.le)
      (ih (x - s) (sub_nonneg.mpr hs.2))
