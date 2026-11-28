import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_scaleConvolutionPower_factorial_majorant_step

set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

-- Proof mirrored from accepted submission 6c4c05a5-5307-431b-942a-3c511cabf961 (by WillR).
theorem Kyprianou.Ch08.StageB.scaleConvolutionPower_factorial_majorant (W : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Set.Ici (0 : ℝ)))
    (hconv : ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      IntegrableOn (fun s : ℝ => W s * scaleConvolutionPower W n (x - s))
        (Set.Ioc (0 : ℝ) x) volume)
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    scaleConvolutionPower W n x ≤
      (x ^ n / (Nat.factorial n : ℝ)) * (W x) ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
    simp only [scaleConvolutionPower, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, zero_add, pow_one]
    exact le_rfl
  | succ n ih =>
    exact scaleConvolutionPower_factorial_majorant_step W hpos hmono n x hx
      (hconv n x hx) (fun y hy => ih y hy)
