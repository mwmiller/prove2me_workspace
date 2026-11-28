import Mathlib.Analysis.Convolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A causal time-reversal substitution turns the interval integral into
positive-time convolution, with no integrability hypotheses. -/
-- Proof mirrored from accepted submission 492cd90c-295b-47fb-af29-deb12b2b7376 (by WillR).
theorem AvramDividend.Classical.positive_causal_integral_eq_posConvolution (f g : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
      MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  have hreverse :
      (∫ s in (0 : ℝ)..x, f (x - s) * g s ∂volume) =
      (∫ t in (0 : ℝ)..x, f t * g (x - t) ∂volume) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ => f t * g (x - t)) (d := x)
      (a := (0 : ℝ)) (b := x)
    simpa only [sub_self, sub_zero, sub_sub_cancel] using h
  rw [← intervalIntegral.integral_of_le (le_of_lt hx), hreverse]
  change (∫ t in (0 : ℝ)..x, f t * g (x - t) ∂volume) =
    (Ioi (0 : ℝ)).indicator
      (fun z => ∫ t in (0 : ℝ)..z, f t * g (z - t) ∂volume) x
  exact (Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)
    (fun z : ℝ => ∫ t in (0 : ℝ)..z, f t * g (z - t) ∂volume)).symm
