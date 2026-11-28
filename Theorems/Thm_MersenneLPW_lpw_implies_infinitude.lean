import Mathlib
import Definitions.Def_MersenneLPW_mersenneExponentCount

namespace MersenneLPW

-- Proof mirrored from earliest accepted submission 39f022fa-f207-4114-be39-2d5d4909c70f (by garyholm).
theorem lpw_implies_infinitude :
    Asymptotics.IsEquivalent Filter.atTop
        (fun y => (mersenneExponentCount y : ℝ))
        (fun y => Real.exp Real.eulerMascheroniConstant * Real.logb 2 y) →
      {p : ℕ | (mersenne p).Prime}.Infinite := by
  intro h
  intro hfin
  have hv : Filter.Tendsto (fun y : ℕ => Real.exp Real.eulerMascheroniConstant * Real.logb 2 (y : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (Real.exp_pos _)
      ((Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).comp tendsto_natCast_atTop_atTop)
  have hu := h.symm.tendsto_atTop hv
  have hb : ∀ y : ℕ, (mersenneExponentCount y : ℝ) ≤ hfin.toFinset.card := by
    intro y
    have : mersenneExponentCount y ≤ hfin.toFinset.card := by
      unfold mersenneExponentCount
      rw [Nat.count_eq_card_filter_range]
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter] at hp
      simpa using hp.2
    exact_mod_cast this
  obtain ⟨y, hy⟩ := (hu.eventually_gt_atTop (hfin.toFinset.card : ℝ)).exists
  linarith [hb y]

end MersenneLPW
