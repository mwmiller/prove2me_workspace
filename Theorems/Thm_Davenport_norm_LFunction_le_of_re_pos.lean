import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset DirichletCharacter

namespace DLFB

open MeasureTheory Set Complex Filter Topology Asymptotics

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
private noncomputable def G (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-- Reindexing a sum over `range q` as a sum over `ZMod q`. -/
private lemma sum_range_eq_sum_zmod (f : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, f (j : ZMod q) = ∑ a : ZMod q, f a := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro a _; rfl

/-- A complete block of `q` consecutive values of a non-principal character sums to zero. -/
private lemma sum_block_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q) = 0 := by
  calc ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q)
      = ∑ j ∈ Finset.range q, (fun a : ZMod q => χ ((m : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((m : ZMod q) + a) :=
        sum_range_eq_sum_zmod (fun a : ZMod q => χ ((m : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a :=
        Fintype.sum_equiv (Equiv.addLeft ((m : ZMod q))) _ _ (fun a => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- `‖∑_{k < n} χ(k)‖ ≤ q`. -/
private lemma norm_sum_range_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n q with hn | hn
    · calc ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖
          ≤ ∑ k ∈ Finset.range n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
        _ = n := by simp
        _ ≤ q := by exact_mod_cast hn
    · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      set m := n - q with hm
      have hmn : m < n := by omega
      have hnm : n = m + q := by omega
      have hsplit : ∑ k ∈ Finset.range m, χ (k : ZMod q)
          + ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = ∑ k ∈ Finset.range n, χ (k : ZMod q) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmn.le
      have hzero : ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : n - m = q := by omega
        rw [this]
        exact sum_block_eq_zero χ hχ m
      rw [← hsplit, hzero, add_zero]
      exact ih m hmn

/-- `‖G χ t‖ ≤ q` for a non-principal character. -/
private lemma norm_G_le_q (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) (t : ℝ) :
    ‖G χ t‖ ≤ q := by
  have hnt : Nontrivial (ZMod q) := by
    haveI : Fact (1 < q) := ⟨by omega⟩
    infer_instance
  have hz : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  have : G χ t = ∑ k ∈ Finset.range (⌊t⌋₊ + 1), χ (k : ZMod q) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have : x = 0 := by omega
      subst this
      simpa using hz
  rw [this]
  exact norm_sum_range_le χ hχ _

omit [NeZero q] in
/-- `‖G χ t‖ ≤ t` for `0 ≤ t`. -/
private lemma norm_G_le_self (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t) :
    ‖G χ t‖ ≤ t := by
  calc ‖G χ t‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = (⌊t⌋₊ : ℝ) := by simp
    _ ≤ t := Nat.floor_le ht

omit [NeZero q] in
/-- `G χ` vanishes below `1`. -/
private lemma G_eq_zero (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) : G χ t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [G, this]

/-! ### The Mellin representation -/

omit [NeZero q] in
private lemma locallyIntegrable_G (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (G χ) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => (χ k : ℂ)) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

private lemma isBigO_G_top (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) :
    (G χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_G_le_q χ hχ hq t

omit [NeZero q] in
private lemma isBigO_G_bot (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (G χ) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [G_eq_zero χ ht.2]

private lemma mellinConv_G (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (G χ) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G χ) (isBigO_G_top χ hχ hq) ?_ (isBigO_G_bot χ _) ?_
  · simpa using hs
  · simp

private lemma mellin_hasDeriv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • G χ t) (-s) ∧
      HasDerivAt (mellin (G χ)) (mellin (fun t => Real.log t • G χ t) (-s)) (-s) := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G χ) (isBigO_G_top χ hχ hq) ?_ (isBigO_G_bot χ _) ?_
  · simpa using hs
  · simp

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
private noncomputable def F (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G χ) (-s)

private lemma hasDerivAt_F (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (F χ)
      (mellin (G χ) (-s) - s * mellin (fun t => Real.log t • G χ t) (-s)) s := by
  have h := (mellin_hasDeriv χ hχ hq hs).2
  have h2 : HasDerivAt (fun z : ℂ => mellin (G χ) (-z))
      (mellin (fun t => Real.log t • G χ t) (-s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).neg)
  have h4 := (hasDerivAt_id s).mul h2
  have heq : (1 : ℂ) * mellin (G χ) (-s)
      + s * (mellin (fun t => Real.log t • G χ t) (-s) * (-1))
      = mellin (G χ) (-s) - s * mellin (fun t => Real.log t • G χ t) (-s) := by ring
  simp only [id] at h4
  rw [heq] at h4
  exact h4

omit [NeZero q] in
/-- Restricting a Mellin integral to `Ioi 1`, using that `G χ` vanishes below `1`. -/
private lemma mellin_eq_integral_Ioi_one (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : MellinConvergent (G χ) s) :
    mellin (G χ) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by
  have hz : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G χ t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    rw [G_eq_zero χ ht.2, smul_zero]
  calc mellin (G χ) s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := rfl
    _ = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G χ t)
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
        exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one))
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by rw [hz, zero_add]

private lemma LFunction_eq_F (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = F χ s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun n => ?_))
    simp only [Real.rpow_zero, norm_one, mul_one]
    have : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) = G χ (n : ℝ) := by
      simp [G, Nat.floor_natCast]
    rw [this]
    exact norm_G_le_q χ hχ hq _
  have hmain := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ)) (r := 0) le_rfl
    (by linarith : (0 : ℝ) < s.re) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hmain]
  have hconv : MellinConvergent (G χ) (-s) := mellinConv_G χ hχ hq (by linarith)
  rw [F, mellin_eq_integral_Ioi_one χ hconv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, G]
  rw [mul_comm]
  congr 2
  ring

/-! ### Analytic continuation via the identity theorem -/

private lemma LFunction_eq_F_of_re_pos (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = F χ s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hFan : AnalyticOnNhd ℂ (F χ) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((hasDerivAt_F χ hχ hq hz).differentiableAt).differentiableWithinAt
  have hmem : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] F χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_F χ hχ hq hz
  have heqOn : EqOn (DirichletCharacter.LFunction χ) (F χ) U :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hFan hUconn hmem hev
  exact heqOn (show s ∈ U from hs)

/-! ### Bounding the Mellin integral -/

private lemma norm_mellin_le (f : ℝ → ℂ) (x : ℂ) :
    ‖mellin f x‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (x.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private lemma integral_Ioi_one_split {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi (0 : ℝ))) :
    ∫ t in Ioi (0 : ℝ), w t = (∫ t in Ioc (0 : ℝ) 1, w t) + ∫ t in Ioi (1 : ℝ), w t := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hw.mono_set Ioc_subset_Ioi_self) (hw.mono_set (Ioi_subset_Ioi zero_le_one))

/-- The main estimate: `‖∫₁^∞ t^{-s-1} G(t) dt‖ ≤ q / Re s`. -/
private lemma norm_mellin_G_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : ‖mellin (G χ) (-s)‖ ≤ (q : ℝ) / s.re := by
  have hlt : (-s.re - 1 : ℝ) < -1 := by linarith
  set u : ℝ → ℝ := fun t => t ^ (-s.re - 1) * ‖G χ t‖ with hu
  have hconv : MellinConvergent (G χ) (-s) := mellinConv_G χ hχ hq hs
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hstep1 : ‖mellin (G χ) (-s)‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    have := norm_mellin_le (G χ) (-s)
    simpa [hu] using this
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, u t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hu, G_eq_zero χ ht.2]
  have hp2 : ∫ t in Ioi (1 : ℝ), u t ≤ (q : ℝ) / s.re := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hlt one_pos).const_mul _
    have hstep : ∫ t in Ioi (1 : ℝ), u t ≤ ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
      refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi zero_le_one)) hmaj
        measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hG : ‖G χ t‖ ≤ (q : ℝ) := norm_G_le_q χ hχ hq t
      calc u t ≤ t ^ (-s.re - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
        _ = (q : ℝ) * t ^ (-s.re - 1) := by ring
    have hval : ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt one_pos,
        show (-s.re - 1 + 1 : ℝ) = -s.re by ring, Real.one_rpow, neg_div_neg_eq, mul_one_div]
    rw [hval] at hstep
    exact hstep
  rw [integral_Ioi_one_split hIA, hp1, zero_add] at hstep1
  linarith

end DLFB

/-- **Davenport, §14.** For a non-principal Dirichlet character `χ` mod `q` and `Re s > 0`,
`‖L(s, χ)‖ ≤ ‖s‖ q / Re s`. -/
-- Proof mirrored from accepted submission 3cec706b-5321-4874-aded-0c8db602850c (by alya).
theorem Davenport.norm_LFunction_le_of_re_pos (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * q / s.re := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hq2 : 2 ≤ q := by omega
  rw [DLFB.LFunction_eq_F_of_re_pos χ hχ hq2 hs, DLFB.F, norm_mul]
  calc ‖s‖ * ‖mellin (DLFB.G χ) (-s)‖ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
        mul_le_mul_of_nonneg_left (DLFB.norm_mellin_G_le χ hχ hq2 hs) (norm_nonneg s)
    _ = ‖s‖ * q / s.re := by ring

