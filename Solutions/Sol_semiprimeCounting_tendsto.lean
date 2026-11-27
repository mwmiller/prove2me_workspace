import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_semiprimeCounting_tendsto
import Theorems.Thm_semiprimeCounting_half_primeCounting

theorem solution :
    Filter.Tendsto semiprimeCounting Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun n => semiprimeCounting_half_primeCounting n) ?_
  rw [Filter.tendsto_atTop]
  intro b
  have h := Filter.tendsto_atTop.mp Nat.tendsto_primeCounting b
  rw [Filter.eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  rw [Filter.eventually_atTop]
  exact ⟨2 * a, fun n hn => ha _ (by omega)⟩
