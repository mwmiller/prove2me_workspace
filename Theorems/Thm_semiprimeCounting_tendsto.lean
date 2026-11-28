import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_semiprimeCounting_half_primeCounting

/-! # The semiprime counting function tends to infinity

Published as `semiprimeCounting_tendsto` (prove2.me, theorem id
`1a1ad0f6-aa2c-4471-a798-f27e00f07c0d`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_semiprimeCounting_tendsto.lean`. -/

theorem semiprimeCounting_tendsto :
    Filter.Tendsto semiprimeCounting Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun n => semiprimeCounting_half_primeCounting n) ?_
  rw [Filter.tendsto_atTop]
  intro b
  have h := Filter.tendsto_atTop.mp Nat.tendsto_primeCounting b
  rw [Filter.eventually_atTop] at h
  obtain ⟨a, ha⟩ := h
  rw [Filter.eventually_atTop]
  exact ⟨2 * a, fun n hn => ha _ (by omega)⟩
