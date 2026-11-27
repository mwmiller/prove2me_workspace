import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The semiprime counting function tends to infinity

Published as `semiprimeCounting_tendsto` (prove2.me, theorem id
`1a1ad0f6-aa2c-4471-a798-f27e00f07c0d`). Statement skeleton; the proof
lives in `Solutions/Sol_semiprimeCounting_tendsto.lean`. -/

theorem semiprimeCounting_tendsto :
    Filter.Tendsto semiprimeCounting Filter.atTop Filter.atTop := by
  sorry
