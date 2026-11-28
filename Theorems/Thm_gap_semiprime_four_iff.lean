import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Gap 4 is exactly the cousin semiprime

Published as `gap_semiprime_four_iff` (prove2.me, theorem id
`ea45918c-e7e8-5eeb-a521-37827e2d760f`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_four_iff.lean`. -/

theorem gap_semiprime_four_iff (n : ℕ) : IsGapSemiprime 4 n ↔ IsCousinSemiprime n := by
  constructor <;> rintro ⟨p, hp, hq, rfl⟩ <;> exact ⟨p, hp, hq, rfl⟩
