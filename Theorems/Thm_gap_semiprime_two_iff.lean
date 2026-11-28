import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Gap 2 is exactly the Edenic semiprime

Published as `gap_semiprime_two_iff` (prove2.me, theorem id
`bd23775b-e91f-4fba-8bc3-1e48635d3a47`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_two_iff.lean`. -/

theorem gap_semiprime_two_iff (n : ℕ) : IsGapSemiprime 2 n ↔ IsEdenicSemiprime n := by
  constructor <;> rintro ⟨p, hp, hq, rfl⟩ <;> exact ⟨p, hp, hq, rfl⟩
