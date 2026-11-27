import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_four_iff

theorem solution (n : ℕ) : IsGapSemiprime 4 n ↔ IsCousinSemiprime n := by
  constructor <;> rintro ⟨p, hp, hq, rfl⟩ <;> exact ⟨p, hp, hq, rfl⟩
