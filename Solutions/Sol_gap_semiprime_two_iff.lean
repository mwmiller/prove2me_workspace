import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (n : ℕ) : IsGapSemiprime 2 n ↔ IsEdenicSemiprime n := by
  constructor <;> rintro ⟨p, hp, hq, rfl⟩ <;> exact ⟨p, hp, hq, rfl⟩
