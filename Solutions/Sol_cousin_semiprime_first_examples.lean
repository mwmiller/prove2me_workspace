import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution :
    IsCousinSemiprime 21 ∧ IsCousinSemiprime 77 ∧
      IsCousinSemiprime 221 ∧ IsCousinSemiprime 437 := by
  refine ⟨⟨3, by norm_num, by norm_num, by norm_num⟩,
    ⟨7, by norm_num, by norm_num, by norm_num⟩,
    ⟨13, by norm_num, by norm_num, by norm_num⟩,
    ⟨19, by norm_num, by norm_num, by norm_num⟩⟩
