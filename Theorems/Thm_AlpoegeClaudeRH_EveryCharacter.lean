import Mathlib
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter_below_record

namespace AlpoegeClaudeRH

theorem EveryCharacter : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro N _ χ s hs h
  by_cases hrec : (0.8749570698 : ℝ) < s.re
  · -- Above the boundary: the audited uniform zero-free record.
    exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ hrec (by tauto)
  · -- At or below the boundary: the remaining open child.
    exact AlpoegeClaudeRH.EveryCharacter_below_record N χ s hs h (le_of_not_gt hrec)

end AlpoegeClaudeRH
