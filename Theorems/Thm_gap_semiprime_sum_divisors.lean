import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The sum-of-divisors of a gap semiprime

Published as `gap_semiprime_sum_divisors` (prove2.me, theorem id
`c93ab500-1e4b-41ef-af4c-5b86be2d57e4`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_sum_divisors.lean`. -/

theorem gap_semiprime_sum_divisors (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      ∑ d ∈ n.divisors, d = (p + 1) * (p + k + 1) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  refine ⟨p, hp, hq, rfl, ?_⟩
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  rw [Nat.Coprime.sum_divisors_mul hc, Nat.Prime.divisors hp, Nat.Prime.divisors hq,
    Finset.sum_pair hp.ne_one.symm, Finset.sum_pair hq.ne_one.symm]
  ring
