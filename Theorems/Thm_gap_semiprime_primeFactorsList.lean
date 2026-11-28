import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # The prime factor list of a gap semiprime

Published as `gap_semiprime_primeFactorsList` (prove2.me, theorem id
`b1c550c0-a711-4e3d-8bd7-06a588bedb9d`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_primeFactorsList.lean`. -/

theorem gap_semiprime_primeFactorsList (k n : ℕ) (hk : k ≠ 0)
    (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.primeFactorsList = [p, p + k] := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  refine ⟨p, hp, hq, rfl, ?_⟩
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  have hperm : List.Perm (p * (p + k)).primeFactorsList
      (p.primeFactorsList ++ (p + k).primeFactorsList) :=
    Nat.perm_primeFactorsList_mul_of_coprime hc
  rw [Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq] at hperm
  simp only [List.cons_append, List.nil_append] at hperm
  exact List.Perm.eq_of_sortedLE (Nat.primeFactorsList_sorted _)
    (by simp [List.sortedLE_iff_pairwise]) hperm
