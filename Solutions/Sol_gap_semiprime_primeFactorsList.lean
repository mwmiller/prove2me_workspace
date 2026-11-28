import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (hk : k ≠ 0)
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
