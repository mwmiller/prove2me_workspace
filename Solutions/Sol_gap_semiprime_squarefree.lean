import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    Squarefree n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  exact (Nat.squarefree_mul hc).mpr ⟨hp.squarefree, hq.squarefree⟩

/-! # Family A: gap-generalized umbrella (A10–A18) -/
