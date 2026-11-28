import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # A gap semiprime is squarefree

Published as `gap_semiprime_squarefree` (prove2.me, theorem id
`d7837ed6-ba45-43ce-a124-d9d263036f7a`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_squarefree.lean`. -/

theorem gap_semiprime_squarefree (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    Squarefree n := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  exact (Nat.squarefree_mul hc).mpr ⟨hp.squarefree, hq.squarefree⟩

/-! # Family A: gap-generalized umbrella (A10–A18) -/
