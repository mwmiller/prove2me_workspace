import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

/-! # Euler's totient of a gap semiprime

Published as `gap_semiprime_totient` (prove2.me, theorem id
`ab12609a-2ccd-5525-89ef-96b13bdff569`). Statement and proof mirrored from the
accepted submission; the submitted solution file is
`Solutions/Sol_gap_semiprime_totient.lean`. -/

theorem gap_semiprime_totient (k n : ℕ) (hk : k ≠ 0) (h : IsGapSemiprime k n) :
    ∃ p, p.Prime ∧ (p + k).Prime ∧ n = p * (p + k) ∧
      n.totient = (p - 1) * (p + k - 1) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  refine ⟨p, hp, hq, rfl, ?_⟩
  have hc : p.Coprime (p + k) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => by
      rcases (Nat.dvd_prime hq).mp hd with h1 | h2
      · exact absurd h1 hp.ne_one
      · exact absurd (by omega) hk
  rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.totient_prime hq]
