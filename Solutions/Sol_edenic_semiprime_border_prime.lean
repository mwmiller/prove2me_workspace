import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_border_prime

theorem solution (n q : ℕ) (h : IsEdenicSemiprime n)
    (hq : q.Prime) (hdvd : q ∣ n) :
    n = q * (q + 2) ∨ n = (q - 2) * q := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h1 | h1
  · have hpq : p = q := (Nat.Prime.dvd_iff_eq hp hq.ne_one).mp h1
    refine Or.inl ?_
    rw [hpq]
  · have hq2 : p + 2 = q := (Nat.Prime.dvd_iff_eq hp2 hq.ne_one).mp h1
    have hpq : p = q - 2 := by omega
    refine Or.inr ?_
    rw [hq2, hpq]
