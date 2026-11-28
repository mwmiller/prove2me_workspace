import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting

theorem solution (m n : ℕ) (hm : IsCousinSemiprime m)
    (hn : IsCousinSemiprime n) (hmn : m ≠ n) :
    m.Coprime n ∨ {m, n} = ({21, 77} : Finset ℕ) := by
  by_cases hc : m.Coprime n
  · exact Or.inl hc
  · right
    obtain ⟨p, hp, hq, rfl⟩ := hm
    obtain ⟨q, hqp, hqq, rfl⟩ := hn
    obtain ⟨r, hr, hrm, hrn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hrp : r = p ∨ r = p + 4 := by
      rw [Nat.Prime.dvd_mul hr] at hrm
      rcases hrm with h | h
      · rcases (Nat.dvd_prime hp).mp h with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inl h2
      · rcases (Nat.dvd_prime hq).mp h with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inr h2
    have hrq : r = q ∨ r = q + 4 := by
      rw [Nat.Prime.dvd_mul hr] at hrn
      rcases hrn with h | h
      · rcases (Nat.dvd_prime hqp).mp h with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inl h2
      · rcases (Nat.dvd_prime hqq).mp h with h1 | h2
        · exact absurd h1 hr.ne_one
        · exact Or.inr h2
    rcases hrp with h1 | h2
    · subst h1
      rcases hrq with h3 | h4
      · subst h3
        exact absurd rfl hmn
      · subst h4
        have h3 : q % 3 = 0 ∨ (q + 4) % 3 = 0 ∨ (q + 4 + 4) % 3 = 0 := by omega
        rcases h3 with h3 | h3 | h3
        · have hd : 3 ∣ q := Nat.dvd_of_mod_eq_zero h3
          rcases hqp.eq_one_or_self_of_dvd 3 hd with h5 | h6
          · omega
          · subst h6
            decide
        · have hd : 3 ∣ q + 4 := Nat.dvd_of_mod_eq_zero h3
          rcases hp.eq_one_or_self_of_dvd 3 hd with h5 | h6
          · omega
          · omega
        · have hd : 3 ∣ q + 4 + 4 := Nat.dvd_of_mod_eq_zero h3
          rcases hq.eq_one_or_self_of_dvd 3 hd with h5 | h6
          · omega
          · omega
    · subst h2
      rcases hrq with h3 | h4
      · subst h3
        have h5 : p % 3 = 0 ∨ (p + 4) % 3 = 0 ∨ (p + 4 + 4) % 3 = 0 := by omega
        rcases h5 with h5 | h5 | h5
        · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h5
          rcases hp.eq_one_or_self_of_dvd 3 hd with h6 | h7
          · omega
          · subst h7
            decide
        · have hd : 3 ∣ p + 4 := Nat.dvd_of_mod_eq_zero h5
          rcases hq.eq_one_or_self_of_dvd 3 hd with h6 | h7
          · omega
          · omega
        · have hd : 3 ∣ p + 4 + 4 := Nat.dvd_of_mod_eq_zero h5
          rcases hqq.eq_one_or_self_of_dvd 3 hd with h6 | h7
          · omega
          · omega
      · have hpq : p = q := by omega
        subst hpq
        exact absurd rfl hmn
