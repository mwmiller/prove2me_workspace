import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Definitions.Def_IsGapSemiprime
import Definitions.Def_IsCousinSemiprime
import Definitions.Def_semiprimeCounting
import Theorems.Thm_gap_semiprime_no_primitive_root

theorem solution (k n : ℕ) (hk : k % 2 = 0) (hk0 : 0 < k)
    (h : IsGapSemiprime k n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) := by
  obtain ⟨p, hp, hq, rfl⟩ := h
  rintro ⟨g, hg⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hpe : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · rw [h2] at hq
      have hk2 : (2 + k) % 2 = 0 := by omega
      rcases hq.eq_two_or_odd with h2' | hodd'
      · omega
      · omega
    · exact hodd
  have hn2 : (p * (p + k)) % 2 = 1 := by
    simp [Nat.mul_mod, hpe, show (p + k) % 2 = 1 from by omega]
  have hp3 : 3 ≤ p := by omega
  have hkk : 2 ≤ k := by omega
  have hbig : 15 ≤ p * (p + k) := by nlinarith [hp3, hkk]
  have hn0 : 0 < p * (p + k) := mul_pos hp.pos (by omega)
  have hm : 0 < Nat.totient (p * (p + k)) := Nat.totient_pos.mpr hn0
  have hm1 : 1 ≤ Nat.totient (p * (p + k)) := Nat.one_le_of_lt hm
  let u : (ZMod (p * (p + k)))ˣ :=
    ⟨g, g ^ (Nat.totient (p * (p + k)) - 1),
      by rw [← pow_succ', Nat.sub_add_cancel hm1]
         exact (hg.pow_eq_one_iff_dvd _).mpr (dvd_refl _),
      by rw [← pow_succ, Nat.sub_add_cancel hm1]
         exact (hg.pow_eq_one_iff_dvd _).mpr (dvd_refl _)⟩
  have horder : orderOf u = Nat.totient (p * (p + k)) := by
    apply (orderOf_eq_iff hm).2
    refine ⟨?_, ?_⟩
    · apply Units.val_injective
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      exact (hg.pow_eq_one_iff_dvd _).mpr (dvd_refl _)
    · intro l hl h0 hne
      have hg1 : g ^ l = 1 := by
        have h := congrArg Units.val hne
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h
        exact h
      have hmdvd : Nat.totient (p * (p + k)) ∣ l := (hg.pow_eq_one_iff_dvd l).mp hg1
      have hle : Nat.totient (p * (p + k)) ≤ l := Nat.le_of_dvd h0 hmdvd
      omega
  have hz : NeZero (p * (p + k)) := ⟨fun h => by nlinarith [hp2, Nat.zero_le k]⟩
  have hcard : Nat.card (ZMod (p * (p + k)))ˣ = Nat.totient (p * (p + k)) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcyc : IsCyclic (ZMod (p * (p + k)))ˣ :=
    isCyclic_of_orderOf_eq_card u (horder.trans hcard.symm)
  rcases (ZMod.isCyclic_units_iff (p * (p + k))).mp hcyc with h0 | h1 | h2 | h3 | hex
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · obtain ⟨p', m', hp', -, hm', he⟩ := hex
    rcases he with h5 | h6
    · rcases (by omega : m' = 1 ∨ 2 ≤ m') with hm1' | hm2
      · rw [hm1', Nat.pow_one] at h5
        have hpk1 : p + k ≠ 1 := by omega
        exact absurd (by rw [h5]; exact hp') (Nat.not_prime_mul hp.ne_one hpk1)
      · have hpp : p ∣ p' ^ m' := by rw [← h5]; exact dvd_mul_right p (p + k)
        have hp'p : p ∣ p' := Nat.Prime.dvd_of_dvd_pow hp hpp
        have hp'e : p = p' := by
          rcases (Nat.dvd_prime hp').mp hp'p with h1' | h2'
          · exact absurd h1' hp.ne_one
          · exact h2'
        have hpk : (p + k) ∣ p' ^ m' := by rw [← h5]; exact dvd_mul_left (p + k) p
        have hpke : p + k = p' := by
          have h := Nat.Prime.dvd_of_dvd_pow hq hpk
          rcases (Nat.dvd_prime hp').mp h with h1' | h2'
          · omega
          · exact h2'
        omega
    · rw [h6] at hn2
      omega
