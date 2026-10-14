/-
  Reencounters/SquareCase.lean — the case n = 2, solved completely.

  These results accompany the note Translations in the Quotient by the n-th Power Remainder.

  For n = 2 the representations of Δ = h² − k² as a difference of squares are the
  factorisations Δ = d·e with d ≤ e of equal parity. Consequences proved here:
  * chapters k < h reencounter in a later chapter iff h − k ≥ 3 (the distances 1 and 2
    separate permanently);
  * the last chapter of reencounter is explicit;
  * the adjacent pair (k, k+1) met in an earlier chapter iff 2k+1 = p·q with 1 < p < q.
-/

import Reencounters.Dictionary

namespace Reencounters

open CampiOperazionistici

/-- Gap of a square chapter is the odd number `2k+1`. -/
lemma gap_two (k : ℕ) : gap 2 k = 2 * k + 1 := by
  simp only [gap]
  have hle : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ k) 2
  zify [hle]
  ring

/-- Product of two even naturals is divisible by 4. -/
lemma four_dvd_of_even_mul_even {d e : ℕ} (hd : Even d) (he : Even e) : 4 ∣ d * e := by
  obtain ⟨a, rfl⟩ := hd
  obtain ⟨b, rfl⟩ := he
  exact ⟨a * b, by ring⟩

/-- Difference of squares factors as `(h-k)(h+k)`. -/
lemma sq_diff_eq_mul (k h : ℕ) (hkh : k ≤ h) :
    h ^ 2 - k ^ 2 = (h - k) * (h + k) := by
  have hkle : k ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left hkh 2
  zify [hkh, hkle]
  ring

/-- Cast of `2k = e - d` into ℤ. -/
lemma two_mul_k_int (k d e : ℕ) (hde : d ≤ e) (hk : 2 * k = e - d) :
    (2 : ℤ) * k = (e : ℤ) - d := by
  have : (2 : ℤ) * k = ↑(e - d) := by exact_mod_cast hk
  rwa [Int.natCast_sub hde] at this

/-- From equal-parity factors `d ≤ e` with `2k = e - d`, recover a difference of squares. -/
lemma exists_h_of_equal_parity (d e k : ℕ) (hde : d ≤ e) (hp : d % 2 = e % 2)
    (hk : 2 * k = e - d) :
    ∃ h : ℕ, k ^ 2 + d * e = h ^ 2 := by
  set h := (e + d) / 2
  refine ⟨h, ?_⟩
  have h2h : 2 * h = e + d := by
    have : (e + d) % 2 = 0 := by omega
    have := Nat.div_add_mod (e + d) 2
    omega
  have Hh : (2 : ℤ) * h = (e : ℤ) + d := by exact_mod_cast h2h
  have Hk : (2 : ℤ) * k = (e : ℤ) - d := two_mul_k_int k d e hde hk
  have hident : (h : ℤ) ^ 2 - (k : ℤ) ^ 2 = (d : ℤ) * e := by nlinarith
  have hk_leZ : (k : ℤ) ^ 2 ≤ (h : ℤ) ^ 2 := by
    have : (0 : ℤ) ≤ (d : ℤ) * e := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hk_le : k ^ 2 ≤ h ^ 2 := mod_cast hk_leZ
  zify [hk_le]
  linarith

/-- If `a * b = c * d` with `0 < c ≤ a`, then `b ≤ d`. -/
lemma le_of_mul_eq_mul_of_le {a b c d : ℕ} (hc : 0 < c) (hle : c ≤ a)
    (heq : a * b = c * d) : b ≤ d :=
  Nat.le_of_mul_le_mul_left (heq ▸ Nat.mul_le_mul_right b hle) hc

/-- Representations of a positive `Δ` as `h² − k²` are the factorisations `Δ = d·e`,
`d ≤ e`, of equal parity, with `k = (e − d)/2`. -/
theorem sq_add_eq_sq_iff (k Δ : ℕ) (hΔ : 0 < Δ) :
    (∃ h : ℕ, k ^ 2 + Δ = h ^ 2) ↔
      ∃ d e : ℕ, d * e = Δ ∧ d ≤ e ∧ d % 2 = e % 2 ∧ 2 * k = e - d := by
  constructor
  · intro ⟨h, hh⟩
    have hkh : k < h := by
      by_contra hle
      push_neg at hle
      have : h ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    refine ⟨h - k, h + k, ?_, by omega, by omega, by omega⟩
    have hdiff := sq_diff_eq_mul k h (Nat.le_of_lt hkh)
    omega
  · intro ⟨d, e, hprod, hde, hp, hk⟩
    obtain ⟨h, hh⟩ := exists_h_of_equal_parity d e k hde hp hk
    exact ⟨h, by rwa [hprod] at hh⟩

/-- The factor `d` in a representation is positive. -/
lemma d_pos_of_sq_repr {d e Δ : ℕ} (hprod : d * e = Δ) (hΔ : 0 < Δ) : 0 < d :=
  Nat.pos_of_mul_pos_right (hprod ▸ hΔ)

/-- Larger chapter index corresponds to a strictly smaller factor `d`. -/
lemma d_lt_of_k_lt {k k' d e d' e' Δ : ℕ}
    (hΔ : 0 < Δ) (hprod : d * e = Δ) (hprod' : d' * e' = Δ)
    (hk : 2 * k = e - d) (hk' : 2 * k' = e' - d')
    (hde : d ≤ e) (hde' : d' ≤ e')
    (hlt : k < k') : d' < d := by
  have hdpos : 0 < d := d_pos_of_sq_repr hprod hΔ
  by_contra hge
  push_neg at hge
  have he'le : e' ≤ e :=
    le_of_mul_eq_mul_of_le hdpos hge (by rw [hprod', hprod])
  have Hk := two_mul_k_int k d e hde hk
  have Hk' := two_mul_k_int k' d' e' hde' hk'
  have hleZ : (2 : ℤ) * k' ≤ (2 : ℤ) * k := by
    have : (e' : ℤ) - d' ≤ (e : ℤ) - d := by
      have h1 : (e' : ℤ) ≤ e := mod_cast he'le
      have h2 : (d : ℤ) ≤ d' := mod_cast hge
      linarith
    linarith
  have hk'le : k' ≤ k := by
    have : (k' : ℤ) ≤ k := by linarith
    exact_mod_cast this
  omega

/-- Half of an even natural. -/
lemma two_mul_div_two {n : ℕ} (h : n % 2 = 0) : 2 * (n / 2) = n := by
  have := Nat.div_add_mod n 2
  omega

/-- **Forward reencounter for n = 2.** The chapters `k < h` meet again in a later chapter
`k' > k` iff `h − k ≥ 3`. -/
theorem forward_reencounter_sq_iff (k h : ℕ) (hkh : k < h) :
    (∃ k' h' : ℕ, k < k' ∧ k' ^ 2 + (h ^ 2 - k ^ 2) = h' ^ 2) ↔ 3 ≤ h - k := by
  set Δ := h ^ 2 - k ^ 2
  have hΔpos : 0 < Δ := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hkh (by norm_num))
  have hkle0 : k ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hkh) 2
  have hΔeq : Δ = (h - k) * (h + k) := by
    change h ^ 2 - k ^ 2 = (h - k) * (h + k)
    exact sq_diff_eq_mul k h (Nat.le_of_lt hkh)
  constructor
  · intro ⟨k', h', hk', hh'⟩
    by_contra hlt
    push_neg at hlt
    have hd_small : h - k = 1 ∨ h - k = 2 := by omega
    obtain ⟨d', e', hprod', hde', hp', hk2'⟩ :=
      (sq_add_eq_sq_iff k' Δ hΔpos).mp ⟨h', hh'⟩
    have hprod : (h - k) * (h + k) = Δ := hΔeq.symm
    have hk2 : 2 * k = (h + k) - (h - k) := by omega
    have hd'lt : d' < h - k :=
      d_lt_of_k_lt hΔpos hprod hprod' hk2 hk2' (by omega) hde' hk'
    have hd'pos : 0 < d' := d_pos_of_sq_repr hprod' hΔpos
    rcases hd_small with h1 | h2
    · omega
    · have hd'1 : d' = 1 := by omega
      subst hd'1
      have he'Δ : e' = Δ := by omega
      subst he'Δ
      have hΔeven : Δ % 2 = 0 := by
        rw [hΔeq, h2]; omega
      -- hp' : 1 % 2 = Δ % 2, contradiction
      omega
  · intro h3
    by_cases hodd : Δ % 2 = 1
    · -- odd Δ: take d' = 1, e' = Δ
      set k' := (Δ - 1) / 2
      have hk2' : 2 * k' = Δ - 1 := two_mul_div_two (by omega)
      obtain ⟨h', hh'⟩ :=
        exists_h_of_equal_parity 1 Δ k' (by omega) (by omega) hk2'
      refine ⟨k', h', ?_, by simpa using hh'⟩
      have hge : Δ ≥ 3 * (h + k) := by
        calc Δ = (h - k) * (h + k) := hΔeq
          _ ≥ 3 * (h + k) := Nat.mul_le_mul_right _ h3
      have hhk : h + k ≥ 2 * k + 1 := by omega
      have hge' : 3 * (h + k) ≥ 3 * (2 * k + 1) := Nat.mul_le_mul_left _ hhk
      -- 2k' = Δ-1 ≥ 3(2k+1)-1 = 6k+2 ≥ 2k+2 > 2k
      have : Δ - 1 ≥ 3 * (2 * k + 1) - 1 := by omega
      omega
    · -- even Δ
      push_neg at hodd
      have hdk_even : (h - k) % 2 = 0 := by
        by_contra hoddk
        have hdk_odd : (h - k) % 2 = 1 := by omega
        have hhk_odd : (h + k) % 2 = 1 := by omega
        have : ((h - k) * (h + k)) % 2 = 1 := by
          rw [Nat.mul_mod, hdk_odd, hhk_odd]
        rw [← hΔeq] at this
        omega
      have hdk4 : 4 ≤ h - k := by omega
      have h4 : 4 ∣ Δ := by
        rw [hΔeq]
        exact four_dvd_of_even_mul_even (Nat.even_iff.mpr hdk_even)
          (Nat.even_iff.mpr (by omega))
      set e' := Δ / 2
      have h2dvd : 2 ∣ Δ := dvd_trans (by decide : 2 ∣ 4) h4
      have hprod2 : (2 : ℕ) * e' = Δ := Nat.mul_div_cancel' h2dvd
      have hgeΔ : Δ ≥ 4 * (h + k) := by
        calc Δ = (h - k) * (h + k) := hΔeq
          _ ≥ 4 * (h + k) := Nat.mul_le_mul_right _ hdk4
      have hde' : (2 : ℕ) ≤ e' := by omega
      have hp' : (2 : ℕ) % 2 = e' % 2 := by
        obtain ⟨u, hu⟩ := h4
        have : e' = 2 * u := by
          change Δ / 2 = 2 * u
          omega
        omega
      set k' := (e' - 2) / 2
      have hk2' : 2 * k' = e' - 2 := two_mul_div_two (by omega)
      obtain ⟨h', hh'⟩ := exists_h_of_equal_parity 2 e' k' hde' hp' hk2'
      refine ⟨k', h', ?_, ?_⟩
      · -- k' > k: 2k' = e'-2 ≥ 2(h+k)-2 ≥ 2(k+1+k)-2 = 4k > 2k (need k≥1? or h≥k+4)
        have : e' ≥ 2 * (h + k) := by omega
        omega
      · calc k' ^ 2 + Δ = k' ^ 2 + 2 * e' := by rw [← hprod2]
          _ = h' ^ 2 := hh'

/-- Choose an offset that lands the point `k² + t` in chapter `k'`. -/
lemma offset_to_chapter (k k' t : ℕ) (hk' : k < k') (ht : t < gap 2 k) :
    ∃ m : ℕ, k ^ 2 + t + m = k' ^ 2 := by
  refine ⟨k' ^ 2 - k ^ 2 - t, ?_⟩
  have hkle : k ^ 2 ≤ k' ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hk') 2
  have hgap : gap 2 k ≤ k' ^ 2 - k ^ 2 := by
    rw [gap_two]
    have : (k + 1) ^ 2 ≤ k' ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt hk') 2
    have heq : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
    omega
  omega

/-- The same statement in the quotient: the translated pair `k² + t, h² + t` is equivalent
at some offset landing beyond chapter `k` iff `h − k ≥ 3`. -/
theorem forward_reencounter_sq_iff_aodEquiv (k h t : ℕ) (hkh : k < h) (ht : t < gap 2 k) :
    (∃ m : ℕ, k < irootN 2 (k ^ 2 + t + m) ∧
        radRem 2 (k ^ 2 + t + m) = radRem 2 (h ^ 2 + t + m)) ↔ 3 ≤ h - k := by
  set Δ := h ^ 2 - k ^ 2
  have hΔpos : 0 < Δ := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hkh (by norm_num))
  have hkle : k ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt hkh) 2
  have hΔadd : ∀ m, h ^ 2 + t + m = (k ^ 2 + t + m) + Δ := by
    intro m; omega
  constructor
  · intro ⟨m, hkroot, heq⟩
    have heq' : radRem 2 (k ^ 2 + t + m) = radRem 2 ((k ^ 2 + t + m) + Δ) := by
      rwa [← hΔadd m]
    obtain ⟨h', hh'⟩ := (aodEquiv_add_iff 2 (k ^ 2 + t + m) Δ (by norm_num)).mp heq'
    set k'' := irootN 2 (k ^ 2 + t + m)
    refine (forward_reencounter_sq_iff k h hkh).mp ⟨k'', h', hkroot, ?_⟩
    exact hh'
  · intro h3
    obtain ⟨k', h', hk', hh'⟩ := (forward_reencounter_sq_iff k h hkh).mpr h3
    obtain ⟨m, hm⟩ := offset_to_chapter k k' t hk' ht
    refine ⟨m, ?_, ?_⟩
    · have hiroot : irootN 2 (k' ^ 2) = k' := irootN_perfectPow 2 k' (by norm_num)
      rwa [hm, hiroot]
    · have hiroot : irootN 2 (k ^ 2 + t + m) = k' := by
        rw [hm]; exact irootN_perfectPow 2 k' (by norm_num)
      have : radRem 2 (k ^ 2 + t + m) = radRem 2 ((k ^ 2 + t + m) + Δ) :=
        (aodEquiv_add_iff 2 (k ^ 2 + t + m) Δ (by norm_num)).mpr ⟨h', by
          rwa [hiroot]⟩
      rwa [← hΔadd m] at this

/-- The last chapter of reencounter at distance `Δ` (`Δ` odd, `Δ ≥ 3`): `(Δ − 1)/2`. -/
theorem last_chapter_odd (Δ : ℕ) (hodd : Δ % 2 = 1) (h3 : 3 ≤ Δ) :
    (∃ h : ℕ, ((Δ - 1) / 2) ^ 2 + Δ = h ^ 2) ∧
      ∀ k h : ℕ, k ^ 2 + Δ = h ^ 2 → k ≤ (Δ - 1) / 2 := by
  have hΔpos : 0 < Δ := by omega
  constructor
  · set k := (Δ - 1) / 2
    have hk2 : 2 * k = Δ - 1 := two_mul_div_two (by omega)
    obtain ⟨h, hh⟩ :=
      exists_h_of_equal_parity 1 Δ k (by omega) (by omega) hk2
    exact ⟨h, by simpa using hh⟩
  · intro k h hh
    obtain ⟨d, e, hprod, hde, hp, hk2⟩ := (sq_add_eq_sq_iff k Δ hΔpos).mp ⟨h, hh⟩
    have hdpos : 1 ≤ d := Nat.succ_le_of_lt (d_pos_of_sq_repr hprod hΔpos)
    have he_le : e ≤ Δ := by
      calc e = 1 * e := by ring
        _ ≤ d * e := Nat.mul_le_mul_right _ hdpos
        _ = Δ := hprod
    have hbound : e - d ≤ Δ - 1 := by omega
    have hdiv : 2 * ((Δ - 1) / 2) = Δ - 1 := two_mul_div_two (by omega)
    -- 2k = e - d ≤ Δ - 1 = 2*((Δ-1)/2)
    omega

/-- The last chapter of reencounter at distance `Δ` (`4 ∣ Δ`, `Δ ≥ 8`): `Δ/4 − 1`. -/
theorem last_chapter_even (Δ : ℕ) (h4 : 4 ∣ Δ) (h8 : 8 ≤ Δ) :
    (∃ h : ℕ, (Δ / 4 - 1) ^ 2 + Δ = h ^ 2) ∧
      ∀ k h : ℕ, k ^ 2 + Δ = h ^ 2 → k ≤ Δ / 4 - 1 := by
  have hΔpos : 0 < Δ := by omega
  have h2dvd : 2 ∣ Δ := dvd_trans (by decide : 2 ∣ 4) h4
  obtain ⟨t, ht⟩ := h4
  -- Δ = 4t with t ≥ 2
  have ht2 : 2 ≤ t := by omega
  have hΔ4 : Δ / 4 = t := by omega
  have hΔ2 : Δ / 2 = 2 * t := by omega
  constructor
  · set e := 2 * t
    have hprod : (2 : ℕ) * e = Δ := by omega
    have hde : (2 : ℕ) ≤ e := by omega
    have hp : (2 : ℕ) % 2 = e % 2 := by omega
    set k := t - 1
    have hk2 : 2 * k = e - 2 := by omega
    obtain ⟨h, hh⟩ := exists_h_of_equal_parity 2 e k hde hp hk2
    have hk_eq : k = Δ / 4 - 1 := by omega
    refine ⟨h, ?_⟩
    rw [← hk_eq]
    calc k ^ 2 + Δ = k ^ 2 + 2 * e := by omega
      _ = h ^ 2 := hh
  · intro k h hh
    obtain ⟨d, e, hprod, hde, hp, hk2⟩ := (sq_add_eq_sq_iff k Δ hΔpos).mp ⟨h, hh⟩
    have hdpos : 0 < d := d_pos_of_sq_repr hprod hΔpos
    have hΔeven : Δ % 2 = 0 := by omega
    have hdne1 : d ≠ 1 := by
      intro hd1
      subst hd1
      have : e = Δ := by omega
      subst this
      -- hp : 1 % 2 = Δ % 2
      omega
    have hd2 : 2 ≤ d := by omega
    have he_le : e ≤ Δ / 2 := by
      have : d * e = 2 * (Δ / 2) := by
        rw [hprod, Nat.mul_div_cancel' h2dvd]
      exact le_of_mul_eq_mul_of_le (by norm_num) hd2 this
    have Hk := two_mul_k_int k d e hde hk2
    -- 2k = e - d ≤ Δ/2 - 2 = 2t - 2 = 2(t-1) = 2(Δ/4 - 1)
    have ht1 : 1 ≤ t := by omega
    have hleZ : (2 : ℤ) * k ≤ (2 : ℤ) * ↑(t - 1) := by
      have h1 : (e : ℤ) ≤ ↑(Δ / 2) := mod_cast he_le
      have h2 : (2 : ℤ) ≤ d := mod_cast hd2
      have h3 : (Δ / 2 : ℤ) = 2 * t := by exact_mod_cast hΔ2
      have h5 : (2 : ℤ) * ↑(t - 1) = 2 * t - 2 := by
        rw [Int.natCast_sub ht1]
        ring
      linarith
    have : (k : ℤ) ≤ ↑(t - 1) := by linarith
    have : k ≤ t - 1 := mod_cast this
    omega

/-- **Backward criterion for adjacent chapters (n = 2).** The pair `(k, k+1)` met in an
earlier chapter `0 < k' < k` iff `2k + 1 = p·q` with `1 < p < q`. (Chapter 0 is the single
point 0; including it would add the case `2k + 1 = p²`.) -/
theorem adjacent_backward_sq_iff (k : ℕ) :
    (∃ k' h' : ℕ, 0 < k' ∧ k' < k ∧ k' ^ 2 + (2 * k + 1) = h' ^ 2) ↔
      ∃ p q : ℕ, 1 < p ∧ p < q ∧ p * q = 2 * k + 1 := by
  set Δ := 2 * k + 1
  have hΔpos : 0 < Δ := by omega
  constructor
  · intro ⟨k', h', hk'pos, hk'lt, hh'⟩
    obtain ⟨p, q, hprod, hpq, hp, hk2⟩ :=
      (sq_add_eq_sq_iff k' Δ hΔpos).mp ⟨h', hh'⟩
    refine ⟨p, q, ?_, ?_, hprod⟩
    · -- p > 1: if p = 1 then 2k' = Δ - 1 = 2k so k' = k
      by_contra hp1
      push_neg at hp1
      have hppos : 0 < p := d_pos_of_sq_repr hprod hΔpos
      have hp1' : p = 1 := by omega
      have hq : q = Δ := by rw [hp1'] at hprod; omega
      have hk2' : 2 * k' = Δ - 1 := by rw [hp1', hq] at hk2; exact hk2
      have : 2 * k' = 2 * k := by
        have : Δ - 1 = 2 * k := by omega
        omega
      omega
    · -- p < q from 2k' = q - p and k' > 0
      have : 0 < q - p := by
        have Hk := two_mul_k_int k' p q hpq hk2
        have : (0 : ℤ) < 2 * ↑k' := by
          have : (0 : ℤ) < ↑k' := Nat.cast_pos.mpr hk'pos
          linarith
        have : (0 : ℤ) < ↑q - ↑p := by linarith
        exact_mod_cast this
      omega
  · intro ⟨p, q, hp1, hpq, hprod⟩
    have hodd_prod : (p * q) % 2 = 1 := by rw [hprod]; omega
    have hpq_odd : Odd p ∧ Odd q := Nat.odd_mul.mp (Nat.odd_iff.mpr hodd_prod)
    have hp_odd : p % 2 = 1 := Nat.odd_iff.mp hpq_odd.1
    have hq_odd : q % 2 = 1 := Nat.odd_iff.mp hpq_odd.2
    have hp_par : p % 2 = q % 2 := by omega
    have hpq_le : p ≤ q := Nat.le_of_lt hpq
    have hdiff_even : (q - p) % 2 = 0 := by omega
    set k' := (q - p) / 2
    have hk2 : 2 * k' = q - p := two_mul_div_two hdiff_even
    obtain ⟨h', hh'⟩ := exists_h_of_equal_parity p q k' hpq_le hp_par hk2
    refine ⟨k', h', ?_, ?_, ?_⟩
    · have : 0 < q - p := Nat.sub_pos_of_lt hpq
      omega
    · -- q - p < p*q - 1 = 2k
      have hltZ : (q : ℤ) - ↑p < (p : ℤ) * q - 1 := by
        have : (1 : ℤ) < p := mod_cast hp1
        nlinarith
      have Hk := two_mul_k_int k' p q hpq_le hk2
      have hpqΔ : (p : ℤ) * q = 2 * k + 1 := by exact_mod_cast hprod
      have : (2 : ℤ) * k' < 2 * k := by linarith
      have : (k' : ℤ) < k := by linarith
      exact_mod_cast this
    · rwa [hprod] at hh'

end Reencounters
