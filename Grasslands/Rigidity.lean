/-
  Grasslands/Rigidity.lean — rigid grasslands are exactly those with a Sidon set of bases.

  These results accompany the note Remainder Quotients of Interval Partitions of ℕ.

  A grassland is *rigid* when every translated pair (B_k + t, B_h + t) is equivalent on its
  first window only (m < min(g_k, g_h) − t) and never again. By the general dictionary, a
  later or earlier meeting is a second representation of the distance B_h − B_k as a
  difference of bases. Hence: rigid ⇔ the base set is a Sidon set. A Sidon set of bases
  has pairwise distinct gaps, so its gaps tend to ∞ (every distance separates eventually).
  Instances: Mersenne is rigid; the radical grassland k ↦ k^n is rigid iff
  x^n + y^n = u^n + v^n has no nontrivial solution (false for n = 2, 3, 4; open for n ≥ 5).
-/

import CampiOperazionistici.GrasslandFlatLimit
import Mathlib.Order.Filter.Cofinite

namespace Grasslands

open CampiOperazionistici

/-- A point is its chapter base plus its residue. -/
private lemma eq_base_chap_add_res (g : GapSeq) (a : ℕ) :
    a = g.base (g.chap a) + g.res a := by
  simpa [GapSeq.phi] using (g.phi_add_res a).symm

/-- Residues agree after a shift iff that shift lands on a base and the residue fits there. -/
private lemma res_eq_res_add_iff (g : GapSeq) (a Δ : ℕ) :
    g.res a = g.res (a + Δ) ↔
      ∃ h : ℕ, g.base h = g.base (g.chap a) + Δ ∧ g.res a < g.gap h := by
  constructor
  · intro heq
    refine ⟨g.chap (a + Δ), ?_, ?_⟩
    · have ha := eq_base_chap_add_res g a
      have had := eq_base_chap_add_res g (a + Δ)
      have : g.base (g.chap a) + g.res a + Δ =
          g.base (g.chap (a + Δ)) + g.res (a + Δ) := by
        rw [← ha, ← had]
      rw [heq] at this
      omega
    · have := g.res_lt_gap (a + Δ)
      rwa [← heq] at this
  · rintro ⟨h, hb, hs⟩
    have ha := eq_base_chap_add_res g a
    have had : a + Δ = g.base h + g.res a := by
      conv_lhs => rw [ha]
      have hcomm : g.base (g.chap a) + g.res a + Δ =
          g.base (g.chap a) + Δ + g.res a := by omega
      rw [hcomm, ← hb]
    rw [had, g.res_base_add hs]

/-- Adding a quantity below both bounds puts it strictly under `min − t`. -/
private lemma lt_min_sub_of_add_lt_both {a b t m : ℕ}
    (hma : t + m < a) (hmb : t + m < b) : m < min a b - t := by
  have hma' : m < a - t := (Nat.lt_sub_iff_add_lt').mpr hma
  have hmb' : m < b - t := (Nat.lt_sub_iff_add_lt').mpr hmb
  cases le_total a b with
  | inl hle => rwa [min_eq_left hle]
  | inr hle => rwa [min_eq_right hle]

/-- A bound `m < min a b − t` splits into a bound under each argument. -/
private lemma lt_sub_both_of_lt_min_sub {a b t m : ℕ}
    (hm : m < min a b - t) : m < a - t ∧ m < b - t := by
  cases le_total a b with
  | inl hle =>
    have hma : m < a - t := by rwa [min_eq_left hle] at hm
    exact ⟨hma, lt_of_lt_of_le hma (Nat.sub_le_sub_right hle t)⟩
  | inr hle =>
    have hmb : m < b - t := by rwa [min_eq_right hle] at hm
    exact ⟨lt_of_lt_of_le hmb (Nat.sub_le_sub_right hle t), hmb⟩

/-- `2^d − 1` is odd whenever `d` is positive. -/
private lemma not_two_dvd_two_pow_sub_one {d : ℕ} (hd : 0 < d) : ¬ 2 ∣ 2 ^ d - 1 := by
  intro hdiv
  have hle : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  have hpow : 2 ∣ 2 ^ d := by
    have hsucc : d = (d - 1) + 1 := by omega
    rw [hsucc, Nat.pow_succ]
    exact Nat.dvd_mul_left 2 (2 ^ (d - 1))
  have hmod : 2 ^ d % 2 = 0 := Nat.mod_eq_zero_of_dvd hpow
  have hsub : (2 ^ d - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hsum : (2 ^ d - 1 + 1) % 2 = ((2 ^ d - 1) % 2 + 1 % 2) % 2 := Nat.add_mod _ _ _
  rw [Nat.sub_add_cancel hle, hmod, hsub] at hsum
  exact absurd hsum.symm (by decide)

/-- Factor a difference of powers of two as `2^k` times an odd cofactor. -/
private lemma two_pow_sub_factor {k h : ℕ} (hk : k ≤ h) :
    2 ^ h - 2 ^ k = 2 ^ k * (2 ^ (h - k) - 1) := by
  have hpow : 2 ^ h = 2 ^ k * 2 ^ (h - k) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have hmul : 2 ^ k * (2 ^ (h - k) - 1) = 2 ^ k * 2 ^ (h - k) - 2 ^ k := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hpow, ← hmul]

/-- Products `2^a * m = 2^b * n` with odd `m` and `n` force equal exponents and cofactors. -/
private lemma eq_of_two_pow_mul_odd {a b m n : ℕ} (hm : ¬ 2 ∣ m) (hn : ¬ 2 ∣ n)
    (h : 2 ^ a * m = 2 ^ b * n) : a = b ∧ m = n := by
  suffices ∀ a b m n : ℕ, ¬ 2 ∣ m → ¬ 2 ∣ n → 2 ^ a * m = 2 ^ b * n → a ≤ b →
      a = b ∧ m = n by
    rcases le_total a b with hab | hba
    · exact this a b m n hm hn h hab
    · obtain ⟨hba', hmn⟩ := this b a n m hn hm h.symm hba
      exact ⟨hba'.symm, hmn.symm⟩
  intro a b m n hm hn h hab
  have hcancel : m = 2 ^ (b - a) * n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a)
    have hbpow : 2 ^ b = 2 ^ (a + (b - a)) := congrArg (fun n => 2 ^ n) (Nat.add_sub_of_le hab).symm
    rw [h, hbpow, Nat.pow_add, Nat.mul_assoc]
  have haeq : a = b := by
    by_contra hne
    have hpos : 0 < b - a := Nat.sub_pos_of_lt (lt_of_le_of_ne hab hne)
    have hdvd : 2 ∣ m := by
      have hsucc : b - a = (b - a - 1) + 1 := by omega
      rw [hcancel, hsucc, Nat.pow_succ]
      exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left 2 _) n
    exact hm hdvd
  refine ⟨haeq, ?_⟩
  simpa [haeq, Nat.pow_zero, Nat.one_mul] using hcancel

/-- The bases form a Sidon set: distinct pairs `k < h` have distinct differences. -/
def IsSidonBases (g : GapSeq) : Prop :=
  ∀ k h k' h' : ℕ, k < h → k' < h' →
    g.base h - g.base k = g.base h' - g.base k' → k = k' ∧ h = h'

/-- Every translated pair is equivalent on its first window and never again. -/
def IsRigid (g : GapSeq) : Prop :=
  ∀ k h t m : ℕ, k < h → t < g.gap k → t < g.gap h →
    (g.res (g.base k + t + m) = g.res (g.base h + t + m) ↔ m < min (g.gap k) (g.gap h) - t)

/-- The same base difference with a strictly later left index contradicts rigidity. -/
private lemma false_of_rigid_repeated_diff (g : GapSeq) (hr : IsRigid g)
    {k h k' h' : ℕ} (hk : k < h) (hk' : k' < h') (hlt : k < k')
    (heq : g.base h - g.base k = g.base h' - g.base k') : False := by
  set m := g.base k' - g.base k
  have hkk' : g.base k ≤ g.base k' := g.base_mono hlt.le
  have hkh : g.base k ≤ g.base h := g.base_mono hk.le
  have hk'h' : g.base k' ≤ g.base h' := g.base_mono hk'.le
  have hm_gap : g.gap k ≤ m := by
    have hsucc : g.base (k + 1) ≤ g.base k' := g.base_mono (Nat.succ_le_of_lt hlt)
    rw [g.base_succ] at hsucc
    omega
  have hm_k : g.base k + m = g.base k' := by omega
  have hm_h : g.base h + m = g.base h' := by omega
  have heqv : g.res (g.base k + 0 + m) = g.res (g.base h + 0 + m) := by
    have hL : g.base k + 0 + m = g.base k' := by omega
    have hR : g.base h + 0 + m = g.base h' := by omega
    rw [hL, hR, g.res_base, g.res_base]
  have hsmall := (hr k h 0 m hk (g.pos k) (g.pos h)).mp heqv
  have hlt_min : m < min (g.gap k) (g.gap h) := by simpa using hsmall
  exact Nat.not_lt.mpr (le_trans (min_le_left _ _) hm_gap) hlt_min

/-- **Rigidity ⇔ Sidon.** -/
theorem rigid_iff_sidon (g : GapSeq) : IsRigid g ↔ IsSidonBases g := by
  constructor
  · intro hr k h k' h' hk hk' heq
    rcases lt_trichotomy k k' with hlt | heqk | hgt
    · exact (false_of_rigid_repeated_diff g hr hk hk' hlt heq).elim
    · subst heqk
      refine ⟨rfl, g.base_strictMono.injective ?_⟩
      have hkh : g.base k ≤ g.base h := g.base_mono hk.le
      have hkh' : g.base k ≤ g.base h' := g.base_mono hk'.le
      omega
    · exact (false_of_rigid_repeated_diff g hr hk' hk hgt heq.symm).elim
  · intro hs k h t m hk htk hth
    constructor
    · intro heq
      set a := g.base k + t + m
      set Δ := g.base h - g.base k
      have hkh : g.base k ≤ g.base h := g.base_mono hk.le
      have hadd : a + Δ = g.base h + t + m := by omega
      have heqΔ : g.res a = g.res (a + Δ) := by simpa [hadd] using heq
      obtain ⟨h', hb, hfit⟩ := (res_eq_res_add_iff g a Δ).mp heqΔ
      have hΔ : 0 < Δ := by
        have := g.base_strictMono hk
        omega
      have hlt : g.chap a < h' := by
        have hbase : g.base (g.chap a) < g.base h' := by omega
        exact g.base_strictMono.lt_iff_lt.mp hbase
      have hdiff : g.base h' - g.base (g.chap a) = g.base h - g.base k := by
        rw [hb, Nat.add_sub_cancel_left]
      obtain ⟨hchap, hh⟩ := hs (g.chap a) h' k h hlt hk hdiff
      have hresa : g.res a = t + m := by
        simp only [GapSeq.res, GapSeq.phi, hchap, a]
        omega
      have htkm : t + m < g.gap k := by
        have := g.res_lt_gap a
        rwa [hresa, hchap] at this
      have hthm : t + m < g.gap h := by
        have := hfit
        rwa [hresa, hh] at this
      exact lt_min_sub_of_add_lt_both htkm hthm
    · intro hm
      obtain ⟨hmk, hmh⟩ := lt_sub_both_of_lt_min_sub hm
      have htm_k : t + m < g.gap k := (Nat.lt_sub_iff_add_lt').mp hmk
      have htm_h : t + m < g.gap h := (Nat.lt_sub_iff_add_lt').mp hmh
      have hL := g.res_base_add (k := k) (t := t + m) htm_k
      have hR := g.res_base_add (k := h) (t := t + m) htm_h
      rw [show g.base k + t + m = g.base k + (t + m) by omega,
        show g.base h + t + m = g.base h + (t + m) by omega, hL, hR]

/-- A Sidon set of bases has injective gaps. -/
theorem gap_injective_of_sidon (g : GapSeq) (hs : IsSidonBases g) : Function.Injective g.gap := by
  intro k j hg
  have hdiff : g.base (k + 1) - g.base k = g.base (j + 1) - g.base j := by
    rw [g.base_succ k, g.base_succ j, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, hg]
  rcases lt_trichotomy k j with hlt | heq | hgt
  · exact (hs k (k + 1) j (j + 1) (Nat.lt_succ_self k) (Nat.lt_succ_self j) hdiff).1
  · exact heq
  · exact (hs j (j + 1) k (k + 1) (Nat.lt_succ_self j) (Nat.lt_succ_self k) hdiff.symm).1.symm

/-- A Sidon set of bases has gaps tending to infinity. -/
theorem tendsto_gap_of_sidon (g : GapSeq) (hs : IsSidonBases g) :
    Filter.Tendsto g.gap Filter.atTop Filter.atTop :=
  (gap_injective_of_sidon g hs).nat_tendsto_atTop

/-- The Mersenne grassland is rigid. -/
theorem mersenne_isSidon : IsSidonBases mersenneSeq := by
  intro k h k' h' hk hk' heq
  rw [mersenneSeq_base, mersenneSeq_base, mersenneSeq_base, mersenneSeq_base] at heq
  have heq' : 2 ^ h - 2 ^ k = 2 ^ h' - 2 ^ k' := by
    have h1k : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have h1h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    have h1k' : 1 ≤ 2 ^ k' := Nat.one_le_pow k' 2 (by decide)
    have h1h' : 1 ≤ 2 ^ h' := Nat.one_le_pow h' 2 (by decide)
    have hpow : 2 ^ k ≤ 2 ^ h := Nat.pow_le_pow_right (by decide : 0 < 2) hk.le
    have hpow' : 2 ^ k' ≤ 2 ^ h' := Nat.pow_le_pow_right (by decide : 0 < 2) hk'.le
    omega
  rw [two_pow_sub_factor hk.le, two_pow_sub_factor hk'.le] at heq'
  obtain ⟨rfl, hcof⟩ := eq_of_two_pow_mul_odd
    (not_two_dvd_two_pow_sub_one (Nat.sub_pos_of_lt hk))
    (not_two_dvd_two_pow_sub_one (Nat.sub_pos_of_lt hk')) heq'
  have hexp : 2 ^ (h - k) = 2 ^ (h' - k) := by
    have hle : 1 ≤ 2 ^ (h - k) := Nat.one_le_pow (h - k) 2 (by decide)
    have hle' : 1 ≤ 2 ^ (h' - k) := Nat.one_le_pow (h' - k) 2 (by decide)
    omega
  have hsub : h - k = h' - k := (Nat.pow_right_injective (le_rfl : 2 ≤ 2)) hexp
  omega

/-- The radical grassland `k ↦ k^n` has a Sidon set of bases iff differences of `n`-th powers
are unique: `h^n − k^n = h'^n − k'^n` with `k < h`, `k' < h'` forces `(k, h) = (k', h')`
(equivalently, `x^n + y^n = u^n + v^n` has only trivial solutions). -/
theorem radical_isSidon_iff (n : ℕ) (hn : n ≠ 0) :
    IsSidonBases (radicalSeq n hn) ↔
      ∀ k h k' h' : ℕ, k < h → k' < h' → h ^ n - k ^ n = h' ^ n - k' ^ n → k = k' ∧ h = h' := by
  constructor
  · intro hs k h k' h' hk hk' heq
    apply hs k h k' h' hk hk'
    simpa [radicalSeq_base] using heq
  · intro hpow k h k' h' hk hk' heq
    apply hpow k h k' h' hk hk'
    simpa [radicalSeq_base] using heq

/-- The square grassland is not rigid (`7² − 1² = 8² − 4² = 48`). -/
theorem radical_two_not_sidon : ¬ IsSidonBases (radicalSeq 2 (by norm_num)) := by
  intro hs
  obtain ⟨h1, _⟩ := hs 1 7 4 8 (by decide) (by decide) (by
    simp only [radicalSeq_base]
    decide)
  exact absurd h1 (by decide)

/-- A later base difference strictly exceeds every earlier base when gaps are superincreasing. -/
private lemma earlier_base_lt_base_sub (g : GapSeq) (hg : ∀ k, g.base k < g.gap k)
    {k h j : ℕ} (hk : k < h) (hj : j < h) : g.base j < g.base h - g.base k := by
  have h1 : 1 ≤ h := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hk)
  have hadd : h - 1 + 1 = h := Nat.sub_add_cancel h1
  have hgap : g.base h - g.base (h - 1) = g.gap (h - 1) := by
    have hb : g.base h = g.base (h - 1) + g.gap (h - 1) := by
      conv_lhs => rw [← hadd]
      exact g.base_succ (h - 1)
    rw [hb, Nat.add_sub_cancel_left]
  have hge : g.base h - g.base (h - 1) ≤ g.base h - g.base k :=
    Nat.sub_le_sub_left (g.base_mono (Nat.le_sub_one_of_lt hk)) _
  calc g.base j
      ≤ g.base (h - 1) := g.base_mono (Nat.le_sub_one_of_lt hj)
    _ < g.gap (h - 1) := hg (h - 1)
    _ = g.base h - g.base (h - 1) := hgap.symm
    _ ≤ g.base h - g.base k := hge

/-- **Superincreasing widths give a rigid grassland.** If every width exceeds the sum of the
previous ones (`B_k < g_k`, i.e. `B_{k+1} > 2 B_k`), the bases form a Sidon set. Mersenne
(`g_k = 2^k = B_k + 1`) is the extremal case. -/
theorem sidon_of_superincreasing (g : GapSeq) (hg : ∀ k, g.base k < g.gap k) : IsSidonBases g := by
  intro k h k' h' hk hk' heq
  have hh : h = h' := by
    rcases lt_trichotomy h h' with hlt | heqh | hgt
    · exact absurd heq (ne_of_lt <| lt_of_le_of_lt (Nat.sub_le _ _)
        (earlier_base_lt_base_sub g hg hk' hlt))
    · exact heqh
    · exact absurd heq.symm (ne_of_lt <| lt_of_le_of_lt (Nat.sub_le _ _)
        (earlier_base_lt_base_sub g hg hk hgt))
  subst hh
  have hbase : g.base k = g.base k' := by
    have hbk : g.base k ≤ g.base h := g.base_mono hk.le
    have hbk' : g.base k' ≤ g.base h := g.base_mono hk'.le
    omega
  exact ⟨g.base_strictMono.injective hbase, rfl⟩

/-- The cubic grassland is not rigid: `12³ − 9³ = 10³ − 1³ = 999` (Frénicle's `1729 = 1³ + 12³ = 9³ + 10³`). -/
theorem radical_three_not_sidon : ¬ IsSidonBases (radicalSeq 3 (by norm_num)) := by
  rw [radical_isSidon_iff]
  intro h
  have := h 9 12 1 10 (by norm_num) (by norm_num) (by norm_num)
  omega

/-- The quartic grassland is not rigid: `158⁴ − 134⁴ = 133⁴ − 59⁴` (Euler's
`59⁴ + 158⁴ = 133⁴ + 134⁴ = 635318657`). -/
theorem radical_four_not_sidon : ¬ IsSidonBases (radicalSeq 4 (by norm_num)) := by
  rw [radical_isSidon_iff]
  intro h
  have := h 134 158 59 133 (by norm_num) (by norm_num) (by norm_num)
  omega

end Grasslands
