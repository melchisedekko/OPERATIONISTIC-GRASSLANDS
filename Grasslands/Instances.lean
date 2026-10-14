/-
  Grasslands/Instances.lean — two exponential grasslands with opposite dynamics.

  These results accompany the note Remainder Quotients of Interval Partitions of ℕ.

  * Mersenne (g_k = 2^k, B_k = 2^k − 1): base differences 2^h − 2^k are distinct (binary
    uniqueness), so a translated pair is equivalent on its first window ONLY: it never
    meets again. The grassland is rigid.
  * Fibonacci (g_k = F_{k+1}: 1, 1, 2, 3, 5, …): base differences coincide exactly for the
    pairs (j, j+2) and (j+2, j+3) — and (0,1), (1,2) — so every pair at index distance 2
    meets again exactly once, in the chapter pair (j+2, j+3).
-/

import CampiOperazionistici.GrasslandFlatLimit

namespace Grasslands

open CampiOperazionistici

/-- A positive power of two is twice the preceding power. -/
private lemma two_pow_pred_mul {a : ℕ} (ha : 0 < a) : 2 ^ a = 2 * 2 ^ (a - 1) := by
  cases a with
  | zero => omega
  | succ a =>
    simp [pow_succ, Nat.mul_comm]

/-- `2^h - 2^k` determines the pair `k < h`. -/
private lemma two_pow_sub_injective {k h k' h' : ℕ} (hkh : k < h) (hkh' : k' < h')
    (heq : 2 ^ h - 2 ^ k = 2 ^ h' - 2 ^ k') : k = k' ∧ h = h' := by
  suffices ∀ k, ∀ h k' h' : ℕ, k < h → k' < h' →
      2 ^ h - 2 ^ k = 2 ^ h' - 2 ^ k' → k = k' ∧ h = h' by
    exact this k h k' h' hkh hkh' heq
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h k' h' hkh hkh' heq
    have h2 : (1 : ℕ) < 2 := by decide
    by_cases hk0 : k = 0
    · subst hk0
      have hle : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
      have hnot : ¬ Even (2 ^ h - 1) := by
        intro hev
        have hiff := (Nat.even_sub hle).mp hev
        have hevenh : Even (2 ^ h) := by
          rw [Nat.even_pow]
          exact ⟨by decide, by omega⟩
        exact Nat.not_even_one (hiff.mp hevenh)
      have hk'0 : k' = 0 := by
        by_contra hk'
        have hle' : 2 ^ k' ≤ 2 ^ h' := (Nat.pow_le_pow_iff_right h2).mpr (le_of_lt hkh')
        have heven : Even (2 ^ h' - 2 ^ k') := by
          have heh : Even (2 ^ h') := by
            rw [Nat.even_pow]
            exact ⟨by decide, by omega⟩
          have hek : Even (2 ^ k') := by
            rw [Nat.even_pow]
            exact ⟨by decide, hk'⟩
          exact (Nat.even_sub hle').mpr (iff_of_true heh hek)
        exact hnot (by simpa [pow_zero] using (heq ▸ heven))
      subst hk'0
      have hpow : 2 ^ h = 2 ^ h' := by
        have h1' : 1 ≤ 2 ^ h' := Nat.one_le_pow h' 2 (by decide)
        have : 2 ^ h - 1 = 2 ^ h' - 1 := by simpa [pow_zero] using heq
        omega
      exact ⟨rfl, (Nat.pow_right_inj h2).mp hpow⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hle : 2 ^ k ≤ 2 ^ h := (Nat.pow_le_pow_iff_right h2).mpr (le_of_lt hkh)
      have hevenL : Even (2 ^ h - 2 ^ k) := by
        have heh : Even (2 ^ h) := by
          rw [Nat.even_pow]
          exact ⟨by decide, by omega⟩
        have hek : Even (2 ^ k) := by
          rw [Nat.even_pow]
          exact ⟨by decide, hk0⟩
        exact (Nat.even_sub hle).mpr (iff_of_true heh hek)
      have hk'pos : 0 < k' := by
        by_contra hk'
        have hk'0 : k' = 0 := by omega
        subst hk'0
        have hle1 : 1 ≤ 2 ^ h' := Nat.one_le_pow h' 2 (by decide)
        have hnot : ¬ Even (2 ^ h' - 1) := by
          intro hev
          have hiff := (Nat.even_sub hle1).mp hev
          have hevenh : Even (2 ^ h') := by
            rw [Nat.even_pow]
            exact ⟨by decide, by omega⟩
          exact Nat.not_even_one (hiff.mp hevenh)
        exact hnot (by simpa [pow_zero] using (heq ▸ hevenL))
      have hdivL : 2 ^ h - 2 ^ k = 2 * (2 ^ (h - 1) - 2 ^ (k - 1)) := by
        rw [two_pow_pred_mul (by omega), two_pow_pred_mul hkpos, ← Nat.mul_sub_left_distrib]
      have hdivR : 2 ^ h' - 2 ^ k' = 2 * (2 ^ (h' - 1) - 2 ^ (k' - 1)) := by
        rw [two_pow_pred_mul (by omega), two_pow_pred_mul hk'pos, ← Nat.mul_sub_left_distrib]
      have hdiv : 2 ^ (h - 1) - 2 ^ (k - 1) = 2 ^ (h' - 1) - 2 ^ (k' - 1) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
        rw [← hdivL, ← hdivR, heq]
      have hstep := ih (k - 1) (by omega) (h - 1) (k' - 1) (h' - 1) (by omega) (by omega) hdiv
      omega

/-- Mersenne base gaps are pure differences of powers of two. -/
private lemma mersenneSeq_base_sub {k h : ℕ} (hk : k ≤ h) :
    mersenneSeq.base h - mersenneSeq.base k = 2 ^ h - 2 ^ k := by
  rw [mersenneSeq_base, mersenneSeq_base]
  have h1k : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have h1h : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
  have hle : 2 ^ k ≤ 2 ^ h := (Nat.pow_le_pow_iff_right (by decide)).mpr hk
  omega

/-- Mersenne base differences are injective on pairs `k < h`. -/
theorem mersenne_base_sub_injective {k h k' h' : ℕ} (hkh : k < h) (hkh' : k' < h')
    (heq : mersenneSeq.base h - mersenneSeq.base k = mersenneSeq.base h' - mersenneSeq.base k') :
    k = k' ∧ h = h' := by
  rw [mersenneSeq_base_sub (le_of_lt hkh), mersenneSeq_base_sub (le_of_lt hkh')] at heq
  exact two_pow_sub_injective hkh hkh' heq

/-- **Mersenne rigidity.** A translated pair is equivalent exactly on its first window. -/
theorem mersenne_first_window_only (k h t m : ℕ) (hkh : k < h) (ht : t < 2 ^ k) :
    mersenneSeq.res (mersenneSeq.base k + t + m) = mersenneSeq.res (mersenneSeq.base h + t + m) ↔
      m < 2 ^ k - t := by
  constructor
  · intro heq
    let a := mersenneSeq.base k + t + m
    let b := mersenneSeq.base h + t + m
    have ha : a = mersenneSeq.base (mersenneSeq.chap a) + mersenneSeq.res a := by
      simpa [GapSeq.phi] using (mersenneSeq.phi_add_res a).symm
    have hb : b = mersenneSeq.base (mersenneSeq.chap b) + mersenneSeq.res b := by
      simpa [GapSeq.phi] using (mersenneSeq.phi_add_res b).symm
    have hs : mersenneSeq.res a = mersenneSeq.res b := by simpa using heq
    have hab : a < b := by
      have hbase : mersenneSeq.base k < mersenneSeq.base h := mersenneSeq.base_strictMono hkh
      show mersenneSeq.base k + t + m < mersenneSeq.base h + t + m
      omega
    have hchap : mersenneSeq.chap a < mersenneSeq.chap b := by
      have hlt_base : mersenneSeq.base (mersenneSeq.chap a) <
          mersenneSeq.base (mersenneSeq.chap b) := by
        have hb' : b = mersenneSeq.base (mersenneSeq.chap b) + mersenneSeq.res a := by
          rw [← hs] at hb
          exact hb
        omega
      exact (mersenneSeq.base_strictMono.lt_iff_lt).mp hlt_base
    have hdiff : mersenneSeq.base h - mersenneSeq.base k =
        mersenneSeq.base (mersenneSeq.chap b) - mersenneSeq.base (mersenneSeq.chap a) := by
      have hba : b - a = mersenneSeq.base h - mersenneSeq.base k := by
        show (mersenneSeq.base h + t + m) - (mersenneSeq.base k + t + m) =
          mersenneSeq.base h - mersenneSeq.base k
        rw [Nat.add_assoc, Nat.add_assoc]
        exact Nat.add_sub_add_right (mersenneSeq.base h) (t + m) (mersenneSeq.base k)
      have hsub := Nat.add_sub_add_right (mersenneSeq.base (mersenneSeq.chap b))
        (mersenneSeq.res a) (mersenneSeq.base (mersenneSeq.chap a))
      have hb' : b = mersenneSeq.base (mersenneSeq.chap b) + mersenneSeq.res a := by
        rw [← hs] at hb
        exact hb
      rw [← ha, ← hb'] at hsub
      omega
    have hinj := mersenne_base_sub_injective hkh hchap hdiff
    have htm : t + m = mersenneSeq.res a := by
      have hchap_k : mersenneSeq.chap a = k := hinj.1.symm
      have : a = mersenneSeq.base k + mersenneSeq.res a := by simpa [hchap_k] using ha
      have : mersenneSeq.base k + t + m = mersenneSeq.base k + mersenneSeq.res a := by
        simpa [a, Nat.add_assoc] using this
      omega
    have hres : mersenneSeq.res a < 2 ^ k := by
      have hlt := mersenneSeq.res_lt_gap a
      rw [hinj.1.symm] at hlt
      change mersenneSeq.res a < 2 ^ k at hlt
      exact hlt
    omega
  · intro hm
    have hk : t + m < mersenneSeq.gap k := by
      show t + m < 2 ^ k
      omega
    have hh : t + m < mersenneSeq.gap h := by
      have hpow : 2 ^ k < 2 ^ h := (Nat.pow_lt_pow_iff_right (by decide)).mpr hkh
      show t + m < 2 ^ h
      omega
    simpa [GapSeq.seqEquiv] using GapSeq.seqEquiv_window mersenneSeq hk hh

/-- The Fibonacci grassland: chapter widths `F_{k+1}` = 1, 1, 2, 3, 5, … -/
def fibSeq : GapSeq := ⟨fun k => Nat.fib (k + 1), fun k => Nat.fib_pos.mpr (Nat.succ_pos k)⟩

/-- Fibonacci chapter bases are one less than a Fibonacci number: `B_k = F_{k+2} - 1`. -/
lemma fibSeq_base (k : ℕ) : fibSeq.base k = Nat.fib (k + 2) - 1 := by
  induction k with
  | zero => simp [GapSeq.base, Nat.fib_two]
  | succ k ih =>
    rw [GapSeq.base_succ, ih]
    simp only [fibSeq]
    have hone : 1 ≤ Nat.fib (k + 2) := by
      have : 0 < Nat.fib (k + 2) := by rw [Nat.fib_pos]; omega
      omega
    have hrec : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      have h0 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 1 + 1) := Nat.fib_add_two
      simpa [show k + 1 + 1 = k + 2 by omega] using h0
    omega

/-- Subtracting Fibonacci bases cancels the `− 1` and leaves a Fibonacci difference. -/
private lemma fibSeq_base_sub {k h : ℕ} (hk : k ≤ h) :
    fibSeq.base h - fibSeq.base k = Nat.fib (h + 2) - Nat.fib (k + 2) := by
  rw [fibSeq_base, fibSeq_base]
  have hfk : 1 ≤ Nat.fib (k + 2) := by
    have : 0 < Nat.fib (k + 2) := by rw [Nat.fib_pos]; omega
    omega
  have hfh : 1 ≤ Nat.fib (h + 2) := by
    have : 0 < Nat.fib (h + 2) := by rw [Nat.fib_pos]; omega
    omega
  have hle : Nat.fib (k + 2) ≤ Nat.fib (h + 2) := Nat.fib_mono (by omega)
  omega

/-- Equal Fibonacci gaps with `h' ≤ h` are `(k', h') = (j, j+2)`, `(k, h) = (j+2, j+3)`, or `(1,2)` with `(0,1)`. -/
private lemma fib_sub_eq_of_le {k h k' h' : ℕ} (hkh : k < h) (hkh' : k' < h')
    (hne : (k, h) ≠ (k', h')) (hle : h' ≤ h)
    (heq : Nat.fib (h + 2) - Nat.fib (k + 2) = Nat.fib (h' + 2) - Nat.fib (k' + 2)) :
    (h' = k' + 2 ∧ k = k' + 2 ∧ h = k' + 3) ∨
      ((k, h) = (1, 2) ∧ (k', h') = (0, 1)) := by
  have hfk_le : Nat.fib (k + 2) ≤ Nat.fib (h + 2) := Nat.fib_mono (by omega)
  have hfk'_le : Nat.fib (k' + 2) ≤ Nat.fib (h' + 2) := Nat.fib_mono (by omega)
  by_cases heqh : h = h'
  · subst heqh
    have hfib : Nat.fib (k + 2) = Nat.fib (k' + 2) := by
      have h1 := (Nat.sub_add_cancel hfk_le).symm
      have h2 := (Nat.sub_add_cancel hfk'_le).symm
      omega
    have hk : k = k' := Nat.fib_add_two_strictMono.injective hfib
    exact absurd (by simp [hk]) hne
  · have hlt_h : h' < h := lt_of_le_of_ne hle (fun hh => heqh hh.symm)
    have hsucc : h' + 1 ≤ h := Nat.succ_le_of_lt hlt_h
    rcases Nat.eq_or_lt_of_le hsucc with rfl | hbig
    · have hsum : Nat.fib (k + 2) = Nat.fib (k' + 2) + Nat.fib (h' + 1) := by
        have hrec : Nat.fib (h' + 3) = Nat.fib (h' + 1) + Nat.fib (h' + 2) := by
          rw [show h' + 3 = h' + 1 + 2 by omega]
          exact Nat.fib_add_two
        have heq' : Nat.fib (h' + 3) - Nat.fib (k + 2) =
            Nat.fib (h' + 2) - Nat.fib (k' + 2) := by
          simpa [show (h' + 1) + 2 = h' + 3 by omega] using heq
        have hA : Nat.fib (h' + 3) =
            Nat.fib (h' + 2) - Nat.fib (k' + 2) + Nat.fib (k + 2) :=
          (Nat.sub_eq_iff_eq_add (Nat.fib_mono (by omega))).mp heq'
        have hB := (Nat.sub_add_cancel hfk'_le).symm
        omega
      have hk_le : k ≤ h' := by omega
      rcases lt_or_eq_of_le hk_le with hklt | hkeq
      · have hle_k : Nat.fib (k + 2) ≤ Nat.fib (h' + 1) := Nat.fib_mono (by omega)
        have hone : 1 ≤ Nat.fib (k' + 2) := by
          have : 0 < Nat.fib (k' + 2) := by rw [Nat.fib_pos]; omega
          omega
        omega
      · have hf : Nat.fib (k' + 2) = Nat.fib h' := by
          have hsum' : Nat.fib (h' + 2) = Nat.fib (k' + 2) + Nat.fib (h' + 1) := by
            simpa [hkeq] using hsum
          have hrec2 : Nat.fib (h' + 2) = Nat.fib h' + Nat.fib (h' + 1) := Nat.fib_add_two
          omega
        by_cases hh2 : 2 ≤ h'
        · have hidx : k' + 2 = h' := by
            rcases lt_trichotomy (k' + 2) h' with h1 | h1 | h1
            · have := (Nat.fib_lt_fib (by omega)).mpr h1
              omega
            · exact h1
            · have := (Nat.fib_lt_fib hh2).mpr h1
              omega
          exact Or.inl (by omega)
        · have hh1 : h' = 1 := by omega
          have hk0 : k' = 0 := by omega
          exact Or.inr ⟨by rw [hkeq, hh1], by rw [hk0, hh1]⟩
    · have hleft : Nat.fib h ≤ Nat.fib (h + 2) - Nat.fib (k + 2) := by
        have hk : Nat.fib (k + 2) ≤ Nat.fib (h + 1) := Nat.fib_mono (by omega)
        have hstep : Nat.fib (h + 2) - Nat.fib (h + 1) = Nat.fib h :=
          Nat.fib_add_two_sub_fib_add_one
        have hcmp : Nat.fib (h + 2) - Nat.fib (h + 1) ≤
            Nat.fib (h + 2) - Nat.fib (k + 2) := Nat.sub_le_sub_left hk _
        omega
      have hright : Nat.fib (h' + 2) - Nat.fib (k' + 2) < Nat.fib (h' + 2) :=
        Nat.sub_lt_of_pos_le (Nat.fib_pos.mpr (by omega)) hfk'_le
      have hmono : Nat.fib (h' + 2) ≤ Nat.fib h := Nat.fib_mono (by omega)
      omega

/-- **Fibonacci coincidences.** Two distinct chapter pairs at the same base distance are
`(j, j+2)` and `(j+2, j+3)`, or `(0,1)` and `(1,2)`. -/
theorem fib_base_sub_eq_iff {k h k' h' : ℕ} (hkh : k < h) (hkh' : k' < h') (hne : (k, h) ≠ (k', h'))
    (heq : fibSeq.base h - fibSeq.base k = fibSeq.base h' - fibSeq.base k') :
    (h = k + 2 ∧ k' = k + 2 ∧ h' = k + 3) ∨ (h' = k' + 2 ∧ k = k' + 2 ∧ h = k' + 3) ∨
      ((k, h) = (0, 1) ∧ (k', h') = (1, 2)) ∨ ((k, h) = (1, 2) ∧ (k', h') = (0, 1)) := by
  have heq' : Nat.fib (h + 2) - Nat.fib (k + 2) =
      Nat.fib (h' + 2) - Nat.fib (k' + 2) := by
    rw [← fibSeq_base_sub (le_of_lt hkh), ← fibSeq_base_sub (le_of_lt hkh')]
    exact heq
  have hne' : (k', h') ≠ (k, h) := fun h => hne h.symm
  rcases Nat.le_total h h' with hle | hle
  · rcases fib_sub_eq_of_le hkh' hkh hne' hle heq'.symm with H | H
    · exact Or.inl H
    · exact Or.inr (Or.inr (Or.inl ⟨H.2, H.1⟩))
  · rcases fib_sub_eq_of_le hkh hkh' hne hle heq' with H | H
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr (Or.inr H))

/-- The coincidence is realised: `B_{j+2} − B_j = B_{j+3} − B_{j+2}`. -/
theorem fib_base_coincidence (j : ℕ) :
    fibSeq.base (j + 2) - fibSeq.base j = fibSeq.base (j + 3) - fibSeq.base (j + 2) := by
  rw [fibSeq_base_sub (by omega), fibSeq_base_sub (by omega)]
  have hL : Nat.fib (j + 2 + 2) = Nat.fib (j + 2) + Nat.fib (j + 3) := by
    have h0 : Nat.fib (j + 2 + 2) = Nat.fib (j + 2) + Nat.fib (j + 2 + 1) := Nat.fib_add_two
    simpa [show j + 2 + 1 = j + 3 by omega] using h0
  have hR : Nat.fib (j + 3 + 2) = Nat.fib (j + 3) + Nat.fib (j + 2 + 2) := by
    have h0 : Nat.fib (j + 3 + 2) = Nat.fib (j + 3) + Nat.fib (j + 3 + 1) := Nat.fib_add_two
    simpa [show j + 3 + 1 = j + 2 + 2 by omega] using h0
  omega

/-- The common distance of the coincidence is a Fibonacci number: `B_{j+2} − B_j = F_{j+3}`. -/
theorem fib_base_sub_two (j : ℕ) : fibSeq.base (j + 2) - fibSeq.base j = Nat.fib (j + 3) := by
  rw [fibSeq_base_sub (by omega : j ≤ j + 2)]
  have h : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  rw [show j + 2 + 2 = j + 4 by omega, h]
  omega

end Grasslands
