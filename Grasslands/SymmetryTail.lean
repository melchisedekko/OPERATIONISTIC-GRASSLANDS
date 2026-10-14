/-
  Grasslands/SymmetryTail.lean — the translation symmetries of an eventually flat grassland.

  These results accompany the note Remainder Quotients of Interval Partitions of ℕ.

  Let g be eventually flat: g_k = m for every k ≥ p₀. For T ≥ B_{p₀}, the translation by T
  is a symmetry iff m divides every width: a + T and b + T both lie in the flat tail, where
  the remainder is (x − B_{p₀}) mod m, and equivalent points are congruent mod m when every
  base is a multiple of m; conversely the translated bases B_k + T and B_{k+1} + T must have
  the same remainder T mod m, which forces m ∣ g_k.

  Symmetries below B_{p₀} also occur, so this is not a classification: the widths
  3, 1, 2, 1, 1, 1, … (m = 1, p₀ = 3, B_{p₀} = 6) have the symmetry T = 3 (found by
  experiments/general_grasslands/; a conjectured converse was refuted this way on 2026-10-13).
-/

import Grasslands.Symmetry

namespace Grasslands

open CampiOperazionistici
open GapSeq

/-! ## Tail arithmetic -/

/-- In the flat tail, bases advance by constant steps of `m`. -/
private lemma base_add_of_tail (g : GapSeq) {m p₀ : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (j : ℕ) :
    g.base (p₀ + j) = g.base p₀ + j * m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, base_succ, ih, htail (p₀ + j) (Nat.le_add_right _ _), Nat.succ_mul]
    ring

/-- Positivity of the eventual width. -/
private lemma tail_gap_pos (g : GapSeq) {m p₀ : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) : 0 < m := by
  have := g.pos p₀
  rwa [htail p₀ le_rfl] at this

/-- Chapter index in the flat tail. -/
private lemma chap_of_tail (g : GapSeq) {m p₀ x : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (hx : g.base p₀ ≤ x) :
    g.chap x = p₀ + (x - g.base p₀) / m := by
  have hm := tail_gap_pos g htail
  set d := x - g.base p₀
  have hx' : x = g.base p₀ + d := by omega
  have hsplit : d / m * m + d % m = d := Nat.div_add_mod' d m
  have hr : d % m < m := Nat.mod_lt d hm
  apply g.chap_eq_of
  · rw [base_add_of_tail g htail (d / m), hx']
    have := Nat.mul_div_le d m
    omega
  · have hsucc : p₀ + d / m + 1 = p₀ + (d / m + 1) := by omega
    rw [hsucc, base_add_of_tail g htail (d / m + 1), hx']
    calc g.base p₀ + d
        = g.base p₀ + (d / m * m + d % m) := by rw [hsplit]
      _ < g.base p₀ + (d / m * m + m) := by omega
      _ = g.base p₀ + (d / m + 1) * m := by ring

/-- Residue in the flat tail. -/
private lemma res_of_tail (g : GapSeq) {m p₀ x : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (hx : g.base p₀ ≤ x) :
    g.res x = (x - g.base p₀) % m := by
  set d := x - g.base p₀
  have hchap := chap_of_tail g htail hx
  have hbase := base_add_of_tail g htail (d / m)
  have hx' : x = g.base p₀ + d := by omega
  unfold res phi
  rw [hchap, hbase, hx']
  have hsplit : d / m * m + d % m = d := Nat.div_add_mod' d m
  omega

/-- Every base is a multiple of `m` when `m` divides every width. -/
private lemma base_dvd_of_gap_dvd (g : GapSeq) {m : ℕ}
    (hdiv : ∀ k, m ∣ g.gap k) (k : ℕ) : m ∣ g.base k := by
  induction k with
  | zero => exact Nat.dvd_zero m
  | succ k ih =>
    rw [base_succ]
    exact Nat.dvd_add ih (hdiv k)

/-- Congruence of a point with its residue, modulo `m`. -/
private lemma mod_eq_res_of_dvd (g : GapSeq) {m x : ℕ}
    (hdiv : ∀ k, m ∣ g.gap k) : x % m = g.res x % m := by
  set b := g.base (g.chap x)
  set r := g.res x
  have hx : x = b + r := by
    have := g.phi_add_res x
    simp only [phi, b, r] at this ⊢
    omega
  have hb : b % m = 0 :=
    Nat.mod_eq_zero_of_dvd (base_dvd_of_gap_dvd g hdiv _)
  calc x % m
      = (b + r) % m := by rw [hx]
    _ = (b % m + r % m) % m := Nat.add_mod _ _ _
    _ = (0 + r % m) % m := by rw [hb]
    _ = r % m := by simp
    _ = g.res x % m := rfl

/-- Equivalent points are congruent mod `m` when widths are multiples of `m`. -/
private lemma seqEquiv_mod_eq_of_dvd (g : GapSeq) {m a b : ℕ}
    (hdiv : ∀ k, m ∣ g.gap k) (hab : g.seqEquiv a b) : a % m = b % m := by
  simp only [seqEquiv] at hab
  rw [mod_eq_res_of_dvd g hdiv (x := a), mod_eq_res_of_dvd g hdiv (x := b), hab]

/-- Subtracting a multiple of the modulus preserves the residue class. -/
private lemma sub_mod_eq_of_dvd_base {B x m : ℕ} (hB : B % m = 0) (hx : B ≤ x) :
    (x - B) % m = x % m := by
  have : x % m = ((x - B) + B) % m := by rw [Nat.sub_add_cancel hx]
  rw [this, Nat.add_mod, hB, Nat.add_zero, Nat.mod_mod]

/-- **Eventually flat grasslands: sufficient condition.** -/
theorem symmetry_of_eventually_flat (g : GapSeq) {m p₀ T : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (hdiv : ∀ k, m ∣ g.gap k)
    (hT : g.base p₀ ≤ T) : IsTranslationSymmetry g T := by
  intro a b hab
  have haT : g.base p₀ ≤ a + T := Nat.le_trans hT (Nat.le_add_left _ _)
  have hbT : g.base p₀ ≤ b + T := Nat.le_trans hT (Nat.le_add_left _ _)
  simp only [seqEquiv] at hab ⊢
  rw [res_of_tail g htail haT, res_of_tail g htail hbT]
  have hmod : a % m = b % m :=
    seqEquiv_mod_eq_of_dvd g hdiv (by simp [seqEquiv]; exact hab)
  have hB : g.base p₀ % m = 0 :=
    Nat.mod_eq_zero_of_dvd (base_dvd_of_gap_dvd g hdiv p₀)
  rw [sub_mod_eq_of_dvd_base hB haT, sub_mod_eq_of_dvd_base hB hbT,
      Nat.add_mod a T, Nat.add_mod b T, hmod]

/-! ## Converse infrastructure -/

/-- Translated bases share one residue under a symmetry. -/
private lemma res_base_add_const_of_symmetry (g : GapSeq) {T : ℕ}
    (hs : IsTranslationSymmetry g T) (k j : ℕ) :
    g.res (g.base k + T) = g.res (g.base j + T) :=
  hs _ _ (by simp [seqEquiv])

/-- Translated bases in the flat tail have residue `T % m`. -/
private lemma res_base_add_tail (g : GapSeq) {m p₀ T : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (j : ℕ) :
    g.res (g.base (p₀ + j) + T) = T % m := by
  have hge : g.base p₀ ≤ g.base (p₀ + j) + T := by
    have := g.base_mono (Nat.le_add_right p₀ j); omega
  rw [res_of_tail g htail hge, base_add_of_tail g htail j]
  have : g.base p₀ + j * m + T - g.base p₀ = j * m + T := by omega
  rw [this, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]

/-- Every translated base has residue `T % m` under a symmetry. -/
private lemma res_base_add_eq_mod (g : GapSeq) {m p₀ T : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m)
    (hs : IsTranslationSymmetry g T) (k : ℕ) :
    g.res (g.base k + T) = T % m := by
  have h := res_base_add_const_of_symmetry g hs k p₀
  have ht : g.res (g.base p₀ + T) = T % m := by
    simpa using res_base_add_tail (T := T) g htail (j := 0)
  rwa [ht] at h

/-- Base recurrence at a positive index. -/
private lemma base_eq_pred_add (g : GapSeq) {p₀ : ℕ} (hp0 : 0 < p₀) :
    g.base p₀ = g.base (p₀ - 1) + g.gap (p₀ - 1) := by
  cases p₀ with
  | zero => cases hp0
  | succ p => rfl

/-- `(u + g) % m = u % m` forces `m ∣ g`. -/
private lemma dvd_of_add_mod_eq {u g m : ℕ} (hm : 0 < m)
    (h : (u + g) % m = u % m) : m ∣ g := by
  have h' : (u % m + g % m) % m = u % m := by
    rwa [Nat.add_mod] at h
  have hult : u % m < m := Nat.mod_lt _ hm
  have hglt : g % m < m := Nat.mod_lt _ hm
  have hg0 : g % m = 0 := by
    by_cases hlt : u % m + g % m < m
    · rw [Nat.mod_eq_of_lt hlt] at h'; omega
    · have hge : m ≤ u % m + g % m := Nat.le_of_not_gt hlt
      have hsub : u % m + g % m - m < m := by omega
      have hmod : (u % m + g % m) % m = u % m + g % m - m := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
      omega
  exact Nat.dvd_of_mod_eq_zero hg0

/-- From a symmetry with `B_{p₀} ≤ T`, every width is a multiple of `m`. -/
private lemma gap_dvd_of_symmetry_ge_base (g : GapSeq) {m p₀ T : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m)
    (hs : IsTranslationSymmetry g T) (hbase : g.base p₀ ≤ T) :
    ∀ k, m ∣ g.gap k := by
  intro k
  have hm := tail_gap_pos g htail
  have hge : g.base p₀ ≤ g.base k + T := Nat.le_trans hbase (Nat.le_add_left _ _)
  have hge' : g.base p₀ ≤ g.base (k + 1) + T := Nat.le_trans hbase (Nat.le_add_left _ _)
  have e1 : (g.base k + T - g.base p₀) % m = T % m := by
    have := res_base_add_eq_mod g htail hs k
    rwa [res_of_tail g htail hge] at this
  have e2 : (g.base (k + 1) + T - g.base p₀) % m = T % m := by
    have := res_base_add_eq_mod g htail hs (k + 1)
    rwa [res_of_tail g htail hge'] at this
  rw [base_succ] at e2
  set u := g.base k + T - g.base p₀
  have hsum : g.base k + g.gap k + T - g.base p₀ = u + g.gap k := by omega
  have heq : (u + g.gap k) % m = u % m := by
    rw [← hsum, e2, e1]
  exact dvd_of_add_mod_eq hm heq

/-- **Eventually flat grasslands, beyond the prefix.** For `T ≥ B_{p₀}`, the translation
by `T` is a symmetry iff the tail width `m` divides every width. -/
theorem eventually_flat_symmetry_iff_of_ge (g : GapSeq) {m p₀ T : ℕ}
    (htail : ∀ k, p₀ ≤ k → g.gap k = m) (hT : g.base p₀ ≤ T) :
    IsTranslationSymmetry g T ↔ ∀ k, m ∣ g.gap k :=
  ⟨fun hs => gap_dvd_of_symmetry_ge_base g htail hs hT,
   fun hdiv => symmetry_of_eventually_flat g htail hdiv hT⟩

end Grasslands
