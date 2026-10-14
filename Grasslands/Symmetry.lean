/-
  Grasslands/Symmetry.lean — which translations preserve the grassland equivalence.

  These results accompany the note Remainder Quotients of Interval Partitions of ℕ.

  The keystone of the frozen library (`GapSeq.translationInvariant_iff_flat`) says that EVERY
  translation preserves the equivalence iff the grassland is flat. Here, a single translation
  T: it fails as soon as two chapters satisfy T < g_k < g_j (so an unbounded grassland has
  no translation symmetry at all), and it holds for T = B_p whenever p is a period of g.
-/

import CampiOperazionistici.GrasslandFlatLimit

namespace Grasslands

open CampiOperazionistici
open GapSeq

/-- `T` is a translation symmetry of the grassland: it maps equivalent points to
equivalent points. -/
def IsTranslationSymmetry (g : GapSeq) (T : ℕ) : Prop :=
  ∀ a b : ℕ, g.seqEquiv a b → g.seqEquiv (a + T) (b + T)

/-- Under a period `p`, bases advance by a constant: `B_{k+p} = B_k + B_p`. -/
lemma base_add_of_period (g : GapSeq) {p : ℕ} (hp : ∀ k, g.gap (k + p) = g.gap k)
    (k : ℕ) : g.base (k + p) = g.base k + g.base p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_add, base_succ, base_succ, ih, hp k]
    omega

/-- Shifting by a period base preserves the chapter index up to `+ p`. -/
private lemma chap_add_base_of_period (g : GapSeq) {p : ℕ}
    (hp : ∀ k, g.gap (k + p) = g.gap k) (x : ℕ) :
    g.chap (x + g.base p) = g.chap x + p := by
  have hx := (g.chap_eq_iff (x := x) (k := g.chap x)).mp rfl
  apply g.chap_eq_of
  · -- B_{chap x + p} ≤ x + B_p
    rw [base_add_of_period g hp]
    omega
  · -- x + B_p < B_{chap x + p + 1}
    have hsucc : g.base (g.chap x + p + 1) = g.base (g.chap x + 1) + g.base p := by
      have := base_add_of_period g hp (g.chap x + 1)
      -- (chap x + 1) + p = chap x + p + 1
      rwa [Nat.add_assoc, Nat.add_comm 1 p, ← Nat.add_assoc] at this
    rw [hsucc]
    omega

/-- Shifting by a period base preserves residues. -/
private lemma res_add_base_of_period (g : GapSeq) {p : ℕ}
    (hp : ∀ k, g.gap (k + p) = g.gap k) (x : ℕ) :
    g.res (x + g.base p) = g.res x := by
  simp only [res, phi, chap_add_base_of_period g hp]
  rw [base_add_of_period g hp]
  have hle := g.base_chap_le x
  omega

/-- The obstruction: `T > 0` is not a symmetry if some chapters satisfy `T < g_k < g_j`.
(Witness: `B_k + (g_k − T)` and `B_j + (g_k − T)`.) -/
theorem not_symmetry_of_gap_lt (g : GapSeq) {T k j : ℕ} (hT : 0 < T)
    (hk : T < g.gap k) (hkj : g.gap k < g.gap j) : ¬ IsTranslationSymmetry g T := by
  intro hs
  set r := g.gap k - T with hr
  have hrpos : 0 < r := Nat.sub_pos_of_lt hk
  have hrk : r < g.gap k := Nat.sub_lt (lt_trans hT hk) hT
  have hrj : r < g.gap j := lt_trans hrk hkj
  set a := g.base k + r with ha
  set b := g.base j + r with hb
  have heq : g.seqEquiv a b := by
    simp only [seqEquiv, a, b, g.res_base_add hrk, g.res_base_add hrj]
  have hsym : g.seqEquiv (a + T) (b + T) := hs a b heq
  have haT : a + T = g.base (k + 1) := by
    rw [ha, base_succ, hr]; omega
  have hbT : b + T = g.base j + g.gap k := by
    rw [hb, hr]; omega
  have hres : g.res (a + T) = g.res (b + T) := hsym
  rw [haT, hbT, g.res_base, g.res_base_add hkj] at hres
  have := g.pos k
  omega

/-- Equivalently: a positive symmetry `T` bounds every gap that is not maximal. -/
theorem gap_le_of_symmetry (g : GapSeq) {T : ℕ} (hT : 0 < T)
    (hs : IsTranslationSymmetry g T) {k j : ℕ} (hkj : g.gap k < g.gap j) : g.gap k ≤ T := by
  by_contra h
  push_neg at h
  exact not_symmetry_of_gap_lt g hT h hkj hs

/-- An unbounded grassland has no positive translation symmetry. -/
theorem no_symmetry_of_unbounded (g : GapSeq) (hub : ∀ M : ℕ, ∃ k, M < g.gap k)
    {T : ℕ} (hT : 0 < T) : ¬ IsTranslationSymmetry g T := by
  intro hs
  obtain ⟨k, hk⟩ := hub T
  obtain ⟨j, hj⟩ := hub (g.gap k)
  exact not_symmetry_of_gap_lt g hT hk hj hs

/-- A period `p` of the gap sequence gives the symmetry `T = B_p`. -/
theorem symmetry_of_period (g : GapSeq) {p : ℕ} (hp : ∀ k, g.gap (k + p) = g.gap k) :
    IsTranslationSymmetry g (g.base p) := by
  intro a b hab
  simp only [seqEquiv] at hab ⊢
  rw [res_add_base_of_period g hp a, res_add_base_of_period g hp b, hab]

/-- In a flat grassland every translation is a symmetry (from the keystone). -/
theorem symmetry_of_flat (g : GapSeq) (hf : g.Flat) (T : ℕ) : IsTranslationSymmetry g T := by
  intro a b hab
  exact (translationInvariant_iff_flat g).mpr hf a b T hab

end Grasslands
