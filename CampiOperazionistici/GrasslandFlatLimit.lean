/-
  GrasslandFlatLimit.lean — CampiOperazionistici
  Author: Alessandro Sgarbi — 2026-06-10
  Paper: §2.5 (The Flat Limit) — planned new subsection of §2

  The deformation-theoretic backbone of the Operationistic Grassland
  framework.  A *global grassland* is the data of a positive gap sequence
  g : ℕ → ℕ₊; classical modular arithmetic ℤ/mℤ is the *flat* grassland
  (constant gaps).  This file proves:

  • the **representation theorem**: partition functions (P1)–(P3) are
    exactly the round-down projections of gap sequences
    (`IsPartitionFunction.exists_gapSeq`, `phi_isPartitionFunction`);
  • the **deformation functionals**: slope Δg, shift σ, curvature κ —
    first and mixed-second finite differences of the gap sequence —
    with the σ-cocycle and telescoping laws;
  • the **hierarchy**: Flat ⟺ σ ≡ 0, Affine ⟺ κ ≡ 0, Flat → Affine,
    with strictness witnesses (modular / radical n = 2 / radical n ≥ 3 /
    Mersenne);
  • the **flat-limit structure theorems**: in the flat case base, chap,
    res collapse to k·m, x/m, x % m, and the grassland equivalence is
    exactly congruence mod m;
  • the **keystone**: translation invariance (hence a quotient algebra)
    holds iff the grassland is flat (`translationInvariant_iff_flat`);
    in the flat case the quotient is canonically ℤ/mℤ
    (`Flat.quotEquivZMod`);
  • the **synchronization theorem**: two chapters are permanently
    equivalent under all common shifts iff their gap tails coincide
    (`seqEquiv_base_add_iff_sync`) — the general form of the First
    Jump / permanent separation dichotomy;
  • **bridges**: `radicalSeq n` recovers `irootN`/`radRem`/`aodEquiv`
    exactly; `constSeq m` recovers `x % m` and `Nat.ModEq`; per-chapter
    restriction recovers the §2 `GrasslandData`.  Corollaries:
    `aodEquiv n` is not a congruence for n ≥ 2; within the radical
    family, Flat ⟺ n = 1 and Affine ⟺ n ≤ 2.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.TranslationReencounter
import CampiOperazionistici.OperationisticGrassland

namespace CampiOperazionistici

/-! ## 1. Global grasslands: gap sequences -/

/-- A *global grassland*: an infinite sequence of positive chapter widths.
    The chapter bases are the partial sums; classical modular arithmetic is
    the constant sequence (`constSeq`). -/
structure GapSeq where
  /-- The width of chapter `k`. -/
  gap : ℕ → ℕ
  /-- All chapter widths are positive. -/
  pos : ∀ k, 0 < gap k

namespace GapSeq

/-- Chapter bases: partial sums of the gaps (`base 0 = 0`). -/
def base (g : GapSeq) : ℕ → ℕ
  | 0 => 0
  | k + 1 => base g k + g.gap k

@[simp] lemma base_zero (g : GapSeq) : g.base 0 = 0 := rfl

lemma base_succ (g : GapSeq) (k : ℕ) : g.base (k + 1) = g.base k + g.gap k := rfl

lemma base_lt_succ (g : GapSeq) (k : ℕ) : g.base k < g.base (k + 1) := by
  have := g.pos k; rw [base_succ]; omega

lemma base_strictMono (g : GapSeq) : StrictMono g.base :=
  strictMono_nat_of_lt_succ g.base_lt_succ

lemma base_mono (g : GapSeq) {k j : ℕ} (h : k ≤ j) : g.base k ≤ g.base j :=
  g.base_strictMono.monotone h

lemma le_base (g : GapSeq) (k : ℕ) : k ≤ g.base k := by
  induction k with
  | zero => simp
  | succ k ih => have := g.pos k; rw [base_succ]; omega

/-- The chapter index of `x`: the largest `k` with `base k ≤ x`. -/
def chap (g : GapSeq) (x : ℕ) : ℕ :=
  Nat.findGreatest (fun k => g.base k ≤ x) x

lemma base_chap_le (g : GapSeq) (x : ℕ) : g.base (g.chap x) ≤ x :=
  Nat.findGreatest_spec (P := fun k => g.base k ≤ x) (Nat.zero_le x) (by simp)

lemma chap_le_self (g : GapSeq) (x : ℕ) : g.chap x ≤ x :=
  Nat.findGreatest_le x

lemma lt_base_chap_succ (g : GapSeq) (x : ℕ) : x < g.base (g.chap x + 1) := by
  by_contra hcon
  push_neg at hcon
  have hle : g.chap x + 1 ≤ x := le_trans (g.le_base _) hcon
  exact Nat.findGreatest_is_greatest (P := fun k => g.base k ≤ x)
    (Nat.lt_succ_self _) hle hcon

/-- Uniqueness: `chap x` is the unique `k` with `base k ≤ x < base (k+1)`. -/
lemma chap_eq_of (g : GapSeq) {x k : ℕ} (h₁ : g.base k ≤ x)
    (h₂ : x < g.base (k + 1)) : g.chap x = k := by
  rcases lt_trichotomy (g.chap x) k with h | h | h
  · have hb : g.base (g.chap x + 1) ≤ g.base k := g.base_mono (by omega)
    have := g.lt_base_chap_succ x
    omega
  · exact h
  · have hb : g.base (k + 1) ≤ g.base (g.chap x) := g.base_mono (by omega)
    have := g.base_chap_le x
    omega

lemma chap_mono (g : GapSeq) {x y : ℕ} (h : x ≤ y) : g.chap x ≤ g.chap y := by
  have h₁ : g.base (g.chap x) ≤ y := le_trans (g.base_chap_le x) h
  have h₂ : g.chap x ≤ y := le_trans (g.chap_le_self x) h
  exact Nat.le_findGreatest h₂ h₁

/-- The grassland projection φ: round `x` down to its chapter base. -/
def phi (g : GapSeq) (x : ℕ) : ℕ := g.base (g.chap x)

/-- The grassland residue: offset of `x` inside its chapter. -/
def res (g : GapSeq) (x : ℕ) : ℕ := x - g.phi x

lemma phi_le (g : GapSeq) (x : ℕ) : g.phi x ≤ x := g.base_chap_le x

lemma phi_add_res (g : GapSeq) (x : ℕ) : g.phi x + g.res x = x := by
  have := g.phi_le x
  simp only [res]
  omega

lemma res_lt_gap (g : GapSeq) (x : ℕ) : g.res x < g.gap (g.chap x) := by
  have h₁ := g.lt_base_chap_succ x
  have h₂ := g.base_chap_le x
  rw [base_succ] at h₁
  simp only [res, phi]
  omega

/-- Membership of an explicit chapter offset. -/
lemma chap_base_add (g : GapSeq) {k t : ℕ} (ht : t < g.gap k) :
    g.chap (g.base k + t) = k :=
  g.chap_eq_of (Nat.le_add_right _ _) (by rw [base_succ]; omega)

lemma res_base_add (g : GapSeq) {k t : ℕ} (ht : t < g.gap k) :
    g.res (g.base k + t) = t := by
  simp [res, phi, g.chap_base_add ht]

@[simp] lemma chap_base (g : GapSeq) (k : ℕ) : g.chap (g.base k) = k := by
  have := g.pos k
  simpa using g.chap_base_add (k := k) (t := 0) (by omega)

@[simp] lemma res_base (g : GapSeq) (k : ℕ) : g.res (g.base k) = 0 := by
  have := g.pos k
  simpa using g.res_base_add (k := k) (t := 0) (by omega)

/-- (P1) The projection is idempotent. -/
lemma phi_idem (g : GapSeq) (x : ℕ) : g.phi (g.phi x) = g.phi x := by
  simp [phi]

/-- (P3) Chapter membership: the fiber over `base k` is the interval
    `[base k, base (k+1))`. -/
lemma chap_eq_iff (g : GapSeq) {x k : ℕ} :
    g.chap x = k ↔ g.base k ≤ x ∧ x < g.base (k + 1) := by
  constructor
  · rintro rfl
    exact ⟨g.base_chap_le x, g.lt_base_chap_succ x⟩
  · rintro ⟨h₁, h₂⟩
    exact g.chap_eq_of h₁ h₂

end GapSeq

/-! ## 2. Partition functions: axioms (P1)–(P3) and the representation theorem

  A *partition function* (paper, Definition 2.1) is an idempotent projection
  whose nonempty fibers are finite intervals anchored at their base.  The
  representation theorem below classifies them completely: they are exactly
  the projections `GapSeq.phi` of gap sequences.  The data of an
  operationistic grassland is therefore *equivalent* to the data of its
  gap sequence — the "metric" from which all deformation functionals
  (slope, σ, κ) are derived. -/

/-- Axioms (P1)–(P3): idempotence, projection, chapter finiteness. -/
structure IsPartitionFunction (φ : ℕ → ℕ) : Prop where
  /-- (P1) idempotence. -/
  idem : ∀ x, φ (φ x) = φ x
  /-- (P2) projection. -/
  proj : ∀ x, φ x ≤ x
  /-- (P3) every nonempty fiber is a finite interval `[b, b + w)`, `w ≥ 1`. -/
  fiber : ∀ b, (∃ x, φ x = b) →
    ∃ w, 0 < w ∧ ∀ x, (φ x = b ↔ b ≤ x ∧ x < b + w)

/-- Forward direction: the projection of every gap sequence satisfies
    (P1)–(P3). -/
theorem phi_isPartitionFunction (g : GapSeq) : IsPartitionFunction g.phi := by
  refine ⟨g.phi_idem, g.phi_le, ?_⟩
  rintro b ⟨x, rfl⟩
  refine ⟨g.gap (g.chap x), g.pos _, fun y => ?_⟩
  constructor
  · intro hy
    have hinj : g.chap y = g.chap x := g.base_strictMono.injective hy
    refine ⟨?_, ?_⟩
    · rw [← hy]; exact g.phi_le y
    · have h3 := g.lt_base_chap_succ y
      rw [GapSeq.base_succ, hinj] at h3
      simpa [GapSeq.phi] using h3
  · rintro ⟨h₁, h₂⟩
    have hc : g.chap y = g.chap x := by
      apply g.chap_eq_of
      · exact h₁
      · rw [GapSeq.base_succ]; exact h₂
    simp [GapSeq.phi, hc]

/-- Iterated bases of a width assignment: the candidate base sequence used
    in the representation theorem. -/
def iterBase (W : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => iterBase W k + W (iterBase W k)

/-- **Representation theorem (classification of partition functions).**
    Every map satisfying (P1)–(P3) is the projection of a gap sequence:
    partition functions are exactly the round-down maps onto base sets with
    positive widths.  Together with `phi_isPartitionFunction` this
    identifies operationistic grasslands with gap sequences. -/
theorem IsPartitionFunction.exists_gapSeq {φ : ℕ → ℕ}
    (pf : IsPartitionFunction φ) : ∃ g : GapSeq, ∀ x, φ x = g.phi x := by
  classical
  have h0 : φ 0 = 0 := Nat.le_zero.mp (pf.proj 0)
  -- the fiber over a fixed point, with chosen width
  have hW : ∀ b, φ b = b → ∃ w, 0 < w ∧ ∀ x, (φ x = b ↔ b ≤ x ∧ x < b + w) :=
    fun b hb => pf.fiber b ⟨b, hb⟩
  choose W hWpos hWspec using hW
  -- the right end of a fiber is again a fixed point
  have hnext : ∀ b (hb : φ b = b), φ (b + W b hb) = b + W b hb := by
    intro b hb
    set w := W b hb with hwdef
    set y := b + w with hydef
    have hwpos : 0 < w := hWpos b hb
    have hfix' : φ (φ y) = φ y := pf.idem y
    obtain ⟨w', hw'pos, hw'spec⟩ := pf.fiber (φ y) ⟨y, rfl⟩
    have hy_in : φ y ≤ y ∧ y < φ y + w' := (hw'spec y).mp rfl
    rcases lt_trichotomy (φ y) b with hlt | heq | hgt
    · -- b would lie in the fiber of φ y, forcing b = φ y < b
      have hb_in : φ b = φ y :=
        (hw'spec b).mpr ⟨Nat.le_of_lt hlt, by omega⟩
      omega
    · -- y would lie in the fiber of b, contradicting y = b + w
      have hmem : b ≤ y ∧ y < b + W b hb := (hWspec b hb y).mp heq
      omega
    · -- φ y is a fixed point in (b, y]; it cannot be < b + w
      have hge : b + w ≤ φ y := by
        by_contra hno
        push_neg at hno
        have hmem : φ (φ y) = b :=
          (hWspec b hb (φ y)).mpr ⟨Nat.le_of_lt hgt, by omega⟩
        rw [hfix'] at hmem
        omega
      have hyy : φ y = y := le_antisymm hy_in.1 (by omega)
      exact hyy
  -- totalise the width over all of ℕ
  set Wt : ℕ → ℕ := fun b => if hb : φ b = b then W b hb else 1 with hWt_def
  have hWt_pos : ∀ b, 0 < Wt b := by
    intro b
    rw [hWt_def]
    by_cases hb : φ b = b
    · simp only [dif_pos hb]; exact hWpos b hb
    · simp only [dif_neg hb]; omega
  have hWt_fix : ∀ b (hb : φ b = b), Wt b = W b hb := by
    intro b hb
    rw [hWt_def]
    exact dif_pos hb
  -- every iterated base is a fixed point
  have hiter : ∀ k, φ (iterBase Wt k) = iterBase Wt k := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hstep : iterBase Wt (k + 1) = iterBase Wt k + W (iterBase Wt k) ih := by
        show iterBase Wt k + Wt (iterBase Wt k) = _
        rw [hWt_fix _ ih]
      rw [hstep]
      exact hnext _ ih
  -- assemble the gap sequence and conclude
  let g : GapSeq := ⟨fun k => Wt (iterBase Wt k), fun _ => hWt_pos _⟩
  have hbase : ∀ k, g.base k = iterBase Wt k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [GapSeq.base_succ, ih]; rfl
  refine ⟨g, fun x => ?_⟩
  have h₁ : g.base (g.chap x) ≤ x := g.base_chap_le x
  have h₂ : x < g.base (g.chap x + 1) := g.lt_base_chap_succ x
  rw [GapSeq.base_succ] at h₂
  have hfixc : φ (iterBase Wt (g.chap x)) = iterBase Wt (g.chap x) :=
    hiter (g.chap x)
  have hspec := hWspec (iterBase Wt (g.chap x)) hfixc x
  show φ x = g.base (g.chap x)
  rw [hbase] at h₁ h₂ ⊢
  have hgapc : g.gap (g.chap x) = Wt (iterBase Wt (g.chap x)) := rfl
  rw [hgapc, hWt_fix _ hfixc] at h₂
  exact hspec.mpr ⟨h₁, h₂⟩

-- Sanity checks for the global projection (radical degree 2 instance built later).
#eval iterBase (fun b => b + 1) 3   -- 0, 1, 3, 7 → expected: 7

namespace GapSeq

/-! ## 3. Deformation functionals: slope, shift σ, curvature κ

  The gap sequence plays the role of a discrete metric; its finite
  differences are the deformation data of the grassland:

  * `slope`  = first difference Δg            ("connection coefficient")
  * `sigma`  = inter-chapter shift            (general subtraction shift)
  * `kappa`  = mixed second difference        ("curvature")

  All three vanish identically on the flat (modular) grassland; their
  vanishing loci stratify the hierarchy proved in §4. -/

/-- First finite difference of the gap sequence (the *slope* Δg). -/
def slope (g : GapSeq) (k : ℕ) : ℤ := (g.gap (k + 1) : ℤ) - g.gap k

/-- Inter-chapter shift σ: the general form of the subtraction shift. -/
def sigma (g : GapSeq) (k h : ℕ) : ℤ := (g.gap h : ℤ) - g.gap k

/-- Curvature κ: the mixed second finite difference of the gap sequence,
    `κ(k,h,j) = σ(h, h+j) − σ(k, k+j)`. -/
def kappa (g : GapSeq) (k h j : ℕ) : ℤ := g.sigma h (h + j) - g.sigma k (k + j)

@[simp] lemma sigma_self (g : GapSeq) (k : ℕ) : g.sigma k k = 0 := by
  simp [sigma]

lemma sigma_symm (g : GapSeq) (k h : ℕ) : g.sigma h k = -g.sigma k h := by
  simp [sigma]

/-- σ is a 1-cocycle on chapter indices. -/
theorem sigma_cocycle (g : GapSeq) (k h l : ℕ) :
    g.sigma k h + g.sigma h l = g.sigma k l := by
  simp only [sigma]; ring

/-- Telescoping: σ along `j` steps is the sum of the slopes. -/
theorem sigma_eq_sum_slope (g : GapSeq) (k j : ℕ) :
    g.sigma k (k + j) = ∑ i ∈ Finset.range j, g.slope (k + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih,
        ← g.sigma_cocycle k (k + j) (k + (j + 1))]
    congr 1

/-- κ at adjacent chapters with unit shift is the second difference of
    the gap sequence. -/
lemma kappa_succ (g : GapSeq) (k : ℕ) :
    g.kappa k (k + 1) 1 = g.slope (k + 1) - g.slope k := by
  simp only [kappa, sigma, slope]

/-! ## 4. The flat/affine hierarchy

  * Level 0 (**flat**): constant gaps — classical modular arithmetic.
    Characterised by σ ≡ 0 (equivalently Δg ≡ 0).
  * Level 1 (**affine**): constant slope — e.g. the radical degree 2.
    Characterised by κ ≡ 0.
  * Level 2 (**curved**): κ ≢ 0 — e.g. radical degree ≥ 3, Mersenne.

  Flat ⟹ Affine, and both inclusions are strict (witnesses in §8). -/

/-- A grassland is *flat* when all chapters have the same width. -/
def Flat (g : GapSeq) : Prop := ∀ k, g.gap k = g.gap 0

/-- A grassland is *affine* when its slope is constant. -/
def Affine (g : GapSeq) : Prop := ∀ k, g.slope k = g.slope 0

/-- Level-0 characterisation: flat ⟺ all shifts vanish. -/
theorem flat_iff_sigma_eq_zero (g : GapSeq) :
    g.Flat ↔ ∀ k h, g.sigma k h = 0 := by
  constructor
  · intro hf k h
    simp [sigma, hf k, hf h]
  · intro hs k
    have h := hs 0 k
    simp only [sigma, sub_eq_zero, Nat.cast_inj] at h
    exact h

/-- Level-0 characterisation, differential form: flat ⟺ zero slope. -/
theorem flat_iff_slope_eq_zero (g : GapSeq) :
    g.Flat ↔ ∀ k, g.slope k = 0 := by
  constructor
  · intro hf k
    simp [slope, hf k, hf (k + 1)]
  · intro hs k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := hs k
      simp only [slope, sub_eq_zero, Nat.cast_inj] at h
      omega

/-- Level-1 characterisation: affine ⟺ the curvature vanishes. -/
theorem affine_iff_kappa_eq_zero (g : GapSeq) :
    g.Affine ↔ ∀ k h j, g.kappa k h j = 0 := by
  constructor
  · intro ha k h j
    have hsum : ∀ m : ℕ, g.sigma m (m + j) = (j : ℤ) * g.slope 0 := by
      intro m
      rw [g.sigma_eq_sum_slope m j,
          Finset.sum_congr rfl fun i _ => ha (m + i),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp [kappa, hsum]
  · intro hk k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := hk k (k + 1) 1
      rw [kappa_succ] at h
      omega

/-- The hierarchy: every flat grassland is affine. -/
theorem Flat.affine {g : GapSeq} (hf : g.Flat) : g.Affine := by
  intro k
  have h := (g.flat_iff_slope_eq_zero).mp hf
  rw [h k, h 0]

/-! ## 5. The grassland equivalence -/

/-- The grassland equivalence: equal residues (the global generalisation
    of `aodEquiv`). -/
def seqEquiv (g : GapSeq) (a b : ℕ) : Prop := g.res a = g.res b

theorem seqEquiv_refl (g : GapSeq) (a : ℕ) : g.seqEquiv a a := rfl

theorem seqEquiv_symm {g : GapSeq} {a b : ℕ} (h : g.seqEquiv a b) :
    g.seqEquiv b a := h.symm

theorem seqEquiv_trans {g : GapSeq} {a b c : ℕ} (h₁ : g.seqEquiv a b)
    (h₂ : g.seqEquiv b c) : g.seqEquiv a c := h₁.trans h₂

/-- The grassland equivalence as a setoid. -/
def seqSetoid (g : GapSeq) : Setoid ℕ :=
  ⟨g.seqEquiv, ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩⟩

/-! ## 6. Flat structure: collapse to classical modular arithmetic

  On a flat grassland with width `m = gap 0`, the three structural maps
  collapse to the classical ones: `base k = k·m`, `chap x = x / m`,
  `res x = x % m`, and the grassland equivalence is congruence mod `m`.
  This is the *compatibility-at-the-limit* part of the extension claim,
  in its strong form: not only do the operations agree, every structural
  invariant degenerates to its classical value. -/

theorem Flat.base_eq {g : GapSeq} (hf : g.Flat) (k : ℕ) :
    g.base k = k * g.gap 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [base_succ, ih, hf k]
    ring

theorem Flat.chap_eq {g : GapSeq} (hf : g.Flat) (x : ℕ) :
    g.chap x = x / g.gap 0 := by
  have hm : 0 < g.gap 0 := g.pos 0
  apply g.chap_eq_of
  · rw [hf.base_eq]
    exact Nat.div_mul_le_self x _
  · rw [hf.base_eq]
    have h1 : x % g.gap 0 < g.gap 0 := Nat.mod_lt _ hm
    have h2 : g.gap 0 * (x / g.gap 0) + x % g.gap 0 = x := Nat.div_add_mod x _
    calc x = g.gap 0 * (x / g.gap 0) + x % g.gap 0 := h2.symm
      _ < g.gap 0 * (x / g.gap 0) + g.gap 0 := by omega
      _ = (x / g.gap 0 + 1) * g.gap 0 := by ring

theorem Flat.res_eq_mod {g : GapSeq} (hf : g.Flat) (x : ℕ) :
    g.res x = x % g.gap 0 := by
  have h2 : x / g.gap 0 * g.gap 0 + x % g.gap 0 = x := Nat.div_add_mod' x _
  simp only [GapSeq.res, GapSeq.phi, hf.chap_eq, hf.base_eq]
  exact Nat.sub_eq_of_eq_add (by rw [Nat.add_comm]; exact h2.symm)

/-- On a flat grassland the equivalence is exactly congruence mod `m`. -/
theorem Flat.seqEquiv_iff_modEq {g : GapSeq} (hf : g.Flat) (a b : ℕ) :
    g.seqEquiv a b ↔ a ≡ b [MOD g.gap 0] := by
  simp only [GapSeq.seqEquiv, hf.res_eq_mod]
  exact Iff.rfl

/-- Flat congruence for addition. -/
theorem Flat.seqEquiv_add {g : GapSeq} (hf : g.Flat) {a a' b b' : ℕ}
    (ha : g.seqEquiv a a') (hb : g.seqEquiv b b') :
    g.seqEquiv (a + b) (a' + b') := by
  rw [hf.seqEquiv_iff_modEq] at ha hb ⊢
  exact ha.add hb

/-- Flat congruence for multiplication. -/
theorem Flat.seqEquiv_mul {g : GapSeq} (hf : g.Flat) {a a' b b' : ℕ}
    (ha : g.seqEquiv a a') (hb : g.seqEquiv b b') :
    g.seqEquiv (a * b) (a' * b') := by
  rw [hf.seqEquiv_iff_modEq] at ha hb ⊢
  exact ha.mul hb

/-- Flat landing congruence: residues add modulo `m`, unconditionally —
    the no-overflow condition is vacuous in the flat limit. -/
theorem Flat.res_add {g : GapSeq} (hf : g.Flat) (a b : ℕ) :
    g.res (a + b) = (g.res a + g.res b) % g.gap 0 := by
  simp [hf.res_eq_mod, Nat.add_mod]

/-! ## 7. The keystone: congruence ⟺ flat

  In ℤ/mℤ the partition is compatible with the ambient operations of ℕ;
  this single property is what makes the *quotient itself* a ring.  The
  keystone theorem shows this compatibility characterises flatness: the
  moment two chapters have different widths, a common shift breaks the
  equivalence.  Modular arithmetic is therefore *exactly* the vanishing
  locus of the deformation — the Level-0 stratum — and the impossibility
  of a quotient algebra in the curved case is a curvature statement, not
  a defect of the framework. -/

/-- **Keystone (flat-limit theorem).**  The grassland equivalence is
    translation-invariant iff the grassland is flat. -/
theorem translationInvariant_iff_flat (g : GapSeq) :
    (∀ a b m, g.seqEquiv a b → g.seqEquiv (a + m) (b + m)) ↔ g.Flat := by
  constructor
  · intro htr
    by_contra hnf
    obtain ⟨p, q, hpq⟩ : ∃ p q, g.gap p < g.gap q := by
      simp only [Flat, not_forall] at hnf
      obtain ⟨k, hk⟩ := hnf
      rcases Nat.lt_or_ge (g.gap k) (g.gap 0) with h | h
      · exact ⟨k, 0, h⟩
      · exact ⟨0, k, by omega⟩
    have h1 : g.seqEquiv (g.base p) (g.base q) := by
      simp [seqEquiv]
    have h2 : g.res (g.base p + g.gap p) = g.res (g.base q + g.gap p) :=
      htr _ _ (g.gap p) h1
    have e1 : g.res (g.base p + g.gap p) = 0 := by
      rw [← base_succ]
      exact g.res_base _
    have e2 : g.res (g.base q + g.gap p) = g.gap p := g.res_base_add hpq
    have hp := g.pos p
    rw [e1, e2] at h2
    omega
  · intro hf a b m hab
    rw [hf.seqEquiv_iff_modEq] at hab ⊢
    exact hab.add_right m

/-- Full congruence form of the keystone: the equivalence is a congruence
    for addition iff the grassland is flat. -/
theorem addCongruence_iff_flat (g : GapSeq) :
    (∀ a a' b b', g.seqEquiv a a' → g.seqEquiv b b' →
      g.seqEquiv (a + b) (a' + b')) ↔ g.Flat := by
  constructor
  · intro hc
    rw [← translationInvariant_iff_flat]
    intro a b m hab
    exact hc a b m m hab (seqEquiv_refl g m)
  · intro hf _ _ _ _ ha hb
    exact hf.seqEquiv_add ha hb

/-- For a non-flat grassland, no representative-wise operation descends:
    the equivalence is not even translation-invariant. -/
theorem not_flat_not_translationInvariant {g : GapSeq} (h : ¬ g.Flat) :
    ¬ ∀ a b m, g.seqEquiv a b → g.seqEquiv (a + m) (b + m) :=
  fun htr => h ((translationInvariant_iff_flat g).mp htr)

/-! ## 8. The flat quotient is ℤ/mℤ -/

/-- The quotient of ℕ by the grassland equivalence. -/
abbrev SeqQuot (g : GapSeq) := Quotient g.seqSetoid

/-- In the flat case, addition descends to the quotient. -/
def Flat.quotAdd {g : GapSeq} (hf : g.Flat) :
    g.SeqQuot → g.SeqQuot → g.SeqQuot :=
  Quotient.map₂ (· + ·) (fun _ _ ha _ _ hb => hf.seqEquiv_add ha hb)

/-- In the flat case, multiplication descends to the quotient. -/
def Flat.quotMul {g : GapSeq} (hf : g.Flat) :
    g.SeqQuot → g.SeqQuot → g.SeqQuot :=
  Quotient.map₂ (· * ·) (fun _ _ ha _ _ hb => hf.seqEquiv_mul ha hb)

/-- **The flat quotient theorem**: for a flat grassland the quotient is
    canonically `ZMod m` (the bijection; the homomorphism laws are
    `Flat.quotEquivZMod_add` / `Flat.quotEquivZMod_mul`). -/
def Flat.quotEquivZMod {g : GapSeq} (hf : g.Flat) :
    g.SeqQuot ≃ ZMod (g.gap 0) :=
  haveI : NeZero (g.gap 0) := ⟨(g.pos 0).ne'⟩
  { toFun := Quotient.lift (fun x : ℕ => (x : ZMod (g.gap 0)))
      (fun a b hab => by
        rw [ZMod.natCast_eq_natCast_iff]
        exact (hf.seqEquiv_iff_modEq a b).mp hab)
    invFun := fun z => Quotient.mk g.seqSetoid z.val
    left_inv := fun q => by
      induction q using Quotient.inductionOn with
      | h a =>
        apply Quotient.sound
        show g.seqEquiv (ZMod.val ((a : ℕ) : ZMod (g.gap 0))) a
        rw [hf.seqEquiv_iff_modEq, ZMod.val_natCast]
        exact Nat.mod_modEq a _
    right_inv := fun z => ZMod.natCast_rightInverse z }

/-- The flat quotient bijection is additive. -/
theorem Flat.quotEquivZMod_add {g : GapSeq} (hf : g.Flat)
    (q₁ q₂ : g.SeqQuot) :
    hf.quotEquivZMod (hf.quotAdd q₁ q₂) =
      hf.quotEquivZMod q₁ + hf.quotEquivZMod q₂ := by
  induction q₁ using Quotient.inductionOn with
  | h a =>
    induction q₂ using Quotient.inductionOn with
    | h b =>
      show ((a + b : ℕ) : ZMod (g.gap 0)) = (a : ZMod (g.gap 0)) + b
      push_cast
      ring

/-- The flat quotient bijection is multiplicative. -/
theorem Flat.quotEquivZMod_mul {g : GapSeq} (hf : g.Flat)
    (q₁ q₂ : g.SeqQuot) :
    hf.quotEquivZMod (hf.quotMul q₁ q₂) =
      hf.quotEquivZMod q₁ * hf.quotEquivZMod q₂ := by
  induction q₁ using Quotient.inductionOn with
  | h a =>
    induction q₂ using Quotient.inductionOn with
    | h b =>
      show ((a * b : ℕ) : ZMod (g.gap 0)) = (a : ZMod (g.gap 0)) * b
      push_cast
      ring

/-! ## 9. Windows, breaks, and the synchronization theorem -/

/-- Common-shift window (general First Jump, persistence direction):
    while both sides stay inside their chapters, equivalence persists. -/
theorem seqEquiv_window (g : GapSeq) {k h t m : ℕ}
    (hk : t + m < g.gap k) (hh : t + m < g.gap h) :
    g.seqEquiv (g.base k + t + m) (g.base h + t + m) := by
  show g.res _ = g.res _
  rw [Nat.add_assoc, Nat.add_assoc, g.res_base_add hk, g.res_base_add hh]

/-- General First Jump (break): if chapter `k` is strictly narrower than
    chapter `h`, the common shift `m* = gap k − t` breaks the equivalence.
    -- Example: k = 0, h = 1, t = 0 in the radical degree-2 grassland. -/
theorem first_break (g : GapSeq) {k h t : ℕ} (hkh : g.gap k < g.gap h)
    (ht : t ≤ g.gap k) :
    ¬ g.seqEquiv (g.base k + t + (g.gap k - t))
        (g.base h + t + (g.gap k - t)) := by
  have hp := g.pos k
  have e1 : g.base k + t + (g.gap k - t) = g.base (k + 1) := by
    rw [base_succ]; omega
  have e2 : g.base h + t + (g.gap k - t) = g.base h + g.gap k := by omega
  intro hcon
  have hcon' : g.res (g.base k + t + (g.gap k - t)) =
      g.res (g.base h + t + (g.gap k - t)) := hcon
  rw [e1, e2, g.res_base, g.res_base_add hkh] at hcon'
  omega

/-- Under gap-tail synchronization up to `N`, bases advance in parallel. -/
lemma base_add_sync_of_lt {g : GapSeq} {k h N : ℕ}
    (hs : ∀ i, i < N → g.gap (k + i) = g.gap (h + i)) :
    ∀ i, i ≤ N → g.base (k + i) + g.base h = g.base (h + i) + g.base k := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    omega
  | succ i ih =>
    intro hiN
    have h1 := ih (by omega)
    have h2 := hs i (by omega)
    rw [show k + (i + 1) = (k + i) + 1 from rfl,
        show h + (i + 1) = (h + i) + 1 from rfl,
        base_succ, base_succ]
    omega

/-- **Synchronization theorem** (general permanent-equivalence dichotomy).
    Two chapters are equivalent under *all* common shifts iff their gap
    tails coincide.  In a flat grassland the right side always holds — no
    First Jump ever happens; in the radical grassland of degree ≥ 2 it
    never does (Growing Frontier), so every pair of distinct chapters is
    eventually separated. -/
theorem seqEquiv_base_add_iff_sync (g : GapSeq) (k h : ℕ) :
    (∀ u, g.seqEquiv (g.base k + u) (g.base h + u)) ↔
      ∀ i, g.gap (k + i) = g.gap (h + i) := by
  constructor
  · intro hall
    by_contra hns
    push_neg at hns
    have hex : ∃ i, g.gap (k + i) ≠ g.gap (h + i) := hns
    have hi₀ : g.gap (k + Nat.find hex) ≠ g.gap (h + Nat.find hex) :=
      Nat.find_spec hex
    have hmin : ∀ j, j < Nat.find hex → g.gap (k + j) = g.gap (h + j) :=
      fun j hj => not_not.mp (Nat.find_min hex hj)
    set i₀ := Nat.find hex
    have hD := base_add_sync_of_lt (g := g) (k := k) (h := h) (N := i₀)
      hmin i₀ le_rfl
    have hbk : g.base k ≤ g.base (k + i₀) := g.base_mono (by omega)
    have hbh : g.base h ≤ g.base (h + i₀) := g.base_mono (by omega)
    rcases Nat.lt_or_ge (g.gap (k + i₀)) (g.gap (h + i₀)) with hlt | hge
    · -- u sends the k-side onto the next base, the h-side strictly inside
      have hku : g.base k + ((g.base (k + i₀) - g.base k) + g.gap (k + i₀))
          = g.base (k + i₀ + 1) := by
        rw [base_succ]; omega
      have hhu : g.base h + ((g.base (k + i₀) - g.base k) + g.gap (k + i₀))
          = g.base (h + i₀) + g.gap (k + i₀) := by omega
      have hres : g.res (g.base k + ((g.base (k + i₀) - g.base k) + g.gap (k + i₀)))
          = g.res (g.base h + ((g.base (k + i₀) - g.base k) + g.gap (k + i₀))) :=
        hall _
      rw [hku, hhu, g.res_base, g.res_base_add hlt] at hres
      have := g.pos (k + i₀)
      omega
    · have hlt' : g.gap (h + i₀) < g.gap (k + i₀) := by omega
      have hhu : g.base h + ((g.base (h + i₀) - g.base h) + g.gap (h + i₀))
          = g.base (h + i₀ + 1) := by
        rw [base_succ]; omega
      have hku : g.base k + ((g.base (h + i₀) - g.base h) + g.gap (h + i₀))
          = g.base (k + i₀) + g.gap (h + i₀) := by omega
      have hres : g.res (g.base k + ((g.base (h + i₀) - g.base h) + g.gap (h + i₀)))
          = g.res (g.base h + ((g.base (h + i₀) - g.base h) + g.gap (h + i₀))) :=
        hall _
      rw [hku, hhu, g.res_base, g.res_base_add hlt'] at hres
      have := g.pos (h + i₀)
      omega
  · intro hs u
    have hD : ∀ i, g.base (k + i) + g.base h = g.base (h + i) + g.base k :=
      fun i => base_add_sync_of_lt (fun j _ => hs j) i le_rfl
    have hck : k ≤ g.chap (g.base k + u) := by
      have h := g.chap_mono (Nat.le_add_right (g.base k) u)
      rwa [g.chap_base] at h
    obtain ⟨i, hci⟩ : ∃ i, g.chap (g.base k + u) = k + i :=
      ⟨_, (Nat.add_sub_cancel' hck).symm⟩
    have h₁ : g.base (k + i) ≤ g.base k + u := by
      have h := g.base_chap_le (g.base k + u)
      rwa [hci] at h
    have h₂ : g.base k + u < g.base (k + i + 1) := by
      have h := g.lt_base_chap_succ (g.base k + u)
      rwa [hci] at h
    have hD1 := hD i
    have hD2 := hD (i + 1)
    rw [show k + (i + 1) = (k + i) + 1 from rfl,
        show h + (i + 1) = (h + i) + 1 from rfl] at hD2
    have hch : g.chap (g.base h + u) = h + i := by
      apply g.chap_eq_of
      · omega
      · omega
    show g.res _ = g.res _
    simp only [res, phi, hci, hch]
    omega

/-- **No breaks ⟺ flat**: a grassland has no First Jump anywhere iff it
    is flat — the global form of the keystone theorem. -/
theorem flat_iff_no_breaks (g : GapSeq) :
    g.Flat ↔ ∀ k h u, g.seqEquiv (g.base k + u) (g.base h + u) := by
  constructor
  · intro hf k h u
    exact (g.seqEquiv_base_add_iff_sync k h).mpr
      (fun i => by rw [hf (k + i), hf (h + i)]) u
  · intro hnb k
    have h := (g.seqEquiv_base_add_iff_sync k 0).mp (fun u => hnb k 0 u) 0
    simpa using h

end GapSeq

/-! ## 10. Instances: flat, radical, Mersenne -/

/-- The flat grassland: constant width `m` — classical modular arithmetic
    as a global gap sequence. -/
def constSeq (m : ℕ) (hm : 0 < m) : GapSeq := ⟨fun _ => m, fun _ => hm⟩

theorem constSeq_flat (m : ℕ) (hm : 0 < m) : (constSeq m hm).Flat :=
  fun _ => rfl

/-- The flat residue is the classical remainder. -/
theorem constSeq_res (m : ℕ) (hm : 0 < m) (x : ℕ) :
    (constSeq m hm).res x = x % m :=
  (constSeq_flat m hm).res_eq_mod x

/-- The flat grassland equivalence is classical congruence mod `m`:
    the Lean-verified form of "ℤ/mℤ is the flat grassland". -/
theorem constSeq_seqEquiv_iff (m : ℕ) (hm : 0 < m) (a b : ℕ) :
    (constSeq m hm).seqEquiv a b ↔ a ≡ b [MOD m] :=
  (constSeq_flat m hm).seqEquiv_iff_modEq a b

/-- The radical grassland of degree `n` as a global gap sequence. -/
def radicalSeq (n : ℕ) (hn : n ≠ 0) : GapSeq :=
  ⟨fun k => gap n k, fun k => gap_pos' n k hn⟩

@[simp] theorem radicalSeq_gap (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    (radicalSeq n hn).gap k = gap n k := rfl

/-- The bases of the radical grassland are the perfect n-th powers. -/
theorem radicalSeq_base (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    (radicalSeq n hn).base k = k ^ n := by
  induction k with
  | zero => simp [Nat.zero_pow (Nat.pos_of_ne_zero hn)]
  | succ k ih =>
    rw [GapSeq.base_succ, ih, radicalSeq_gap]
    exact (succ_pow_eq_add_gap n k hn).symm

/-- The chapter index of the radical grassland is the integer root. -/
theorem radicalSeq_chap (n : ℕ) (hn : n ≠ 0) (x : ℕ) :
    (radicalSeq n hn).chap x = irootN n x := by
  apply GapSeq.chap_eq_of
  · rw [radicalSeq_base]
    exact irootN_pow_le n x hn
  · rw [radicalSeq_base]
    exact irootN_lt_succ_pow n x hn

/-- The residue of the radical grassland is the radical remainder:
    the global framework specialises exactly to Aod_n. -/
theorem radicalSeq_res (n : ℕ) (hn : n ≠ 0) (x : ℕ) :
    (radicalSeq n hn).res x = radRem n x := by
  simp only [GapSeq.res, GapSeq.phi, radicalSeq_chap, radicalSeq_base, radRem]

/-- The radical grassland equivalence is exactly `aodEquiv`. -/
theorem radicalSeq_seqEquiv_iff (n : ℕ) (hn : n ≠ 0) (a b : ℕ) :
    (radicalSeq n hn).seqEquiv a b ↔ aodEquiv n a b := by
  simp only [GapSeq.seqEquiv, radicalSeq_res, aodEquiv]

private lemma gap_one_eq (k : ℕ) : gap 1 k = 1 := by
  simp only [gap, pow_one]
  omega

private lemma gap_zero_chapter (n : ℕ) (hn : n ≠ 0) : gap n 0 = 1 := by
  simp [gap, Nat.zero_pow (Nat.pos_of_ne_zero hn)]

/-- Degree 1 is the flat (trivial) radical grassland. -/
theorem radicalSeq_one_flat (h1 : (1 : ℕ) ≠ 0) : (radicalSeq 1 h1).Flat := by
  intro k
  simp [gap_one_eq]

/-- Within the radical family, the flat locus is exactly degree 1:
    the modular limit sits inside the radical family itself. -/
theorem radicalSeq_flat_iff (n : ℕ) (hn : n ≠ 0) :
    (radicalSeq n hn).Flat ↔ n = 1 := by
  constructor
  · intro hf
    have h1 := hf 1
    simp only [radicalSeq_gap] at h1
    have hg0 : gap n 0 = 1 := gap_zero_chapter n hn
    have hg1 : gap n 1 = 2 ^ n - 1 := by norm_num [gap]
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have h2 : 2 ^ n = 2 ^ 1 := by
      have h21 : (2 : ℕ) ^ 1 = 2 := by norm_num
      omega
    exact Nat.pow_right_injective (le_refl 2) h2
  · rintro rfl
    exact radicalSeq_one_flat hn

private lemma gap_two_eq (k : ℕ) : gap 2 k = 2 * k + 1 := by
  have h : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
  simp [gap, h]

/-- Degree 2 is affine: constant slope 2 (zero curvature, nonzero shift). -/
theorem radicalSeq_two_affine (h2 : (2 : ℕ) ≠ 0) :
    (radicalSeq 2 h2).Affine := by
  intro k
  simp only [GapSeq.slope, radicalSeq_gap, gap_two_eq]
  push_cast
  ring

theorem radicalSeq_two_not_flat (h2 : (2 : ℕ) ≠ 0) :
    ¬ (radicalSeq 2 h2).Flat := by
  intro hf
  have h := hf 1
  norm_num [radicalSeq_gap, gap_two_eq] at h

private lemma three_mul_two_pow_lt {n : ℕ} (hn : 3 ≤ n) :
    3 * 2 ^ n < 3 ^ n + 3 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h3 : 3 ≤ 3 ^ n := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, pow_succ]
    omega

/-- Degrees ≥ 3 are not affine: the curvature κ is nonzero.
    -- Witness: κ(n,1,2,1) = 3^n − 3·2^n + 3 > 0 for n ≥ 3. -/
theorem radicalSeq_not_affine {n : ℕ} (hn : 3 ≤ n) (hn0 : n ≠ 0) :
    ¬ (radicalSeq n hn0).Affine := by
  intro ha
  have h1 := ha 1
  simp only [GapSeq.slope, radicalSeq_gap] at h1
  have hg0 : gap n 0 = 1 := gap_zero_chapter n hn0
  have hg1 : gap n 1 = 2 ^ n - 1 := by norm_num [gap]
  have hg2 : gap n 2 = 3 ^ n - 2 ^ n := by norm_num [gap]
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have h32 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  rw [hg0, hg1, hg2] at h1
  push_cast [Nat.cast_sub h32, Nat.cast_sub h2n] at h1
  have hlt : (3 : ℤ) * 2 ^ n < 3 ^ n + 3 := by
    exact_mod_cast three_mul_two_pow_lt hn
  linarith

/-- Within the radical family, the affine locus is exactly degrees ≤ 2:
    the global form of the n = 2 flatness theorem (κ ≡ 0 ⟺ n ≤ 2). -/
theorem radicalSeq_affine_iff (n : ℕ) (hn : n ≠ 0) :
    (radicalSeq n hn).Affine ↔ n ≤ 2 := by
  constructor
  · intro ha
    by_contra hcon
    exact radicalSeq_not_affine (by omega) hn ha
  · intro hle
    have hpos : 1 ≤ n := Nat.pos_of_ne_zero hn
    interval_cases n
    · exact (radicalSeq_one_flat hn).affine
    · exact radicalSeq_two_affine hn

/-- The Mersenne grassland: gap k = 2^k, bases 2^k − 1.  A grassland of
    exponential curvature (contrast with the polynomial curvature of the
    radical family); its bases are the Mersenne numbers of Dir III. -/
def mersenneSeq : GapSeq :=
  ⟨fun k => 2 ^ k, fun k => pow_pos (by norm_num) k⟩

theorem mersenneSeq_base (k : ℕ) : mersenneSeq.base k = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hg : mersenneSeq.gap k = 2 ^ k := rfl
    rw [GapSeq.base_succ, ih, hg, pow_succ]
    omega

theorem mersenneSeq_not_affine : ¬ mersenneSeq.Affine := by
  intro ha
  have h := ha 1
  simp only [GapSeq.slope] at h
  norm_num [mersenneSeq] at h

/-- Exponential curvature of the Mersenne grassland: κ(k, k+1, 1) = 2^k. -/
theorem mersenneSeq_kappa (k : ℕ) :
    mersenneSeq.kappa k (k + 1) 1 = 2 ^ k := by
  show ((2 ^ (k + 1 + 1) : ℕ) : ℤ) - (2 ^ (k + 1) : ℕ)
      - (((2 ^ (k + 1) : ℕ) : ℤ) - (2 ^ k : ℕ)) = 2 ^ k
  push_cast
  simp only [pow_succ]
  ring

/-! ## 11. Per-chapter restriction: the §2 GrasslandData -/

/-- The per-chapter data of a global grassland: chapter `k` as a
    `GrasslandData` (the §2 structure, carrying the ring `Grass`). -/
def GapSeq.chapterData (g : GapSeq) (k : ℕ) : GrasslandData :=
  ⟨g.gap k, g.base k, g.pos k⟩

private lemma GrasslandData.ext' {d₁ d₂ : GrasslandData} (hG : d₁.G = d₂.G)
    (hB : d₁.B = d₂.B) : d₁ = d₂ := by
  cases d₁; cases d₂; simp_all

/-- The chapter-0 restriction of the flat grassland is the modular
    grassland of §2. -/
theorem constSeq_chapterData_zero (m : ℕ) (hm : 0 < m) :
    (constSeq m hm).chapterData 0 = modularGrassland m hm := rfl

/-- The chapter-k restriction of the radical grassland is the radical
    `GrasslandData` of §2: the global object glues the local ones. -/
theorem radicalSeq_chapterData (n k : ℕ) (hn : n ≠ 0) :
    (radicalSeq n hn).chapterData k = radicalGrassland n k hn :=
  GrasslandData.ext'
    (by simp [GapSeq.chapterData, radicalGrassland, capGap, gap])
    (by simpa [GapSeq.chapterData, radicalGrassland] using radicalSeq_base n hn k)

/-! ## 12. Radical corollaries: curvature facts for Aod_n -/

/-- For n ≥ 2 the radical grassland is not flat (Growing Frontier). -/
theorem radicalSeq_not_flat {n : ℕ} (hn : 2 ≤ n) (hn0 : n ≠ 0) :
    ¬ (radicalSeq n hn0).Flat := by
  intro hf
  have h := (radicalSeq_flat_iff n hn0).mp hf
  omega

/-- **aodEquiv is not a congruence** (n ≥ 2): explicit witnesses for the
    failure of translation invariance — the formal content of "the
    quotient Aod_n carries no induced ring".  In the flat grassland the
    same property holds by `constSeq_seqEquiv_iff`; the dichotomy is the
    keystone `translationInvariant_iff_flat`. -/
theorem aodEquiv_not_translation_invariant (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b m, aodEquiv n a b ∧ ¬ aodEquiv n (a + m) (b + m) := by
  have hn0 : n ≠ 0 := by omega
  have hni := GapSeq.not_flat_not_translationInvariant
    (radicalSeq_not_flat hn hn0)
  push_neg at hni
  obtain ⟨a, b, m, hab, hnab⟩ := hni
  refine ⟨a, b, m, (radicalSeq_seqEquiv_iff n hn0 a b).mp hab, fun hcon => ?_⟩
  exact hnab ((radicalSeq_seqEquiv_iff n hn0 _ _).mpr hcon)

/-- Permanent separation, global form: for n ≥ 2 any two distinct
    chapters are broken by some common shift — the gap tails never
    synchronize, by the Growing Frontier. -/
theorem radical_break_exists (n : ℕ) (hn : 2 ≤ n) (k h : ℕ) (hkh : k < h) :
    ∃ u, ¬ aodEquiv n (k ^ n + u) (h ^ n + u) := by
  have hn0 : n ≠ 0 := by omega
  have hnsync : ¬ ∀ i, (radicalSeq n hn0).gap (k + i)
      = (radicalSeq n hn0).gap (h + i) := by
    intro hs
    have h0 := hs 0
    simp only [radicalSeq_gap, Nat.add_zero] at h0
    exact absurd h0 (Nat.ne_of_lt (gap_strictMono n hn k h hkh))
  have hnall : ¬ ∀ u, (radicalSeq n hn0).seqEquiv
      ((radicalSeq n hn0).base k + u) ((radicalSeq n hn0).base h + u) :=
    fun hall =>
      hnsync (((radicalSeq n hn0).seqEquiv_base_add_iff_sync k h).mp hall)
  push_neg at hnall
  obtain ⟨u, hu⟩ := hnall
  refine ⟨u, fun hcon => hu ?_⟩
  have hbridge : (radicalSeq n hn0).seqEquiv (k ^ n + u) (h ^ n + u) :=
    (radicalSeq_seqEquiv_iff n hn0 _ _).mpr hcon
  rwa [← radicalSeq_base n hn0 k, ← radicalSeq_base n hn0 h] at hbridge

/-! ## 13. Curvature prescription: slope data classify grasslands -/

/-- Slopes determine the gap sequence given the initial width:
    `(gap 0, slope)` is a complete invariant of the grassland. -/
theorem GapSeq.gap_eq_of_slope_eq (g g' : GapSeq) (h0 : g.gap 0 = g'.gap 0)
    (hs : ∀ k, g.slope k = g'.slope k) : ∀ k, g.gap k = g'.gap k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have h := hs k
    simp only [GapSeq.slope] at h
    omega

/-- **Curvature prescription**: any slope profile whose partial sums stay
    admissible is realised by a grassland — and uniquely so, by
    `gap_eq_of_slope_eq`.
    -- Example witness: g0 = 1, s = fun _ => 2 (sums 1, 3, 5, …) realises
    -- the radical grassland of degree 2. -/
def GapSeq.ofSlopes (g0 : ℕ) (s : ℕ → ℤ)
    (hpos : ∀ k, 0 < (g0 : ℤ) + ∑ i ∈ Finset.range k, s i) : GapSeq where
  gap k := ((g0 : ℤ) + ∑ i ∈ Finset.range k, s i).toNat
  pos k := by
    have h := hpos k
    omega

theorem GapSeq.ofSlopes_gap_zero (g0 : ℕ) (s : ℕ → ℤ)
    (hpos : ∀ k, 0 < (g0 : ℤ) + ∑ i ∈ Finset.range k, s i) :
    (GapSeq.ofSlopes g0 s hpos).gap 0 = g0 := by
  simp [GapSeq.ofSlopes]

theorem GapSeq.ofSlopes_slope (g0 : ℕ) (s : ℕ → ℤ)
    (hpos : ∀ k, 0 < (g0 : ℤ) + ∑ i ∈ Finset.range k, s i) (k : ℕ) :
    (GapSeq.ofSlopes g0 s hpos).slope k = s k := by
  have h1 := hpos k
  have h2 := hpos (k + 1)
  simp only [GapSeq.slope, GapSeq.ofSlopes]
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
      Finset.sum_range_succ]
  ring

/-! ## 14. Computational checks -/

#eval (radicalSeq 2 (by norm_num)).chap 10      -- expected: 3
#eval (radicalSeq 2 (by norm_num)).res 10       -- expected: 1  (= radRem 2 10)
#eval radRem 2 10                                -- expected: 1
#eval (radicalSeq 2 (by norm_num)).base 5        -- expected: 25
#eval (radicalSeq 3 (by norm_num)).kappa 1 2 1  -- expected: 6  (κ(3,k,h,j) = 6j(h−k))
#eval (constSeq 5 (by norm_num)).res 13         -- expected: 3  (= 13 % 5)
#eval mersenneSeq.base 4                         -- expected: 15 (= 2^4 − 1)
#eval mersenneSeq.kappa 3 4 1                    -- expected: 8  (= 2^3)

end CampiOperazionistici
