/-
  CapitolarTranslations.lean — Campi Operazionistici
  Operation Invariance and Capitolar Translations

  Paper: §14 (Capitolar Translations and Operation Invariance)

  Formalizes the results on operation invariance and on the semigroup of
  capitolar translations from the main paper (`main.pdf`), a natural extension
  of TranslationReencounter.lean.

  Structure:
  §1 — Absolute invariants (Category A): r_n(x), k(x)^n, (k(x)+1)^n, τ-gap
  §2 — Capitolar translation τ_j and its semigroup (≅ (ℕ,+))
  §3 — Unified preservation formula (parameters j, s, c)
  §4 — Conditional invariant: squaring in Aod_2 (trivial but documented)
  §5 — Non-invariants (Category B): counterexamples for multiplication and reflection

  Dependencies:
  - CampiOperazionistici.CampiOperazionistici (irootN, radRem, aodEquiv, gap, …)
  - CampiOperazionistici.TranslationReencounter (gap_strictMono, irootN_perfectPow,
    succ_pow_eq_add_gap, gap_pos', gap_lt_of_lt, gap_le_of_lt)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.TranslationReencounter

namespace CampiOperazionistici

/-! ─────────────────────────────────────────────────────────────────────────
    §1 — Absolute Invariants (Category A)
    ───────────────────────────────────────────────────────────────────────── -/

section InvariantiAssoluti

/-- The radical eval is an invariant (idempotent): if a ≡ b then r_n(a) ≡ r_n(b). -/
theorem radRem_aodEquiv_self (n a b : ℕ) (h : a ≡ₒ b [Aod n]) :
    radRem n a ≡ₒ radRem n b [Aod n] := by
  simp only [aodEquiv] at *
  rw [h]

/-- k(x)^n is an absolute invariant: it sends every equivalent pair into the class [0]. -/
theorem chapter_pow_aodEquiv_zero (n a b : ℕ) (hn : n ≠ 0)
    (_h : a ≡ₒ b [Aod n]) :
    (irootN n a) ^ n ≡ₒ (irootN n b) ^ n [Aod n] := by
  simp only [aodEquiv]
  have ha : radRem n ((irootN n a) ^ n) = 0 := by
    rw [← perfectPower_iff_radRem_zero n _ hn]
    exact ⟨irootN n a, rfl⟩
  have hb : radRem n ((irootN n b) ^ n) = 0 := by
    rw [← perfectPower_iff_radRem_zero n _ hn]
    exact ⟨irootN n b, rfl⟩
  rw [ha, hb]

/-- (k(x)+1)^n is an absolute invariant: it sends every equivalent pair into the class [0]. -/
theorem succ_chapter_pow_aodEquiv_zero (n a b : ℕ) (hn : n ≠ 0)
    (_h : a ≡ₒ b [Aod n]) :
    (irootN n a + 1) ^ n ≡ₒ (irootN n b + 1) ^ n [Aod n] := by
  simp only [aodEquiv]
  have ha : radRem n ((irootN n a + 1) ^ n) = 0 := by
    rw [← perfectPower_iff_radRem_zero n _ hn]
    exact ⟨irootN n a + 1, rfl⟩
  have hb : radRem n ((irootN n b + 1) ^ n) = 0 := by
    rw [← perfectPower_iff_radRem_zero n _ hn]
    exact ⟨irootN n b + 1, rfl⟩
  rw [ha, hb]

/-- Auxiliary lemma: k^n + t + gap(n,k) = (k+1)^n + t. -/
lemma add_gap_eq_succ_pow_add (n k t : ℕ) (hn : n ≠ 0) :
    k ^ n + t + gap n k = (k + 1) ^ n + t := by
  rw [succ_pow_eq_add_gap n k hn]; ring

/-- Theorem 2 (Gap Translation Invariance):
    if a = k^n + t and b = h^n + t with k < h and t < gap(n,k),
    then a + gap(n,k) ≡ b + gap(n,h) [Aod n]. -/
theorem gap_translation_aodEquiv (n k h t : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) :
    k ^ n + t + gap n k ≡ₒ h ^ n + t + gap n h [Aod n] := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  have ht_h : t < gap n h := Nat.lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh)
  have ht_k1 : t < gap n (k + 1) := Nat.lt_trans ht (growingFrontier n k hn)
  have ht_h1 : t < gap n (h + 1) := Nat.lt_trans ht_h (growingFrontier n h hn)
  rw [add_gap_eq_succ_pow_add n k t hnn, add_gap_eq_succ_pow_add n h t hnn]
  rw [radRem_base_add n (k + 1) t hnn ht_k1, radRem_base_add n (h + 1) t hnn ht_h1]

end InvariantiAssoluti


/-! ─────────────────────────────────────────────────────────────────────────
    §2 — Capitolar Translations τ_j and Semigroup Structure
    ───────────────────────────────────────────────────────────────────────── -/

section TauJ

/-- Capitolar translation of order j:
    τ_j(a) = a + (k(a)+j)^n - k(a)^n
    Moves a from chapter k(a) to chapter k(a)+j while keeping the remainder. -/
def tauJ (n j a : ℕ) : ℕ :=
  a + (irootN n a + j) ^ n - (irootN n a) ^ n

-- Computational checks
#eval tauJ 2 1 5   -- 5 + (2+1)^2 - 2^2 = 5 + 9 - 4 = 10  ✓
#eval tauJ 2 1 6   -- 6 + (2+1)^2 - 2^2 = 6 + 9 - 4 = 11  ✓
#eval tauJ 2 0 5   -- 5 + 2^2 - 2^2 = 5  (identity) ✓
#eval tauJ 3 2 9   -- 9 = 2^3+1, k=2; 9 + (2+2)^3 - 8 = 9 + 64 - 8 = 65 = 4^3+1 ✓

/-- Auxiliary lemma: k^n ≤ (k+j)^n for every j. -/
private lemma pow_le_pow_add (n k j : ℕ) : k ^ n ≤ (k + j) ^ n :=
  Nat.pow_le_pow_left (Nat.le_add_right k j) n

/-- Explicit computation of τ_j on elements in standard form k^n + t. -/
lemma tauJ_base_add (n k j t : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    tauJ n j (k ^ n + t) = (k + j) ^ n + t := by
  simp only [tauJ]
  -- First we rewrite irootN n (k^n + t) = k
  have hirootN : irootN n (k ^ n + t) = k := sum_in_chapter n k t hn ht
  rw [hirootN]
  have hle : k ^ n ≤ (k + j) ^ n := pow_le_pow_add n k j
  omega

/-- τ_0 is the identity (on elements in standard form). -/
lemma tauJ_zero (n k t : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    tauJ n 0 (k ^ n + t) = k ^ n + t := by
  simp [tauJ_base_add n k 0 t hn ht]

/-- gap(n,k) ≤ gap(n, k+j) for every j (gap is increasing in k). -/
lemma gap_le_of_add (n k j : ℕ) (hn : 2 ≤ n) : gap n k ≤ gap n (k + j) := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hlt : gap n (k + m) < gap n (k + (m + 1)) := by
      have : k + m + 1 = k + (m + 1) := by ring
      rw [← this]; exact growingFrontier n (k + m) hn
    omega

/-- t < gap(n,k) implies t < gap(n, k+j) for every j ≥ 0. -/
lemma gap_lt_of_add (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    t < gap n (k + j) :=
  Nat.lt_of_lt_of_le ht (gap_le_of_add n k j hn)

/-- Invariance of capitolar translations: if a ≡ b [Aod n], then τ_j(a) ≡ τ_j(b). -/
theorem tauJ_aodEquiv (n j k h t : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) :
    tauJ n j (k ^ n + t) ≡ₒ tauJ n j (h ^ n + t) [Aod n] := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  have ht_h : t < gap n h := Nat.lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh)
  rw [tauJ_base_add n k j t hnn ht, tauJ_base_add n h j t hnn ht_h]
  rw [radRem_base_add n (k + j) t hnn (gap_lt_of_add n k j t hn ht),
      radRem_base_add n (h + j) t hnn (gap_lt_of_add n h j t hn ht_h)]

/-- Semigroup law: τ_{i+j} = τ_j ∘ τ_i.
    The capitolar translations form a monoid isomorphic to (ℕ, +). -/
theorem tauJ_comp (n i j k t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    tauJ n j (tauJ n i (k ^ n + t)) = tauJ n (i + j) (k ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  have hti : t < gap n (k + i) := gap_lt_of_add n k i t hn ht
  rw [tauJ_base_add n k i t hnn ht, tauJ_base_add n (k + i) j t hnn hti,
      tauJ_base_add n k (i + j) t hnn ht]
  ring_nf

/-- Corollary: τ_j ∘ τ_i = τ_{j+i}. -/
theorem tauJ_compose_eq (n i j k t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    tauJ n i (tauJ n j (k ^ n + t)) = tauJ n (j + i) (k ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  rw [tauJ_base_add n k j t hnn ht, tauJ_base_add n (k + j) i t hnn htj,
      tauJ_base_add n k (j + i) t hnn ht]
  ring_nf

/-- **Monoid law** (explicit form):
    τ_{i+j} = τ_j ∘ τ_i, that is, the capitolar translations
    act as a monoid (ℕ, +) under composition. -/
lemma tauJ_monoid_law (n : ℕ) (hn : 2 ≤ n) :
    ∀ i j k t, t < gap n k →
    tauJ n (i + j) (k ^ n + t) = tauJ n j (tauJ n i (k ^ n + t)) :=
  fun i j k t ht => (tauJ_comp n i j k t hn ht).symm

end TauJ


/-! ─────────────────────────────────────────────────────────────────────────
    §3 — Unified Preservation Formula
    ─────────────────────────────────────────────────────────────────────────

    The translations (δ_a, δ_b) that preserve the equivalence of (a, b) are
    parametrized by (j, s, c) with:
      δ_a(j,s,c) = (k+j)^n - k^n + s + c
      δ_b(j,s,c) = (h+j)^n - h^n + s + c
    subject to the constraints: t+s+c < gap(n, k+j).
    ───────────────────────────────────────────────────────────────────────── -/

section FormulaUnificata

/-- Increment of the unified formula for the a-side (chapter k). -/
def deltaA (n k j s c : ℕ) : ℕ :=
  (k + j) ^ n - k ^ n + s + c

/-- Increment of the unified formula for the b-side (chapter h). -/
def deltaB (n h j s c : ℕ) : ℕ :=
  (h + j) ^ n - h ^ n + s + c

/-- Lemma: k^n + t + deltaA n k j s c = (k+j)^n + (t+s+c). -/
private lemma lhs_unified (n k j t s c : ℕ) :
    k ^ n + t + deltaA n k j s c = (k + j) ^ n + (t + s + c) := by
  simp only [deltaA]
  have hle : k ^ n ≤ (k + j) ^ n := pow_le_pow_add n k j
  omega

/-- Lemma: h^n + t + deltaB n h j s c = (h+j)^n + (t+s+c). -/
private lemma rhs_unified (n h j t s c : ℕ) :
    h ^ n + t + deltaB n h j s c = (h + j) ^ n + (t + s + c) := by
  simp only [deltaB]
  have hle : h ^ n ≤ (h + j) ^ n := pow_le_pow_add n h j
  omega

/-- Unified Formula Theorem:
    all translations (δ_a, δ_b) with parameters (j, s, c) satisfying
    the constraints preserve the equivalence of the pair (k^n+t, h^n+t). -/
theorem unified_translation (n k h t j s c : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (_ht : t < gap n k)
    (hsc : t + s + c < gap n (k + j)) :
    k ^ n + t + deltaA n k j s c ≡ₒ h ^ n + t + deltaB n h j s c [Aod n] := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  rw [lhs_unified, rhs_unified]
  have hkhjlt : k + j < h + j := by omega
  have hsc_h : t + s + c < gap n (h + j) :=
    Nat.lt_trans hsc (gap_lt_of_lt n (k + j) (h + j) hn hkhjlt)
  rw [radRem_base_add n (k + j) (t + s + c) hnn hsc,
      radRem_base_add n (h + j) (t + s + c) hnn hsc_h]

/-- Special case j=0, s=0: recovers the homogeneous translation (window [0, gap-t)). -/
theorem unified_homogeneous (n k h t c : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) (hc : c < gap n k - t) :
    k ^ n + t + c ≡ₒ h ^ n + t + c [Aod n] := by
  have key : k ^ n + t + c = k ^ n + t + deltaA n k 0 0 c := by
    simp only [deltaA, Nat.add_zero, Nat.sub_self]; omega
  have key2 : h ^ n + t + c = h ^ n + t + deltaB n h 0 0 c := by
    simp only [deltaB, Nat.add_zero, Nat.sub_self]; omega
  rw [key, key2]
  apply unified_translation n k h t 0 0 c hn hkh ht
  simp only [Nat.add_zero]
  omega

/-- Special case s=0, c=0: recovers the capitolar translation τ_j. -/
theorem unified_capitolar (n k h t j : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) :
    k ^ n + t + deltaA n k j 0 0 ≡ₒ h ^ n + t + deltaB n h j 0 0 [Aod n] := by
  apply unified_translation n k h t j 0 0 hn hkh ht
  simp only [Nat.add_zero]
  have hle : k ^ n ≤ (k + j) ^ n := pow_le_pow_add n k j
  have : t < gap n k := ht
  linarith [gap_lt_of_add n k j t hn ht]

end FormulaUnificata


/-! ─────────────────────────────────────────────────────────────────────────
    §4 — Conditional Invariant: Squaring in Aod_2
    ─────────────────────────────────────────────────────────────────────────

    In Aod_2, for every a ≡ b, we have a^2 ≡ b^2 — but for a trivial reason:
    every a^2 is a perfect square, hence radRem 2 (a^2) = 0 always.
    ───────────────────────────────────────────────────────────────────────── -/

section QuadraturaAod2

/-- Every natural number squared is a perfect power of degree 2. -/
lemma sq_isPerfectPower (a : ℕ) : isPerfectPower 2 (a ^ 2) := ⟨a, by ring⟩

/-- radRem 2 (a^2) = 0 for every a. -/
lemma radRem_sq_zero (a : ℕ) : radRem 2 (a ^ 2) = 0 := by
  rw [← perfectPower_iff_radRem_zero 2 _ (by norm_num)]
  exact sq_isPerfectPower a

/-- Theorem 3 (Squaring in Aod_2): a ≡ b [Aod 2] implies a^2 ≡ b^2 [Aod 2].
    Note: the result is true but for a trivial reason — both sides are 0. -/
theorem sq_aodEquiv_aod2 (a b : ℕ) (_h : a ≡ₒ b [Aod 2]) : a ^ 2 ≡ₒ b ^ 2 [Aod 2] := by
  simp only [aodEquiv]
  rw [radRem_sq_zero a, radRem_sq_zero b]

/-- Observation: a^n ≡ 0 [Aod n] for every a (a^n is always a perfect power). -/
theorem pow_radRem_always_zero (n a : ℕ) (hn : n ≠ 0) : a ^ n ≡ₒ 0 [Aod n] := by
  simp only [aodEquiv]
  have h0 : radRem n 0 = 0 := by simp [radRem]
  rw [h0, ← perfectPower_iff_radRem_zero n _ hn]
  exact ⟨a, rfl⟩

end QuadraturaAod2


/-! ─────────────────────────────────────────────────────────────────────────
    §5 — Non-Invariants (Category B): Counterexamples
    ─────────────────────────────────────────────────────────────────────────

    We prove by counterexample that multiplication and internal reflection
    do not preserve the equivalence.
    ───────────────────────────────────────────────────────────────────────── -/

section NonInvarianti

-- Auxiliary lemma: radRem 2 5 = 1
private lemma radRem_2_5 : radRem 2 5 = 1 := by
  simp only [radRem, irootN, irootAux]; norm_num

-- Auxiliary lemma: radRem 2 2 = 1
private lemma radRem_2_2 : radRem 2 2 = 1 := by
  simp only [radRem, irootN, irootAux]; norm_num

-- Auxiliary lemma: radRem 2 10 = 1
private lemma radRem_2_10 : radRem 2 10 = 1 := by
  simp only [radRem, irootN, irootAux]; norm_num

-- Auxiliary lemma: radRem 2 4 = 0
private lemma radRem_2_4 : radRem 2 4 = 0 := by
  simp only [radRem, irootN, irootAux]; norm_num

/-- Multiplication c·x (c ≥ 2) does not preserve in general.
    Counterexample: n=2, c=2, a=5 (chapter 2, t=1), b=2 (chapter 1, t=1).
    5 ≡ 2 [Aod 2] but 2*5=10 ≢ 2*2=4 [Aod 2]. -/
theorem mul_not_invariant :
    ¬ ∀ (c a b : ℕ), 2 ≤ c → a ≡ₒ b [Aod 2] → c * a ≡ₒ c * b [Aod 2] := by
  intro h
  have hequiv : (5 : ℕ) ≡ₒ 2 [Aod 2] := by
    simp only [aodEquiv]; rw [radRem_2_5, radRem_2_2]
  have hbad := h 2 5 2 (by norm_num) hequiv
  simp only [aodEquiv] at hbad
  rw [show (2 : ℕ) * 5 = 10 from by norm_num,
      show (2 : ℕ) * 2 = 4 from by norm_num,
      radRem_2_10, radRem_2_4] at hbad
  norm_num at hbad

/-- Internal reflection k^n + gap-1-r_n(x) does not preserve in general.
    Counterexample: n=2, a=5 (k=2, t=1, reflection → 7), b=2 (k=1, t=1, reflection → 2).
    radRem 2 7 = 3 ≠ 1 = radRem 2 2. -/
theorem reflection_not_invariant :
    ¬ ∀ (a b : ℕ), a ≡ₒ b [Aod 2] →
      (irootN 2 a) ^ 2 + (gap 2 (irootN 2 a) - 1 - radRem 2 a) ≡ₒ
      (irootN 2 b) ^ 2 + (gap 2 (irootN 2 b) - 1 - radRem 2 b) [Aod 2] := by
  intro h
  have hequiv : (5 : ℕ) ≡ₒ 2 [Aod 2] := by
    simp only [aodEquiv]; rw [radRem_2_5, radRem_2_2]
  have hbad := h 5 2 hequiv
  simp only [aodEquiv] at hbad
  have h7 : irootN 2 5 ^ 2 + (gap 2 (irootN 2 5) - 1 - radRem 2 5) = 7 := by decide
  have h2 : irootN 2 2 ^ 2 + (gap 2 (irootN 2 2) - 1 - radRem 2 2) = 2 := by decide
  rw [h7, h2] at hbad
  have hr7 : radRem 2 7 = 3 := by decide
  have hr2 : radRem 2 2 = 1 := by decide
  rw [hr7, hr2] at hbad
  norm_num at hbad

end NonInvarianti


/-! ─────────────────────────────────────────────────────────────────────────
    §6 — Subtractive Translations and Correction Supertranslation
    ─────────────────────────────────────────────────────────────────────────

    Given a = k^n + t and b = h^n + t with k < h and 0 < t < gap(n,k),
    the pair is equivalent (same radRem = t). We analyze what
    happens when subtracting m:

    • For 0 ≤ m ≤ t  : the equivalence is maintained (radRem = t - m).
      At m = t both land on zero: r_n(k^n) = r_n(h^n) = 0.

    • At m = t + 1   : a - m = k^n - 1  (chapter k-1, radRem = gap(n,k-1) - 1)
                      b - m = h^n - 1  (chapter h-1, radRem = gap(n,h-1) - 1)
                      The two remainders diverge because gap is strictly increasing.

    • Supertranslation: to correct the b-side and restore the equivalence
      in the subtractive regime, the necessary correction is
        σ(n, k, h) = gap(n, h-1) - gap(n, k-1)
      that is, one must subtract from b one extra unit for each interposed gap.

    Connection with the telescopic structure:
        gap(n, h-1) - gap(n, k-1) = ∑_{j=k}^{h-1} Δ(n, j)
    where Δ(n, j) = gap(n, j) - gap(n, j-1) is the growth slice of chapter j.
    ───────────────────────────────────────────────────────────────────────── -/

section TraslazioneSottrattiva

/-- Auxiliary lemma: k^n + t - m = k^n + (t - m) for m ≤ t. -/
private lemma base_sub_rearrange (k n t m : ℕ) (hm : m ≤ t) :
    k ^ n + t - m = k ^ n + (t - m) := by omega

/-- S1 — Subtractive persistence down to zero.
    For 0 ≤ m ≤ t, subtracting m the pair stays equivalent with radRem = t - m.
    At m = t both land on the class [0] (the perfect powers k^n and h^n). -/
theorem subtraction_equiv_until_zero (n k h t m : ℕ)
    (hn : 2 ≤ n) (hkh : k < h)
    (_ht_pos : 0 < t) (ht_bound : t < gap n k) (hm : m ≤ t) :
    k ^ n + t - m ≡ₒ h ^ n + t - m [Aod n] := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  have htm_k : t - m < gap n k := by omega
  have htm_h : t - m < gap n h :=
    Nat.lt_of_lt_of_le htm_k (gap_le_of_lt n k h hn hkh)
  rw [base_sub_rearrange k n t m hm, base_sub_rearrange h n t m hm]
  rw [radRem_base_add n k (t - m) hnn htm_k,
      radRem_base_add n h (t - m) hnn htm_h]

/-- Corollary of S1: at m = t both sides are in the class [0]. -/
theorem subtraction_lands_on_zero (n k h t : ℕ)
    (hn : 2 ≤ n) (hkh : k < h)
    (ht_pos : 0 < t) (ht_bound : t < gap n k) :
    k ^ n + t - t ≡ₒ h ^ n + t - t [Aod n] := by
  have key := subtraction_equiv_until_zero n k h t t hn hkh ht_pos ht_bound (le_refl t)
  -- k^n + t - t = k^n  and  h^n + t - t = h^n
  -- radRem n (k^n) = 0 = radRem n (h^n), confirmed by key
  exact key

/-- Auxiliary lemma: radRem n (k^n - 1) = gap(n, k-1) - 1 for k ≥ 1.
    The predecessor of k^n is the last element of chapter k-1. -/
lemma radRem_pred_pow (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k) :
    radRem n (k ^ n - 1) = gap n (k - 1) - 1 := by
  have hkpred : k = k - 1 + 1 := by omega
  -- k^n - 1 = (k-1)^n + gap(n, k-1) - 1
  have hdecomp : k ^ n - 1 = (k - 1) ^ n + (gap n (k - 1) - 1) := by
    have hsucc : k ^ n = (k - 1) ^ n + gap n (k - 1) := by
      conv_lhs => rw [hkpred]
      exact succ_pow_eq_add_gap n (k - 1) hn
    have hgap_pos : 0 < gap n (k - 1) := gap_pos' n (k - 1) hn
    omega
  have hgap_pos : 0 < gap n (k - 1) := gap_pos' n (k - 1) hn
  have hbound : gap n (k - 1) - 1 < gap n (k - 1) := by omega
  rw [hdecomp]
  exact radRem_base_add n (k - 1) (gap n (k - 1) - 1) hn hbound

/-- S2 — Breaking of the equivalence at m = t + 1 (one step beyond zero).
    After crossing zero, the two radRem diverge:
      r_n(k^n - 1) = gap(n, k-1) - 1
      r_n(h^n - 1) = gap(n, h-1) - 1
    and these are distinct because gap is strictly increasing. -/
theorem subtraction_breaks_after_zero (n k h t : ℕ)
    (hn : 2 ≤ n) (hkh : k < h)
    (hk : 0 < k) (_ht_pos : 0 < t) (_ht_bound : t < gap n k) :
    ¬ (k ^ n + t - (t + 1) ≡ₒ h ^ n + t - (t + 1) [Aod n]) := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  -- k^n + t - (t+1) = k^n - 1  (since t < t+1)
  have hka : k ^ n + t - (t + 1) = k ^ n - 1 := by omega
  have hha : h ^ n + t - (t + 1) = h ^ n - 1 := by omega
  have hh : 0 < h := Nat.lt_trans hk hkh
  rw [hka, hha]
  rw [radRem_pred_pow n k hnn hk, radRem_pred_pow n h hnn hh]
  -- needed: gap(n, k-1) - 1 ≠ gap(n, h-1) - 1
  -- equivalent to: gap(n, k-1) ≠ gap(n, h-1)
  -- which follows from gap strictly increasing and k-1 < h-1
  have hkh_pred : k - 1 < h - 1 := by omega
  have hgap_ne : gap n (k - 1) ≠ gap n (h - 1) :=
    Nat.ne_of_lt (gap_lt_of_lt n (k - 1) (h - 1) hn hkh_pred)
  have hgap_pos_k : 1 ≤ gap n (k - 1) := gap_pos' n (k - 1) (by omega)
  have hgap_pos_h : 1 ≤ gap n (h - 1) := gap_pos' n (h - 1) (by omega)
  omega

/-- S3 — Definition of the subtractive supertranslation.
    To restore the equivalence between k^n - 1 and h^n - 1, one must
    correct the h-side by subtracting the excess σ(n,k,h) = gap(n,h-1) - gap(n,k-1). -/
def subtractionShift (n k h : ℕ) : ℕ :=
  gap n (h - 1) - gap n (k - 1)

/-- S4 — Supertranslation: by subtracting an extra σ(n,k,h) from the h-side,
    the two radRem realign on the value gap(n,k-1) - 1. -/
theorem subtraction_supershift (n k h : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k) :
    radRem n (h ^ n - 1) - subtractionShift n k h = radRem n (k ^ n - 1) := by
  have hnn : n ≠ 0 := by omega
  have hh : 0 < h := Nat.lt_trans hk hkh
  rw [radRem_pred_pow n k hnn hk, radRem_pred_pow n h hnn hh]
  simp only [subtractionShift]
  -- goal: gap(n,h-1) - 1 - (gap(n,h-1) - gap(n,k-1)) = gap(n,k-1) - 1
  have hkh_pred : k - 1 < h - 1 := by omega
  have hgap_lt : gap n (k - 1) < gap n (h - 1) :=
    gap_lt_of_lt n (k - 1) (h - 1) hn hkh_pred
  have hgap_pos_k : 0 < gap n (k - 1) := gap_pos' n (k - 1) hnn
  omega

/-- The telescopic correction: σ(n,k,h) = Σ_{j=k}^{h-1} Δ(n,j)
    where Δ(n,j) = gap(n,j) - gap(n,j-1) is the growth slice of chapter j.
    In closed form: σ(n,k,h) = gap(n,h-1) - gap(n,k-1).
    Connects the subtractive supertranslation with the structure of the growth slices. -/
theorem subtractionShift_telescopic (n k h : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k) :
    subtractionShift n k h =
    ∑ j ∈ Finset.Ico k h, (gap n j - gap n (j - 1)) := by
  simp only [subtractionShift]
  induction h with
  | zero => omega
  | succ h' ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hkh) with heq | hkh'
    · -- base case: k = h', Ico k (k+1) = {k}
      subst heq
      simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, Nat.succ_sub_one]
    · -- inductive step: k < h'
      have hk' : 0 < h' := Nat.lt_trans hk hkh'
      rw [Finset.sum_Ico_succ_top (Nat.le_of_lt_succ hkh)]
      simp only [Nat.succ_sub_one]
      have ih_used := ih hkh'
      have hgap_kk : gap n (k - 1) ≤ gap n (h' - 1) :=
        Nat.le_of_lt (gap_lt_of_lt n (k - 1) (h' - 1) hn (by omega))
      have hgap_hh : gap n (h' - 1) ≤ gap n h' :=
        Nat.le_of_lt (gap_lt_of_lt n (h' - 1) h' hn (by omega))
      omega

-- Computational checks §6
-- Aod 3, k=1, h=2, t=3: subtractive window = {m | m ≤ 3}
-- k^n + t = 1 + 3 = 4,  h^n + t = 8 + 3 = 11
-- radRem 3 (4 - 0) = 3, radRem 3 (11 - 0) = 3  ✓
#eval (radRem 3 4, radRem 3 11)       -- (3, 3)
#eval (radRem 3 3, radRem 3 10)       -- (3, 3)  m=1
#eval (radRem 3 1, radRem 3 8)        -- (1, 0) wait — at m=t=3: (1-1+1=1,8)
-- At m = t = 3: 4 - 3 = 1 = 1^3, 11 - 3 = 8 = 2^3. radRem 3 1 = 0, radRem 3 8 = 0 ✓
#eval (radRem 3 (4 - 3), radRem 3 (11 - 3))   -- (0, 0) ✓ both on zero
-- At m = t+1 = 4: 4 - 4 = 0, 11 - 4 = 7. radRem 3 0 = 0, radRem 3 7 = 6. THEY DIVERGE ✓
#eval (radRem 3 (4 - 4), radRem 3 (11 - 4))   -- (0, 6) ✗ broken
-- subtractionShift 3 1 2 = gap(3,1) - gap(3,0) = 7 - 1 = 6  ✓
#eval subtractionShift 3 1 2     -- 6
-- gap(3,1) - gap(3,0) = 7 - 1 = 6: the slice of chapter 1
#eval (gap 3 1, gap 3 0)         -- (7, 1)
-- radRem 3 (h^n - 1) - σ = radRem 3 (k^n - 1): 6 - 6 = 0 ✓
#eval (radRem 3 (8 - 1), radRem 3 (1 - 1))    -- (6, 0)
-- Aod 3, k=1, h=3: σ = gap(3,2) - gap(3,0) = 19 - 1 = 18
#eval subtractionShift 3 1 3     -- 18
-- Aod 2, k=2, h=4: σ = gap(2,3) - gap(2,1) = 7 - 3 = 4
#eval subtractionShift 2 2 4     -- 4

end TraslazioneSottrattiva


/-! ─────────────────────────────────────────────────────────────────────────
    §6b — Subtractive Reencounters: reencounter blocks in the descending orbit
    ─────────────────────────────────────────────────────────────────────────

    For a pair (a, b) = (k^n+t, h^n+t) with k < h and t < gap(n,k):
    the subtractive translation (a−m, b−m) produces:

    • **Initial window** [0,t]: r_n(a−m) = r_n(b−m) = t−m.
    • **First separation** at m = t+1 (the remainders diverge).
    • **Reencounter blocks**: for t < m < a, the equivalence reappears exactly
      when m falls into a block B(kpp) associated to a pair (kpp, hpp) with
      kpp < k and hpp^n + k^n = kpp^n + h^n ("same Δ-difference of powers").

    Block B(kpp) = {m | k^n+t+1 ≤ m+(kpp+1)^n ∧ m+kpp^n ≤ k^n+t}.
    Duration = gap(n,kpp); common value = k^n+t−m−kpp^n (descends from gap(n,kpp)−1 to 0).

    The blocks are disjoint and ordered by decreasing kpp (the block with maximal kpp
    appears first in the subtractive descent).

    Duality with the additive case: in the additive case one looks for k' > k with
    (k')^n − k^n = Δ (unbounded space); in the subtractive case one looks for kpp < k
    with k^n − kpp^n = Δ (finite space {1,...,k−1}).

    Ref: section on subtractive reencounters of the main paper, §3–§4. -/

section ReincontriSottrattiivi

/-- Initial subtractive window: for m ≤ t, both k^n+t−m and h^n+t−m
    fall into their respective chapter of origin and the common value is t−m. -/
lemma subtractive_initial_window (n k h t m : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) (htm : m ≤ t) :
    radRem n (k ^ n + t - m) = t - m ∧ radRem n (h ^ n + t - m) = t - m := by
  have hnn : n ≠ 0 := by omega
  have ht_sub_k : t - m < gap n k := by omega
  have ht_sub_h : t - m < gap n h :=
    Nat.lt_of_lt_of_le ht_sub_k (gap_le_of_lt n k h hn hkh)
  refine ⟨?_, ?_⟩
  · have heq : k ^ n + t - m = k ^ n + (t - m) := by omega
    rw [heq, radRem_base_add n k _ hnn ht_sub_k]
  · have heq : h ^ n + t - m = h ^ n + (t - m) := by omega
    rw [heq, radRem_base_add n h _ hnn ht_sub_h]

/-- Key lemma: if m is in the block B(kpp) (i.e. k^n+t−m falls into chapter kpp),
    then r_n(k^n+t−m) = k^n+t−m−kpp^n.
    The hypotheses use additions instead of ℕ subtractions to avoid underflow. -/
lemma subtractive_block_radRem (n k kpp t m : ℕ) (hn : 2 ≤ n)
    (_hkpp_lt_k : kpp < k)
    (hm_start : k ^ n + t + 1 ≤ m + (kpp + 1) ^ n)
    (hm_end   : m + kpp ^ n ≤ k ^ n + t) :
    radRem n (k ^ n + t - m) = k ^ n + t - m - kpp ^ n := by
  have hnn : n ≠ 0 := by omega
  set v := k ^ n + t - m with hv_def
  have hv_lb : kpp ^ n ≤ v := by omega
  have hv_ub : v < (kpp + 1) ^ n := by omega
  have hr_lt : v - kpp ^ n < gap n kpp := by simp only [gap]; omega
  have hv_eq : kpp ^ n + (v - kpp ^ n) = v := Nat.add_sub_cancel' hv_lb
  calc radRem n v
      = radRem n (kpp ^ n + (v - kpp ^ n)) := by rw [hv_eq]
    _ = v - kpp ^ n := radRem_base_add n kpp _ hnn hr_lt

/-- Main theorem of subtractive reencounters.
    For t < m < k^n+t, the remainders r_n(a−m) = r_n(b−m) coincide if and only if
    m falls in a reencounter block B(kpp) associated with a pair (kpp,hpp)
    with the same power difference: hpp^n + k^n = kpp^n + h^n.

    Direction ← (proved): applying `subtractive_block_radRem` to the k side
    and to the h side (via hpp playing the same role as kpp for h^n+t−m).

    Direction → (proved): witnesses kpp = irootN n v, hpp = irootN n w with
    v = k^n+t−m, w = h^n+t−m; outside the blocks the remainders are distinct —
    the subtractive dual of the First Jump Theorem. Fully proved (no `sorry`). -/
theorem subtractive_reencounter_iff (n k h t m : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (_ht : t < gap n k) (htm : t < m) (hma : m < k ^ n + t) :
    radRem n (k ^ n + t - m) = radRem n (h ^ n + t - m) ↔
    ∃ kpp hpp : ℕ,
      kpp < k ∧
      hpp ^ n + k ^ n = kpp ^ n + h ^ n ∧
      k ^ n + t + 1 ≤ m + (kpp + 1) ^ n ∧
      m + kpp ^ n ≤ k ^ n + t := by
  constructor
  · -- → direction: witnesses kpp = irootN n v, hpp = irootN n w
    intro heq
    have hnn : n ≠ 0 := by omega
    -- v = k^n+t−m lies in (0, k^n)
    set v := k ^ n + t - m with hv_def
    set w := h ^ n + t - m with hw_def
    have hv_pos : 0 < v := by omega
    have hv_lt : v < k ^ n := by omega
    have hw_pos : 0 < w := by
      have : k ^ n < h ^ n := Nat.pow_lt_pow_left hkh (by omega)
      omega
    -- witnesses
    refine ⟨irootN n v, irootN n w, ?_, ?_, ?_, ?_⟩
    · -- kpp < k: from irootN n v ≤ irootN n (k^n-1) < k
      have hkpp_pow_le : (irootN n v) ^ n ≤ v := irootN_pow_le n v hnn
      have hkpp_lt_k_pow : v < k ^ n := hv_lt
      -- (irootN n v)^n ≤ v < k^n so irootN n v < k
      by_contra h_ge
      push_neg at h_ge
      have : k ^ n ≤ (irootN n v) ^ n := Nat.pow_le_pow_left h_ge n
      omega
    · -- hpp^n + k^n = kpp^n + h^n: from radRem n v = radRem n w
      -- radRem n v = v - (irootN n v)^n, radRem n w = w - (irootN n w)^n
      -- and v + h^n = w + k^n (both equal k^n+t-m+h^n)
      have hrv : radRem n v = v - (irootN n v) ^ n := rfl
      have hrw : radRem n w = w - (irootN n w) ^ n := rfl
      have hv_kpp : (irootN n v) ^ n ≤ v := irootN_pow_le n v hnn
      have hw_hpp : (irootN n w) ^ n ≤ w := irootN_pow_le n w hnn
      -- w - v = h^n - k^n
      have hwv : w = v + (h ^ n - k ^ n) := by
        have : k ^ n < h ^ n := Nat.pow_lt_pow_left hkh (by omega)
        omega
      -- heq gives: v - kpp^n = w - hpp^n
      rw [hrv, hrw] at heq
      omega
    · -- k^n+t+1 ≤ m+(kpp+1)^n: from v < (irootN n v + 1)^n
      have hlt : v < (irootN n v + 1) ^ n := irootN_lt_succ_pow n v hnn
      omega
    · -- m+kpp^n ≤ k^n+t: from kpp^n ≤ v
      have hle : (irootN n v) ^ n ≤ v := irootN_pow_le n v hnn
      omega
  · -- ← direction: both sides equal k^n+t−m−kpp^n
    rintro ⟨kpp, hpp, hkpp_lt, hδ, hm_start, hm_end⟩
    have hnn : n ≠ 0 := by omega
    -- k-side radRem
    have hk_eq : radRem n (k ^ n + t - m) = k ^ n + t - m - kpp ^ n :=
      subtractive_block_radRem n k kpp t m hn hkpp_lt hm_start hm_end
    -- derive hpp > kpp from hδ and hkh
    have hkn_lt_hn : k ^ n < h ^ n := Nat.pow_lt_pow_left hkh (by omega)
    have hkpp_lt_hpp : kpp < hpp := by
      by_contra h_le
      push_neg at h_le
      have : hpp ^ n ≤ kpp ^ n := Nat.pow_le_pow_left h_le n
      omega
    -- residue bound: k^n+t−m−kpp^n < gap n hpp
    have hr_kpp : k ^ n + t - m - kpp ^ n < gap n kpp := by
      simp only [gap]; omega
    have hr_hpp : k ^ n + t - m - kpp ^ n < gap n hpp :=
      Nat.lt_of_lt_of_le hr_kpp (gap_le_of_lt n kpp hpp hn hkpp_lt_hpp)
    -- h-side: h^n+t−m = hpp^n + (k^n+t−m−kpp^n)
    have hh_side_eq : h ^ n + t - m = hpp ^ n + (k ^ n + t - m - kpp ^ n) := by
      omega
    have hh_eq : radRem n (h ^ n + t - m) = k ^ n + t - m - kpp ^ n := by
      rw [hh_side_eq]
      exact radRem_base_add n hpp _ hnn hr_hpp
    rw [hk_eq, hh_eq]

-- Verifiche computazionali §6b
-- n=2, k=7, h=8, t=1: a=50, b=65; (kpp,hpp)=(1,4)
-- hδ: 4^2+7^2 = 1^2+8^2 = 65 ✓
#eval (4^2 + 7^2 : ℕ)   -- 65
#eval (1^2 + 8^2 : ℕ)   -- 65 ✓
-- m=47: k^n+t+1 ≤ m+(kpp+1)^2 ↔ 51 ≤ 47+4=51 ✓; m+kpp^2 ≤ k^n+t ↔ 48 ≤ 50 ✓
#eval (50 + 1, 47 + 4)  -- (51, 51): 51 ≤ 51 ✓
#eval (47 + 1, 50)      -- (48, 50): 48 ≤ 50 ✓
-- valore comune = 50−47−1 = 2
#eval (radRem 2 (50 - 47), radRem 2 (65 - 47))  -- (2, 2) ✓
-- n=2, k=10, h=11, t=1: a=101, b=122; (kpp,hpp)=(2,5)
-- hδ: 5^2+10^2 = 2^2+11^2 = 125 ✓
#eval (5^2 + 10^2 : ℕ)  -- 125
#eval (2^2 + 11^2 : ℕ)  -- 125 ✓
-- m=93: 102 ≤ 93+9=102 ✓; 93+4=97 ≤ 101 ✓; valore comune = 101−93−4 = 4
#eval (radRem 2 (101 - 93), radRem 2 (122 - 93))  -- (4, 4) ✓

/-- **Block duration** (Rem. 14.68):
    The descent block B(kpp) has exactly gap(n,kpp) = (kpp+1)^n − kpp^n elements:
    its last position is k^n+t−kpp^n and its first is k^n+t+1−(kpp+1)^n,
    so (last) + 1 = (first) + gap(n,kpp). -/
lemma subtractive_block_duration (n k kpp t : ℕ) (_hn : 2 ≤ n) (hkpp : kpp < k) :
    k ^ n + t - kpp ^ n + 1 = k ^ n + t + 1 - (kpp + 1) ^ n + gap n kpp := by
  have hpow1 : (kpp + 1) ^ n ≤ k ^ n := Nat.pow_le_pow_left (by omega) n
  have hpow2 : kpp ^ n ≤ (kpp + 1) ^ n := Nat.pow_le_pow_left (by omega) n
  simp only [gap]; omega

/-- **Disjunction of descent blocks** (Prop. 14.66):
    No shift m can lie in two distinct blocks simultaneously. -/
lemma subtractive_blocks_disjoint (n k kpp1 kpp2 t m : ℕ) (_hn : 2 ≤ n)
    (hne : kpp1 ≠ kpp2) (_hkpp1 : kpp1 < k) (_hkpp2 : kpp2 < k)
    (hm1_start : k ^ n + t + 1 ≤ m + (kpp1 + 1) ^ n)
    (hm1_end   : m + kpp1 ^ n ≤ k ^ n + t)
    (hm2_start : k ^ n + t + 1 ≤ m + (kpp2 + 1) ^ n)
    (hm2_end   : m + kpp2 ^ n ≤ k ^ n + t) :
    False := by
  rcases Nat.lt_or_gt_of_ne hne with h12 | h21
  · -- kpp1 < kpp2: (kpp1+1)^n ≤ kpp2^n
    --   hm1_start + this + hm2_end give k^n+t+1 ≤ k^n+t
    set p := (kpp1 + 1) ^ n
    set q := kpp2 ^ n
    have hpq : p ≤ q := Nat.pow_le_pow_left (by omega) n
    omega
  · -- kpp2 < kpp1: symmetric
    set p := (kpp2 + 1) ^ n
    set q := kpp1 ^ n
    have hpq : p ≤ q := Nat.pow_le_pow_left (by omega) n
    omega

/-- **Complete subtractive partition** (Corollary 14.67):
    For m < k^n+t, the pair (k^n+t−m, h^n+t−m) is aod-equivalent if and only if
    m lies in the initial window [0,t] or in some descent block B(kpp). -/
theorem subtractive_complete_partition (n k h t m : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) (hm : m < k ^ n + t) :
    radRem n (k ^ n + t - m) = radRem n (h ^ n + t - m) ↔
    m ≤ t ∨
    ∃ kpp hpp : ℕ,
      kpp < k ∧ hpp ^ n + k ^ n = kpp ^ n + h ^ n ∧
      k ^ n + t + 1 ≤ m + (kpp + 1) ^ n ∧ m + kpp ^ n ≤ k ^ n + t := by
  constructor
  · intro heq
    by_cases htm : m ≤ t
    · exact Or.inl htm
    · exact Or.inr
        ((subtractive_reencounter_iff n k h t m hn hkh ht (by omega) hm).mp heq)
  · rintro (htm | ⟨kpp, hpp, hlt, hdelta, hstart, hend⟩)
    · -- Initial window: both radRem equal t − m
      have hw := subtractive_initial_window n k h t m hn hkh ht htm
      rw [hw.1, hw.2]
    · -- Descent block: derive t < m, then use subtractive_reencounter_iff
      -- From hstart and kpp < k: (kpp+1)^n ≤ k^n, so m ≥ t+1
      set q := (kpp + 1) ^ n
      set p := k ^ n
      have hqp : q ≤ p := Nat.pow_le_pow_left (by omega) n
      have htm' : t < m := by omega
      exact (subtractive_reencounter_iff n k h t m hn hkh ht htm' hm).mpr
        ⟨kpp, hpp, hlt, hdelta, hstart, hend⟩

end ReincontriSottrattiivi


/-! ─────────────────────────────────────────────────────────────────────────
    §7 — Gauge Impossibility: τ_j-Invariant Functions Factor Through radRem
    ─────────────────────────────────────────────────────────────────────────

    **Question**: what structure does a function f : ℕ → ℕ need to respect all
    capitolar translations τ_j?  The answer is crisp:

      *f must be a function of radRem n alone.*

    Proof: any two elements a = k^n+t and b = h^n+t sharing the same local
    coordinate t are connected by τ_{h−k}(a) = b (for k ≤ h).  Hence
    f(a) = f(τ_{h−k}(a)) = f(b).

    Corollary: aodEquiv is the **finest** τ_j-invariant equivalence.
    Every equivalence relation preserved by all τ_j is coarser than aodEquiv
    (has fewer distinctions).  The Aod_n classes are therefore the atoms of the
    τ_j-invariant structure — no τ_j-preserved partition can be finer.
    ───────────────────────────────────────────────────────────────────────── -/

section GaugeImpossibility

/-- **radRem invariance of τ_j** (standard form):
    τ_j preserves the local coordinate on elements of the form k^n+t. -/
theorem tauJ_radRem_preserved (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    radRem n (tauJ n j (k ^ n + t)) = radRem n (k ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  rw [tauJ_base_add n k j t hnn ht,
      radRem_base_add n (k + j) t hnn (gap_lt_of_add n k j t hn ht),
      radRem_base_add n k t hnn ht]

/-- **τ_j connects same-radRem elements**: for k ≤ h,
    τ_{h−k}(k^n+t) = h^n+t.  The local coordinate t stays fixed while the
    chapter index advances from k to h. -/
lemma tauJ_connects_same_radRem (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k ≤ h)
    (ht : t < gap n k) :
    tauJ n (h - k) (k ^ n + t) = h ^ n + t := by
  have hnn : n ≠ 0 := by omega
  rw [tauJ_base_add n k (h - k) t hnn ht, Nat.add_sub_cancel' hkh]

/-- **Gauge Impossibility Theorem**: any function f : ℕ → ℕ preserved by all τ_j
    must be constant on every Aod_n equivalence class; that is, it takes equal values
    on any two elements sharing the same local coordinate radRem n.

    In other words, f factors through radRem n: f = g ∘ (radRem n) for some g.

    Proof sketch: write a = k^n+t and b = h^n+t.  For k ≤ h:
      f(a) = f(τ_{h−k}(a)) = f(b).
    For k > h, swap roles. -/
theorem tauJ_invariant_factors_radRem (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℕ)
    (hf : ∀ j a, f (tauJ n j a) = f a)
    (a b : ℕ) (hrad : radRem n a = radRem n b) :
    f a = f b := by
  have hnn : n ≠ 0 := by omega
  -- Canonical chapter indices and local coordinate
  have hle_a := irootN_pow_le n a hnn
  have hlt_a := irootN_lt_succ_pow n a hnn
  have hle_b := irootN_pow_le n b hnn
  -- a = (irootN n a)^n + radRem n a
  have ha : a = (irootN n a) ^ n + radRem n a := by simp [radRem]; omega
  -- b = (irootN n b)^n + radRem n b = (irootN n b)^n + radRem n a  (using hrad)
  have hb : b = (irootN n b) ^ n + radRem n a := by
    -- Goal: b = (irootN n b)^n + radRem n a.
    -- Rewrite radRem n a → radRem n b (hrad), then use irootN_pow_le.
    rw [hrad]; simp [radRem]; omega
  -- Local coordinate fits in gap of irootN n a
  have ht_ka : radRem n a < gap n (irootN n a) := by simp [gap, radRem]; omega
  -- Local coordinate also fits in gap of irootN n b  (using hrad)
  have ht_kb : radRem n a < gap n (irootN n b) := by
    have hlt_b := irootN_lt_succ_pow n b hnn
    -- rewrite goal: radRem n a = radRem n b (via hrad), then use same bound as ht_ka style
    rw [hrad]    -- radRem n a → radRem n b in the goal
    simp [gap, radRem]; omega
  -- Connect a to b via the appropriate τ
  rcases Nat.lt_or_ge (irootN n b) (irootN n a) with hkh | hkh
  · -- irootN n b < irootN n a: τ_{k−h}(b) = a
    have hkh_le : irootN n b ≤ irootN n a := Nat.le_of_lt hkh
    have hlink : tauJ n (irootN n a - irootN n b) b = a := by
      have := tauJ_connects_same_radRem n (irootN n b) (irootN n a) (radRem n a) hn hkh_le ht_kb
      rw [← hb] at this; rwa [← ha] at this
    calc f a = f (tauJ n (irootN n a - irootN n b) b) := by rw [hlink]
         _ = f b := hf _ _
  · -- irootN n a ≤ irootN n b: τ_{h−k}(a) = b
    have hlink : tauJ n (irootN n b - irootN n a) a = b := by
      have := tauJ_connects_same_radRem n (irootN n a) (irootN n b) (radRem n a) hn hkh ht_ka
      rw [← ha] at this; rwa [← hb] at this
    calc f a = f (tauJ n (irootN n b - irootN n a) a) := (hf _ _).symm
         _ = f b := by rw [hlink]

/-- **Corollary — aodEquiv is the finest τ_j-invariant equivalence**:
    any function preserved by all τ_j cannot distinguish Aod_n classes.
    Equivalently, if a ≡ₒ b [Aod n] then every τ_j-invariant f satisfies f(a) = f(b). -/
theorem aodEquiv_finest_tauJ_invariant (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℕ)
    (hf : ∀ j a, f (tauJ n j a) = f a)
    (a b : ℕ) (heq : a ≡ₒ b [Aod n]) : f a = f b :=
  -- aodEquiv IS radRem n a = radRem n b by definition
  tauJ_invariant_factors_radRem n hn f hf a b heq

end GaugeImpossibility

end CampiOperazionistici
