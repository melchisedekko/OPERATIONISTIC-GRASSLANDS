/-
  SeparationVector.lean — Campi Operazionistici
  Separation Vector, Projection into Aod∞ and the Operational Tower

  Paper: §18 (Separation Vector)

  Formalizes the results on the separation vector and the projection tower in Aod∞
  from the main paper (`main.pdf`):

  §1  — Auxiliary lemmas on irootN for high degrees
  §2  — Separation vector: definition and explicit formula
  §3  — Profile stabilization theorem
  §4  — Structure of the discontinuities D(k,h) (under the hypothesis k ≥ 1)
  §5  — Projection π_n and injectivity of the fibers
  §6  — Tower Lemma: κ_{pn} = κ_p ∘ κ_n
  §7  — Tower Theorem (proved)
  §8  — Invariance of sepComp under τ_j at level n
  §8b — Subtractive direction: sepComp under τ_{-j} (offset-bounded descent)
  §9  — Capitolar profile monoid constraint (D4)
  §10 — General (n,m)-bigraded cells (from FourDiamond §D2)

  Conceptual dependence on Aod∞ (the Lean imports do not reflect it):
  - The separation vector is s⃗(a,b) = ι(b) − ι(a), where
    ι(x) = (r_2(x), r_3(x), ...) is the radical profile in Aod∞
    (AodInfinito.lean, `diagEmbed`).
  - `aodInf_separates` (§5) is the injectivity of the diagonal embedding ℕ → Aod∞:
    Aod∞ separates every pair of distinct naturals ≥ 2.
  - The Tower Lemma κ_{pn} = κ_p ∘ κ_n (§6) is the hierarchical structure
    of the levels of Aod∞: composite degrees factor through the prime degrees.
  - Understanding §5–§7 requires AodInfinito.lean as a conceptual frame,
    even though the Lean code is self-contained (i.e. it does not import it).

  Lean dependencies:
  - CampiOperazionistici.CampiOperazionistici (irootN, radRem, aodEquiv, …)
  - CampiOperazionistici.TranslationReencounter (gap_pos', succ_pow_eq_add_gap, …)
  - CampiOperazionistici.CapitolarTranslations (tauJ, gap_le_of_add)
  - CampiOperazionistici.CapitolarGroupoid (tauNeg, tauNeg_base_add) — for §8b
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.TranslationReencounter
import CampiOperazionistici.CapitolarTranslations
import CampiOperazionistici.CapitolarGroupoid

namespace CampiOperazionistici

/-! ─────────────────────────────────────────────────────────────────────────
    §1 — Auxiliary Lemmas on irootN for High Degrees
    ───────────────────────────────────────────────────────────────────────── -/

section LemmiAusiliari

/-- n < 2^n for every n : ℕ. -/
private lemma lt_two_pow_self' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm]
    have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    linarith

/-- If 2^m > a ≥ 2, then irootN m a = 1. -/
lemma irootN_eq_one_large (m a : ℕ) (hm : 2 ^ m > a) (ha : 2 ≤ a) :
    irootN m a = 1 := by
  have hnn : m ≠ 0 := by
    intro h; simp [h] at hm; omega
  apply Nat.le_antisymm
  · by_contra hc
    push_neg at hc
    have h2 : 2 ≤ irootN m a := hc
    have hpow : 2 ^ m ≤ (irootN m a) ^ m := Nat.pow_le_pow_left h2 m
    have hle : (irootN m a) ^ m ≤ a := irootN_pow_le m a hnn
    linarith
  · rw [Nat.one_le_iff_ne_zero]
    intro h
    rw [irootN_eq_zero_iff m a hnn] at h
    omega

/-- If irootN m a = 1, then radRem m a = a - 1. -/
lemma radRem_eq_pred_of_irootN_one (m a : ℕ) (h : irootN m a = 1) :
    radRem m a = a - 1 := by
  simp [radRem, h]

/-- For 2^m > a ≥ 2, radRem m a = a - 1. -/
lemma radRem_large_grade (m a : ℕ) (hm : 2 ^ m > a) (ha : 2 ≤ a) :
    radRem m a = a - 1 := by
  rw [radRem_eq_pred_of_irootN_one m a (irootN_eq_one_large m a hm ha)]

/-- irootN m 1 = 1 for every m ≠ 0. -/
lemma irootN_one (m : ℕ) (hm : m ≠ 0) : irootN m 1 = 1 := by
  apply Nat.le_antisymm
  · by_contra hc; push_neg at hc
    have h2le : 2 ≤ irootN m 1 := hc
    have hpow : 2 ^ m ≤ (irootN m 1) ^ m := Nat.pow_le_pow_left h2le m
    have hle : (irootN m 1) ^ m ≤ 1 := irootN_pow_le m 1 hm
    -- 2^m ≤ (irootN m 1)^m ≤ 1, but 2^m ≥ 2 > 1 for m ≥ 1
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    have h2m : 2 ≤ 2 ^ m := Nat.le_self_pow hm 2
    omega
  · rw [Nat.one_le_iff_ne_zero]
    intro h0; rw [irootN_eq_zero_iff m 1 hm] at h0; omega

end LemmiAusiliari


/-! ─────────────────────────────────────────────────────────────────────────
    §2 — Separation Vector
    ─────────────────────────────────────────────────────────────────────────

    For a pair (a, b), we define the m-th component of the separation
    vector as r_m(b) - r_m(a) (in ℤ to keep the sign).

    Explicit Formula Theorem (cf. §2.2 of the main paper):
      s⃗(a,b)[m] = (b - a) - (κ_m(b)^m - κ_m(a)^m)   with everything in ℤ.
    ───────────────────────────────────────────────────────────────────────── -/

section SeparationVector

/-- m-th component of the separation vector: r_m(b) - r_m(a). -/
def sepComp (m a b : ℕ) : ℤ :=
  (radRem m b : ℤ) - (radRem m a : ℤ)

/-- For a pair equivalent in Aod n, the n-th component is 0. -/
theorem sepComp_eq_zero_at_n (n a b : ℕ) (h : a ≡ₒ b [Aod n]) :
    sepComp n a b = 0 := by
  simp only [sepComp, aodEquiv] at *; omega

/-- The m-th component is antisymmetric. -/
lemma sepComp_antisymm (m a b : ℕ) : sepComp m a b = -sepComp m b a := by
  simp [sepComp]

/-- **Explicit Formula of the Separation Vector** (§2.2):
    s⃗(a,b)[m] = (b - a) - (κ_m(b)^m - κ_m(a)^m). -/
theorem sepComp_formula (m a b : ℕ) (hm : m ≠ 0) :
    sepComp m a b =
      ((b : ℤ) - a) - ((irootN m b : ℤ) ^ m - (irootN m a : ℤ) ^ m) := by
  simp only [sepComp, radRem]
  have ha_le : (irootN m a) ^ m ≤ a := irootN_pow_le m a hm
  have hb_le : (irootN m b) ^ m ≤ b := irootN_pow_le m b hm
  zify [ha_le, hb_le]; ring

/-- **Fundamental Corollary** (§2.3):
    s⃗(a,b)[m] = b - a  ↔  κ_m(a) = κ_m(b). -/
theorem sepComp_eq_diff_iff_same_chapter (m a b : ℕ) (hm : m ≠ 0) :
    sepComp m a b = (b : ℤ) - a ↔ irootN m a = irootN m b := by
  rw [sepComp_formula m a b hm]
  constructor
  · intro h
    have hpow_eq : (irootN m b : ℤ) ^ m = (irootN m a : ℤ) ^ m := by linarith
    have hpow_nat : irootN m b ^ m = irootN m a ^ m := by exact_mod_cast hpow_eq
    exact (Nat.pow_left_injective hm hpow_nat).symm
  · intro h; rw [h]; ring

/-- Consequence: if the chapters coincide, sepComp = b - a. -/
lemma sepComp_of_same_chapter (m a b : ℕ) (hm : m ≠ 0) (h : irootN m a = irootN m b) :
    sepComp m a b = (b : ℤ) - a :=
  (sepComp_eq_diff_iff_same_chapter m a b hm).mpr h

/-- Consequence: if sepComp ≠ b - a, then the chapters differ. -/
lemma sepComp_ne_diff_imp_diff_chapter (m a b : ℕ) (hm : m ≠ 0)
    (h : sepComp m a b ≠ (b : ℤ) - a) : irootN m a ≠ irootN m b :=
  fun heq => h ((sepComp_eq_diff_iff_same_chapter m a b hm).mpr heq)

end SeparationVector


/-! ─────────────────────────────────────────────────────────────────────────
    §3 — Profile Stabilization Theorem
    ─────────────────────────────────────────────────────────────────────────

    For m large enough (2^m > max(a,b)), the pair (a,b) both fall
    into chapter 1 of Aod_m and the difference of the remainders stabilizes to b - a.
    Explicit threshold: M(a,b) = ⌊log₂(max(a,b))⌋ + 1.
    ───────────────────────────────────────────────────────────────────────── -/

section Stabilization

/-- **Stabilization Theorem** (§3.1, general form):
    For 2^m > max(a,b) with a,b ≥ 2, sepComp m a b = b - a. -/
theorem sepComp_stabilizes_general (m a b : ℕ)
    (hm_a : 2 ^ m > a) (hm_b : 2 ^ m > b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    sepComp m a b = (b : ℤ) - a := by
  have hm_ne : m ≠ 0 := by intro h; simp [h] at hm_a; omega
  apply (sepComp_eq_diff_iff_same_chapter m a b hm_ne).mpr
  rw [irootN_eq_one_large m a hm_a ha, irootN_eq_one_large m b hm_b hb]

/-- Logarithmic threshold: max(a,b) < 2^(log₂(max(a,b))+1). -/
private lemma lt_pow_log2_succ (x : ℕ) (_hx : 0 < x) :
    x < 2 ^ (Nat.log2 x + 1) := by
  rw [Nat.log2_eq_log_two]; exact Nat.lt_pow_succ_log_self (by norm_num) x

/-- **Explicit stabilization threshold** (§3.1):
    For every m ≥ ⌊log₂(max(a,b))⌋ + 1, sepComp m a b = b - a holds. -/
theorem sepComp_stabilizes_threshold (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∀ m ≥ Nat.log2 (max a b) + 1, sepComp m a b = (b : ℤ) - a := by
  intro m hm
  have hmax_pos : 0 < max a b := by omega
  have hlt : max a b < 2 ^ (Nat.log2 (max a b) + 1) := lt_pow_log2_succ _ hmax_pos
  apply sepComp_stabilizes_general
  · calc a ≤ max a b := Nat.le_max_left _ _
         _ < 2 ^ (Nat.log2 (max a b) + 1) := hlt
         _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · calc b ≤ max a b := Nat.le_max_right _ _
         _ < 2 ^ (Nat.log2 (max a b) + 1) := hlt
         _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · exact ha
  · exact hb

/-- **Existence of the threshold**: for every a,b ≥ 2, there exists M s.t. ∀ m ≥ M,
    sepComp m a b = b - a. -/
theorem sepComp_eventually_diff (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ M : ℕ, ∀ m ≥ M, sepComp m a b = (b : ℤ) - a :=
  ⟨Nat.log2 (max a b) + 1, sepComp_stabilizes_threshold a b ha hb⟩

/-- **Coordinate form** (§3, form k^n+t). -/
theorem profile_stabilization (n k h t m : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (_ht : t < gap n k)
    (hm : 2 ^ m > h ^ n + t) (ha2 : 2 ≤ k ^ n + t) :
    sepComp m (k ^ n + t) (h ^ n + t) = (h ^ n : ℤ) - k ^ n := by
  simp only [sepComp]
  have hnn : n ≠ 0 := by omega
  have hm_a : 2 ^ m > k ^ n + t :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.pow_lt_pow_left hkh hnn) t) hm.le
  have hb2 : 2 ≤ h ^ n + t := by
    have : k ^ n < h ^ n := Nat.pow_lt_pow_left hkh hnn; linarith
  rw [radRem_large_grade m (k ^ n + t) hm_a ha2,
      radRem_large_grade m (h ^ n + t) hm hb2]
  zify [show 1 ≤ k ^ n + t by linarith, show 1 ≤ h ^ n + t by linarith]; ring

/-- Corollary: the asymptotic stabilization is independent of t. -/
theorem profile_stabilization_indep_t (n k h t t' m : ℕ)
    (hn : 2 ≤ n) (hkh : k < h)
    (ht : t < gap n k) (ht' : t' < gap n k)
    (hm : 2 ^ m > h ^ n + (max t t'))
    (ha2 : 2 ≤ k ^ n + t) (ha2' : 2 ≤ k ^ n + t') :
    sepComp m (k ^ n + t) (h ^ n + t) =
    sepComp m (k ^ n + t') (h ^ n + t') := by
  have hmt : 2 ^ m > h ^ n + t :=
    (Nat.add_le_add_left (Nat.le_max_left t t') _).trans_lt hm
  have hmt' : 2 ^ m > h ^ n + t' :=
    (Nat.add_le_add_left (Nat.le_max_right t t') _).trans_lt hm
  rw [profile_stabilization n k h t m hn hkh ht hmt ha2,
      profile_stabilization n k h t' m hn hkh ht' hmt' ha2']

/-- Existence of the threshold (coordinate form). -/
theorem sepComp_stabilizes (n k h t : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (ht : t < gap n k) (ha2 : 2 ≤ k ^ n + t) :
    ∃ M : ℕ, ∀ m ≥ M,
      sepComp m (k ^ n + t) (h ^ n + t) = (h ^ n : ℤ) - k ^ n := by
  refine ⟨Nat.log2 (h ^ n + t) + 1, fun m hm => profile_stabilization n k h t m hn hkh ht ?_ ha2⟩
  have hpos : 0 < h ^ n + t := by
    have : k ^ n < h ^ n := Nat.pow_lt_pow_left (by omega) (by omega); linarith
  calc h ^ n + t < 2 ^ (Nat.log2 (h ^ n + t) + 1) := lt_pow_log2_succ _ hpos
       _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

end Stabilization


/-! ─────────────────────────────────────────────────────────────────────────
    §4 — Structure of the Discontinuities of the Separation Vector
    ─────────────────────────────────────────────────────────────────────────

    For (a,b) with a = k^n+t, b = h^n+t, 1 ≤ k < h, the set of
    "non-stable" components is D(k,h,n) = {m ≥ 2 : κ_m(k^n) ≠ κ_m(h^n)}.
    (cf. §4 of the main paper)

    Note: the hypothesis k ≥ 1 is necessary. For k=0, h=1 we have k^n=0 and h^n=1
    which always remain distinct, hence D(0,1,n) is infinite.
    ───────────────────────────────────────────────────────────────────────── -/

section Discontinuities

/-- **Set of discontinuities** D(k,h,n):
    the degrees m for which the base points k^n and h^n have distinct chapters in Aod_m. -/
def discontinuitySet (n k h : ℕ) : Set ℕ :=
  {m | 2 ≤ m ∧ irootN m (k ^ n) ≠ irootN m (h ^ n)}

/-- The m-th component is "stable" (= h^n - k^n) iff m ∉ D(k,h,n),
    in the case t=0. -/
theorem sepComp_stable_iff_not_disc (n k h m : ℕ) (_hn : 2 ≤ n) (_hkh : k < h)
    (hm : 2 ≤ m) :
    sepComp m (k ^ n) (h ^ n) = (h ^ n : ℤ) - k ^ n ↔
    m ∉ discontinuitySet n k h := by
  have hm_ne : m ≠ 0 := by omega
  simp only [discontinuitySet, Set.mem_setOf_eq, not_and, not_not]
  have key := sepComp_eq_diff_iff_same_chapter m (k ^ n) (h ^ n) hm_ne
  constructor
  · intro heq h2m
    exact key.mp (by exact_mod_cast heq)
  · intro himp
    have := key.mpr (himp hm)
    exact_mod_cast this

/-- The discontinuities disappear for large degrees (with k ≥ 1):
    for m ≥ M(k^n, h^n), no m belongs to D(k,h,n). -/
theorem discontinuitySet_bounded (n k h : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkh : k < h) :
    ∀ m ≥ Nat.log2 (max (k ^ n) (h ^ n)) + 1,
      m ∉ discontinuitySet n k h := by
  intro m hm hcontra
  simp only [discontinuitySet, Set.mem_setOf_eq] at hcontra
  obtain ⟨hm2, hne⟩ := hcontra
  have hnn : n ≠ 0 := by omega
  -- k ≥ 1, h ≥ 2 (since h > k ≥ 1)
  have hh2 : 2 ≤ h := by omega
  -- k^n ≥ 1 and h^n ≥ 2^n ≥ 4 ≥ 2
  have hkn_ge1 : 1 ≤ k ^ n := Nat.one_le_pow n k hk
  have hhn_ge : 2 ≤ h ^ n := by
    have : 2 ^ n ≤ h ^ n := Nat.pow_le_pow_left hh2 n
    have : 2 ≤ 2 ^ n := Nat.le_self_pow hnn 2
    omega
  -- 2^m > max(k^n, h^n)
  have hmax_pos : 0 < max (k ^ n) (h ^ n) := by omega
  have hlt : max (k ^ n) (h ^ n) < 2 ^ (Nat.log2 (max (k ^ n) (h ^ n)) + 1) :=
    lt_pow_log2_succ _ hmax_pos
  have h2m_h : 2 ^ m > h ^ n :=
    (Nat.le_max_right _ _).trans_lt hlt |>.trans_le (Nat.pow_le_pow_right (by norm_num) hm)
  have h2m_k : 2 ^ m > k ^ n :=
    (Nat.le_max_left _ _).trans_lt hlt |>.trans_le (Nat.pow_le_pow_right (by norm_num) hm)
  -- Both irootN m (h^n) = 1 and irootN m (k^n) = 1 or 0
  have h_eq_h : irootN m (h ^ n) = 1 := irootN_eq_one_large m (h ^ n) h2m_h hhn_ge
  rcases Nat.lt_or_ge (k ^ n) 2 with hkn_lt | hkn_ge
  · -- k^n = 1 (since k^n ≥ 1 and k^n < 2)
    have hkn1 : k ^ n = 1 := by omega
    have h_eq_k : irootN m (k ^ n) = 1 := by rw [hkn1]; exact irootN_one m (by omega)
    exact hne (h_eq_k.trans h_eq_h.symm)
  · -- k^n ≥ 2
    have h_eq_k : irootN m (k ^ n) = 1 := irootN_eq_one_large m (k ^ n) h2m_k hkn_ge
    exact hne (h_eq_k.trans h_eq_h.symm)

end Discontinuities


/-! ─────────────────────────────────────────────────────────────────────────
    §5 — Projection π_n and Injectivity of the Fibers
    ─────────────────────────────────────────────────────────────────────────

    The projection of degree n is π_n(x) = r_n(x).
    The fiber of t is π_n⁻¹(t) = {k^n + t : k ≥ 1, t < gap(n,k)}.
    Theorem: distinct elements of the fiber have distinct Aod∞ profiles.
    (cf. §5 of the main paper)
    ───────────────────────────────────────────────────────────────────────── -/

section Projection

/-- The projection of degree n: π_n(x) = r_n(x). -/
def projN (n x : ℕ) : ℕ := radRem n x

/-- The fiber of t under π_n. -/
def fiberN (n t : ℕ) : Set ℕ :=
  {x | ∃ k ≥ 1, t < gap n k ∧ x = k ^ n + t}

/-- Compatibility: a ~ b [Aod n] ↔ π_n(a) = π_n(b). -/
theorem projN_iff_aodEquiv (n a b : ℕ) :
    projN n a = projN n b ↔ a ≡ₒ b [Aod n] := by
  simp [projN, aodEquiv]

/-- **Injectivity of the Fibers in Aod∞** (§5.2 Proposition):
    If k ≠ k' (with k,k' ≥ 1), for large m r_m(k^n+t) ≠ r_m((k')^n+t). -/
theorem fiber_injective_aodInf (n t k k' : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hk' : 1 ≤ k') (hne : k ≠ k') :
    ∃ m : ℕ, radRem m (k ^ n + t) ≠ radRem m (k' ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  have hkn_ne : k ^ n ≠ k' ^ n := fun h => hne (Nat.pow_left_injective hnn h)
  have hkn_ge1 : 1 ≤ k ^ n := Nat.one_le_pow n k (by omega)
  have hkn_ge1' : 1 ≤ k' ^ n := Nat.one_le_pow n k' (by omega)
  -- Use witness M = k^n + k'^n + t + 2; then 2^M is large enough for both
  -- but simpler: use the separating degree n itself
  -- For large m both k^n+t and k'^n+t fall in chapter 1 of Aod_m
  -- and radRem m (x) = x - 1, so difference = k'^n - k^n ≠ 0.
  -- We need both ≥ 2. Handle k^n = 1 (i.e. k=1, t=0) separately.
  -- Since k^n ≠ k'^n and both ≥ 1, one is ≥ 2.
  -- If k^n = 1 and t = 0: radRem M (k^n+t) = radRem M 1 = 0
  --   and k'^n+t ≥ k'^n ≥ 2 → radRem M (k'^n+t) = k'^n+t-1 ≥ 1. Done.
  -- Otherwise both k^n+t ≥ 2 and k'^n+t ≥ 2 and we use radRem_large_grade.
  rcases Nat.eq_or_lt_of_le hkn_ge1 with hk1 | hk2
  · -- 1 = k^n, so k^n = 1
    have hkn1 : k ^ n = 1 := hk1.symm
    rcases Nat.eq_or_lt_of_le hkn_ge1' with hk'1 | hk'2
    · -- k'^n = 1 too: impossible since k^n ≠ k'^n
      exact absurd (hkn1.trans hk'1) hkn_ne
    · -- k'^n ≥ 2
      have hk'n2 : 2 ≤ k' ^ n := hk'2
      set A := k ^ n + t; set B := k' ^ n + t
      have hA_val : A = 1 + t := by simp [A, hkn1]
      have hB2 : 2 ≤ B := by simp [B]; omega
      have hA_le_B : A ≤ B := by simp [A, B, hkn1]; omega
      use Nat.log2 B + 1
      set M := Nat.log2 B + 1
      have hB_pos : 0 < B := by omega
      have hM_B : B < 2 ^ M := lt_pow_log2_succ B hB_pos
      have hM_A : 2 ^ M > A := hA_le_B.trans_lt hM_B
      rcases Nat.lt_or_ge A 2 with hA1 | hA2
      · -- A = 1 (since A ≥ 1 from hkn_ge1 + t ≥ 0)
        have hA_eq : A = 1 := by simp [A, hkn1]; omega
        have hA_rr : radRem M A = 0 := by
          rw [hA_eq]; simp [radRem, irootN_one M (by omega)]
        have hB_rr : radRem M B = B - 1 := radRem_large_grade M B hM_B hB2
        rw [hA_rr, hB_rr]; omega
      · rw [radRem_large_grade M A hM_A hA2, radRem_large_grade M B hM_B hB2]
        simp only [A, B, hkn1]; omega
  · -- k^n ≥ 2
    have hkn2 : 2 ≤ k ^ n := hk2
    have ha2 : 2 ≤ k ^ n + t := by omega
    -- k'^n ≥ 2 as well, since k'^n ≥ 1 and if k'^n = 1 then k^n ≥ 2 > 1 = k'^n so k^n ≠ k'^n ✓
    -- but we still need 2 ≤ k'^n + t; if k'^n = 1 and t = 0 this fails
    -- Handle: case split on k'^n
    rcases Nat.eq_or_lt_of_le hkn_ge1' with hk'1 | hk'2
    · -- k'^n = 1
      have hk'n1 : k' ^ n = 1 := hk'1.symm
      -- Then k^n ≥ 2 and k'^n + t = 1 + t
      -- Use same log2 witness based on k^n + t
      use Nat.log2 (k ^ n + t) + 1
      set M := Nat.log2 (k ^ n + t) + 1
      have hpos : 0 < k ^ n + t := by omega
      have hM_A : k ^ n + t < 2 ^ M := lt_pow_log2_succ _ hpos
      have hB_val : k' ^ n + t = 1 + t := by rw [hk'n1]
      have hM_B : 2 ^ M > k' ^ n + t := by
        rw [hB_val]
        calc 1 + t ≤ k ^ n + t := by omega
             _ < 2 ^ M := hM_A
      rcases Nat.lt_or_ge (k' ^ n + t) 2 with hB1 | hB2
      · -- k'^n + t = 1
        have hB_eq : k' ^ n + t = 1 := by omega
        have hB_rr : radRem M (k' ^ n + t) = 0 := by
          rw [hB_eq]; simp [radRem, irootN_one M (by omega)]
        have hA_rr : radRem M (k ^ n + t) = k ^ n + t - 1 :=
          radRem_large_grade M _ hM_A ha2
        rw [hA_rr, hB_rr]; omega
      · rw [radRem_large_grade M (k ^ n + t) hM_A ha2,
            radRem_large_grade M (k' ^ n + t) hM_B hB2]
        simp only [hk'n1]; omega
    · -- k'^n ≥ 2
      have hb2 : 2 ≤ k' ^ n + t := by omega
      use Nat.log2 (max (k ^ n + t) (k' ^ n + t)) + 1
      set M := Nat.log2 (max (k ^ n + t) (k' ^ n + t)) + 1
      have hmax_pos : 0 < max (k ^ n + t) (k' ^ n + t) := by omega
      have hlt : max (k ^ n + t) (k' ^ n + t) < 2 ^ M :=
        lt_pow_log2_succ _ hmax_pos
      have hm_a : 2 ^ M > k ^ n + t := (Nat.le_max_left _ _).trans_lt hlt
      have hm_b : 2 ^ M > k' ^ n + t := (Nat.le_max_right _ _).trans_lt hlt
      rw [radRem_large_grade M (k ^ n + t) hm_a ha2,
          radRem_large_grade M (k' ^ n + t) hm_b hb2]
      omega

/-- **Separation Theorem from Aod∞** (§5.3):
    For every distinct a, b ≥ 2, there exists m such that r_m(a) ≠ r_m(b). -/
theorem aodInf_separates (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ∃ m : ℕ, radRem m a ≠ radRem m b := by
  use a + b
  have ha_lt : a < 2 ^ (a + b) :=
    (lt_two_pow_self' a).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb_lt : b < 2 ^ (a + b) :=
    (lt_two_pow_self' b).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [radRem_large_grade (a + b) a ha_lt ha, radRem_large_grade (a + b) b hb_lt hb]
  omega

end Projection


/-! ─────────────────────────────────────────────────────────────────────────
    §6 — Tower Lemma: κ_{pn}(x) = κ_p(κ_n(x))
    ─────────────────────────────────────────────────────────────────────────

    For n, p ≥ 1 and every x:
      irootN (p * n) x = irootN p (irootN n x)
    (cf. §6.1 of the main paper)
    ───────────────────────────────────────────────────────────────────────── -/

section TowerLemma

/-- **Tower Lemma** (§6.1):
    irootN (p * n) x = irootN p (irootN n x). -/
theorem irootN_tower (p n x : ℕ) (hp : n ≠ 0) (hn : p ≠ 0) :
    irootN (p * n) x = irootN p (irootN n x) := by
  set m := irootN n x
  set j := irootN p m
  set pn := p * n
  have hpn_ne : pn ≠ 0 := Nat.mul_ne_zero hn hp
  apply Nat.le_antisymm
  · -- irootN pn x ≤ j: (irootN pn x)^p ≤ m, hence ≤ j = irootN p m
    have hirootpn_pn : (irootN pn x) ^ pn ≤ x := irootN_pow_le pn x hpn_ne
    -- (irootN pn x)^p ≤ m
    have hirootpn_p_le_m : (irootN pn x) ^ p ≤ m := by
      by_contra hlt; push_neg at hlt
      -- hlt : m < (irootN pn x)^p, i.e. m+1 ≤ (irootN pn x)^p
      -- → ((irootN pn x)^p)^n ≥ (m+1)^n > x ≥ (irootN pn x)^(pn)
      have hlt_succ : x < (m + 1) ^ n := irootN_lt_succ_pow n x hp
      have hge_n : (m + 1) ^ n ≤ ((irootN pn x) ^ p) ^ n :=
        Nat.pow_le_pow_left hlt n
      have heq_pn : ((irootN pn x) ^ p) ^ n = (irootN pn x) ^ pn := by
        rw [← pow_mul]
      linarith
    -- irootN pn x ≤ j = irootN p m: by_contra gives j < irootN pn x
    by_contra hlt; push_neg at hlt
    -- hlt : j < irootN pn x, i.e. j + 1 ≤ irootN pn x
    have hle_p : j + 1 ≤ irootN pn x := hlt
    have hjlt : m < (j + 1) ^ p := irootN_lt_succ_pow p m hn
    have hge : (j + 1) ^ p ≤ (irootN pn x) ^ p :=
      Nat.pow_le_pow_left hle_p p
    linarith
  · -- j ≤ irootN pn x: proved via j^pn ≤ x
    have hjp : j ^ p ≤ m := irootN_pow_le p m hn
    have hmn : m ^ n ≤ x := irootN_pow_le n x hp
    have hjpn : j ^ pn ≤ x := by
      calc j ^ pn = (j ^ p) ^ n := by rw [← pow_mul]
           _ ≤ m ^ n := Nat.pow_le_pow_left hjp n
           _ ≤ x := hmn
    by_contra hlt; push_neg at hlt
    -- hlt : irootN pn x < j, i.e. irootN pn x + 1 ≤ j
    have hle_pn : irootN pn x + 1 ≤ j := hlt
    have hle : (irootN pn x + 1) ^ pn ≤ j ^ pn :=
      Nat.pow_le_pow_left hle_pn pn
    linarith [irootN_lt_succ_pow pn x hpn_ne]

/-- Verifiable corollary: irootN 4 x = irootN 2 (irootN 2 x). -/
example (x : ℕ) : irootN 4 x = irootN 2 (irootN 2 x) := by
  have := irootN_tower 2 2 x (by norm_num) (by norm_num)
  simpa using this

/-- The non-preservation of equivalence along the tower:
    a ~ b [Aod n] does NOT imply in general a ~ b [Aod (pn)]. -/
theorem aodEquiv_not_preserved_tower :
    ¬ ∀ (p n a b : ℕ), 2 ≤ n → 2 ≤ p →
      a ≡ₒ b [Aod n] → a ≡ₒ b [Aod (p * n)] := by
  intro h
  -- Counterexample: n=2, p=2, a=5, b=2
  -- r_2(5) = 1 = r_2(2), but r_4(5) = 4 ≠ 1 = r_4(2)
  have hequiv : (5 : ℕ) ≡ₒ 2 [Aod 2] := by
    simp only [aodEquiv, radRem, irootN, irootAux]; norm_num
  have hbad := h 2 2 5 2 (by norm_num) (by norm_num) hequiv
  simp only [aodEquiv] at hbad
  norm_num [radRem, irootN, irootAux] at hbad

end TowerLemma


/-! ─────────────────────────────────────────────────────────────────────────
    §7 — Tower Theorem
    ─────────────────────────────────────────────────────────────────────────

    Aod_∞ is the projective limit of the tower (Aod_n)_{n≥2}.
    Tower Theorem: two distinct naturals ≥ 2 are separable at a
    level n ≤ log₂(max a b) + 1.

    Note: the formulation with min is false (14 violations on [2,79]).
    The correct formulation uses max: 0 violations on [2,79].
    Constructive proof: the witness n = log₂(max a b) + 1 always works
    via radRem_large_grade (already proved in §1).
    ───────────────────────────────────────────────────────────────────────── -/

section TowerConjecture

/-- Definition: a and b are separated by Aod_m if r_m(a) ≠ r_m(b). -/
def aodSeparates (m a b : ℕ) : Prop := radRem m a ≠ radRem m b

/-- Observation: a ≡ b [Aod m] ↔ ¬ aodSeparates m a b. -/
lemma aodSeparates_iff_not_equiv (m a b : ℕ) :
    aodSeparates m a b ↔ ¬ a ≡ₒ b [Aod m] := by
  simp [aodSeparates, aodEquiv]

/-- **Finite Separation Theorem**: for distinct a,b ≥ 2, there exists m
    (possibly large) such that Aod_m separates a from b. -/
theorem aodInf_separates' (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ∃ m : ℕ, aodSeparates m a b :=
  aodInf_separates a b ha hb hab

/-- **Tower Theorem** (proved):
    for a ≠ b with a, b ≥ 2, there exists n ≤ log₂(max a b) + 1
    such that Aod_n separates a from b.

    Proof: the witness n = M = log₂(max a b) + 1 satisfies 2^M > max(a,b),
    hence radRem M a = a - 1 and radRem M b = b - 1 by radRem_large_grade,
    and since a ≠ b we have radRem M a ≠ radRem M b. -/
theorem tower_separation (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ∃ n, n ≤ Nat.log2 (max a b) + 1 ∧ aodSeparates n a b := by
  refine ⟨Nat.log2 (max a b) + 1, le_refl _, ?_⟩
  simp only [aodSeparates]
  set M := Nat.log2 (max a b) + 1
  have hmax_pos : 0 < max a b := by omega
  have hM_gt : max a b < 2 ^ M := lt_pow_log2_succ _ hmax_pos
  have hMa : 2 ^ M > a := (Nat.le_max_left a b).trans_lt hM_gt
  have hMb : 2 ^ M > b := (Nat.le_max_right a b).trans_lt hM_gt
  rw [radRem_large_grade M a hMa ha, radRem_large_grade M b hMb hb]
  omega

end TowerConjecture


/-! ─────────────────────────────────────────────────────────────────────────
    §8 — Invariance of sepComp under τ_j at level n
    ─────────────────────────────────────────────────────────────────────────

    τ_j preserves equivalence in Aod_n: if a ≡ b [Aod n], then
    τ_j(a) ≡ τ_j(b) [Aod n]. As an immediate consequence,
    sepComp n (τ_j(a), τ_j(b)) = 0 for every pair equivalent in Aod_n.

    Note on the cross-degree drift (m ≠ n).  Since τ_j only shifts the
    chapter bases (k → k+j, h → h+j) while preserving the t-coordinate,
    the *asymptotic* drift is fully determined: for m large enough,
    sepComp m (τ_j a) (τ_j b) stabilizes to ((h+j)^n - (k+j)^n) — see
    `tauJ_sepComp_stabilizes` below, an immediate corollary of profile
    stabilization (§3).  The genuinely open part is the *transient*
    behaviour at intermediate degrees m (neither m = n nor m asymptotic),
    where irootN m ((k+j)^n + t) has no elementary closed form.
    ───────────────────────────────────────────────────────────────────────── -/

section TauJSepComp

/-- **Lemma**: τ_j sends pairs equivalent in Aod_n to equivalent pairs.
    Formally: sepComp n (tauJ n j a) (tauJ n j b) = 0
    for every pair k^n+t, h^n+t with k < h and t < gap(n,k). -/
theorem tauJ_preserves_sepComp_at_n (n j k h t : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht : t < gap n k) :
    sepComp n (tauJ n j (k ^ n + t)) (tauJ n j (h ^ n + t)) = 0 := by
  have hequiv : tauJ n j (k ^ n + t) ≡ₒ tauJ n j (h ^ n + t) [Aod n] :=
    tauJ_aodEquiv n j k h t hn hkh ht
  exact sepComp_eq_zero_at_n n _ _ hequiv

/-- Invariance of radRem under τ_j: radRem n (tauJ n j a) = radRem n a.
    Proof: writing a = k^n + t with k = irootN n a and t = radRem n a,
    tauJ n j a = (k+j)^n + t, and radRem n ((k+j)^n + t) = t. -/
lemma radRem_tauJ (n j a : ℕ) (hn : 2 ≤ n) :
    radRem n (tauJ n j a) = radRem n a := by
  have hnn : n ≠ 0 := by omega
  set k := irootN n a
  set t := radRem n a
  -- Canonical decomposition: a = k^n + t
  have hkn_le : k ^ n ≤ a := irootN_pow_le n a hnn
  have hdecomp : a = k ^ n + t := by
    have : t = a - k ^ n := radRem_eq_sub n a hnn
    omega
  -- t < gap n k (from the definition of gap)
  have ht_lt : t < gap n k := by
    simp only [t, k, gap]
    exact radRem_lt_gap n a hnn
  rw [hdecomp, tauJ_base_add n k j t hnn ht_lt]
  rw [radRem_base_add n (k + j) t hnn (gap_lt_of_add n k j t hn ht_lt)]

/-- Corollary: for any j and n ≥ 2, the n-th component of the separation
    vector is annihilated by the capitolar translations. -/
theorem tauJ_sepComp_at_n_zero_of_equiv (n j a b : ℕ) (hn : 2 ≤ n)
    (h : a ≡ₒ b [Aod n]) :
    sepComp n (tauJ n j a) (tauJ n j b) = 0 := by
  simp only [sepComp, radRem_tauJ n j a hn, radRem_tauJ n j b hn]
  simp only [aodEquiv] at h
  omega

/-- **Asymptotic cross-degree drift under τ_j** (partial resolution of the
    m ≠ n drift problem).  Since τ_j shifts the chapter bases by j while
    fixing the t-coordinate, for m large enough the m-th separation
    component of the translated pair stabilizes to the difference of the
    shifted bases: ((h+j)^n − (k+j)^n).  This is an immediate corollary of
    `sepComp_stabilizes` (§3) applied to the shifted bases k+j < h+j.
    The full transient law for intermediate m remains open. -/
theorem tauJ_sepComp_stabilizes (n j k h t : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (ht : t < gap n k)
    (ha2 : 2 ≤ (k + j) ^ n + t) :
    ∃ M : ℕ, ∀ m ≥ M,
      sepComp m (tauJ n j (k ^ n + t)) (tauJ n j (h ^ n + t))
        = ((h + j) ^ n : ℤ) - (k + j) ^ n := by
  have hnn : n ≠ 0 := by omega
  have ht_h : t < gap n h := lt_of_lt_of_le ht (gap_strictMono n hn k h hkh).le
  rw [tauJ_base_add n k j t hnn ht, tauJ_base_add n h j t hnn ht_h]
  exact sepComp_stabilizes n (k + j) (h + j) t hn (by omega)
    (gap_lt_of_add n k j t hn ht) ha2

end TauJSepComp

/-! ─────────────────────────────────────────────────────────────────────────
    §8b — Subtractive direction: sepComp under τ_{-j}

    The mirror of §8 for the subtractive capitolar translation τ_{-j} (tauNeg,
    defined in CapitolarGroupoid).  Like τ_j, τ_{-j} preserves the local
    coordinate r_n and therefore annihilates the n-th separation component of a
    same-offset pair.  The asymptotic cross-degree drift mirrors §8 with the
    bases shifted *down*: for m large enough,

        sepComp m (τ_{-j} a) (τ_{-j} b)  →  (h-j)^n − (k-j)^n.

    The qualitative contrast with the additive direction is the *offset bound*.
    τ_j shifts k ↦ k+j unconditionally and the drift (h+j)^n − (k+j)^n grows
    without bound in j.  τ_{-j} shifts k ↦ k-j and is constrained by the
    hypothesis `t < gap n (k-j)`: the offset t must still fit in the (narrower)
    target chapter k-j.  This caps the descent — one cannot translate an element
    with offset t below the first chapter whose width exceeds t — so the
    subtractive drift descends toward a floor rather than growing.  In the
    extreme admissible case the k-side approaches chapter 0 and the separation
    approaches the bare base difference.
    ───────────────────────────────────────────────────────────────────────── -/

section TauNegSepComp

/-- Invariance of radRem under τ_{-j} (general form):
    radRem n (tauNeg n j a _) = radRem n a, provided the offset radRem n a fits
    in the target chapter irootN n a − j.  Subtractive analogue of `radRem_tauJ`.

    -- Example: n=2, a=9 (k=3, t=0), j=1: irootN 2 9 = 3, gap(2,2)=5 > 0 = radRem 2 9. ✓ -/
lemma radRem_tauNeg (n j a : ℕ) (hn : 2 ≤ n) (hja : j ≤ irootN n a)
    (hfit : radRem n a < gap n (irootN n a - j)) :
    radRem n (tauNeg n j a hja) = radRem n a := by
  -- unfold tauNeg to coordinate form (avoids the dependent-argument motive issue)
  simp only [tauNeg]
  exact radRem_base_add n (irootN n a - j) (radRem n a) (by omega) hfit

/-- **Corollary**: τ_{-j} annihilates the n-th separation component of any pair
    that is equivalent in Aod_n (general form). Subtractive analogue of
    `tauJ_sepComp_at_n_zero_of_equiv`.

    -- Example: n=2, a=9, b=16 (both r₂ = 0, so 9 ≡ₒ 16 [Aod 2]), j=1:
    --   irootN 2 9 = 3 ≥ 1, irootN 2 16 = 4 ≥ 1, offsets 0 fit. ✓ -/
theorem tauNeg_sepComp_at_n_zero_of_equiv (n j a b : ℕ) (hn : 2 ≤ n)
    (hja : j ≤ irootN n a) (hjb : j ≤ irootN n b)
    (hfa : radRem n a < gap n (irootN n a - j))
    (hfb : radRem n b < gap n (irootN n b - j))
    (h : a ≡ₒ b [Aod n]) :
    sepComp n (tauNeg n j a hja) (tauNeg n j b hjb) = 0 := by
  simp only [sepComp, radRem_tauNeg n j a hn hja hfa, radRem_tauNeg n j b hn hjb hfb]
  simp only [aodEquiv] at h
  omega

/-- **Lemma**: τ_{-j} sends a same-offset pair k^n+t, h^n+t (with k < h) to an
    Aod_n-equivalent pair — its n-th separation component is 0. Coordinate-form
    mirror of `tauJ_preserves_sepComp_at_n`.

    The hypothesis `t < gap n (k-j)` is the offset bound: t must fit in the
    target chapter k-j (it then fits in h-j as well, since gap is increasing).

    -- Example: n=2, k=2, h=3, j=1, t=1: 1 ≤ 2, 2 < 3, 1 < gap(2,2)=5, 1 < gap(2,1)=3. ✓ -/
theorem tauNeg_preserves_sepComp_at_n (n j k h t : ℕ) (hn : 2 ≤ n)
    (hjk : j ≤ k) (hkh : k < h) (ht : t < gap n k) (htkj : t < gap n (k - j)) :
    sepComp n
      (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht]))
      (tauNeg n j (h ^ n + t) (by
        rw [sum_in_chapter n h t (by omega)
          (lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh))]; omega))
      = 0 := by
  have hnn : n ≠ 0 := by omega
  have ht_h : t < gap n h := lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh)
  have hthj : t < gap n (h - j) :=
    lt_of_lt_of_le htkj (gap_le_of_lt n (k - j) (h - j) hn (by omega))
  simp only [sepComp, tauNeg,
    sum_in_chapter n k t hnn ht, radRem_base_add n k t hnn ht,
    sum_in_chapter n h t hnn ht_h, radRem_base_add n h t hnn ht_h,
    radRem_base_add n (k - j) t hnn htkj, radRem_base_add n (h - j) t hnn hthj,
    sub_self]

/-- **Asymptotic cross-degree drift under τ_{-j}** (subtractive analogue of
    `tauJ_sepComp_stabilizes`).  Since τ_{-j} shifts the chapter bases down by j
    while fixing the offset t, for m large enough the m-th separation component
    of the translated pair stabilizes to the difference of the *lowered* bases:
    ((h-j)^n − (k-j)^n).  Immediate corollary of `sepComp_stabilizes` applied to
    the shifted bases k-j < h-j.

    Contrast with the additive drift ((h+j)^n − (k+j)^n): the descent is bounded
    by the offset hypothesis `t < gap n (k-j)`.

    -- Example: n=2, k=2, h=3, j=1, t=1 → bases 1 < 2, drift = 2² − 1² = 3
    --   (cf. `#eval sepComp 10 2 5` below). -/
theorem tauNeg_sepComp_stabilizes (n j k h t : ℕ) (hn : 2 ≤ n)
    (hjk : j ≤ k) (hkh : k < h) (ht : t < gap n k) (htkj : t < gap n (k - j))
    (ha2 : 2 ≤ (k - j) ^ n + t) :
    ∃ M : ℕ, ∀ m ≥ M,
      sepComp m
        (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht]))
        (tauNeg n j (h ^ n + t) (by
          rw [sum_in_chapter n h t (by omega)
            (lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh))]; omega))
        = (((h - j) ^ n : ℕ) : ℤ) - (((k - j) ^ n : ℕ) : ℤ) := by
  have hnn : n ≠ 0 := by omega
  have ht_h : t < gap n h := lt_of_lt_of_le ht (gap_le_of_lt n k h hn hkh)
  -- reduce both tauNeg images to coordinate form via tauNeg_base_add
  -- (rw matches across differing proof terms by proof irrelevance; cf. tauNeg_right_inverse)
  rw [tauNeg_base_add n k j t hnn ht hjk,
      tauNeg_base_add n h j t hnn ht_h (by omega)]
  exact sepComp_stabilizes n (k - j) (h - j) t hn (by omega) htkj ha2

-- Sanity check: subtracted pair (1²+1, 2²+1) = (2,5); at large degree the
-- separation stabilizes to (h-j)² − (k-j)² = 2² − 1² = 3.
#eval sepComp 10 2 5     -- 3

end TauNegSepComp

-- ================================================================
-- §9 — FourDiamond D4 — Capitolar profile monoid constraint
-- ================================================================

section ProfileMonoide

/-- **D4 (FourDiamond): Capitolar profile monoid constraint.**
    For n ∣ m with n ≠ 0 and m/n ≠ 0:
      irootN m a = irootN (m / n) (irootN n a).
    This is the Tower Lemma (§6) specialized to the case n ∣ m:
    the capitolar profile is determined by the prime degrees, and the
    composite degrees are obtained by composing the maps of the prime degrees.
    -- Example: n=2, m=6, a=64: irootN 6 64 = 2, irootN 3 (irootN 2 64) = irootN 3 8 = 2. ✓
    -- (n=2 ≠ 0, m/n = 3 ≠ 0, 2 ∣ 6) -/
theorem profile_monoide_constraint (a n m : ℕ) (hn : n ≠ 0) (hdvd : n ∣ m)
    (hq : m / n ≠ 0) :
    irootN m a = irootN (m / n) (irootN n a) := by
  obtain ⟨p, rfl⟩ := hdvd
  -- After substitution m = n * p; m / n = p (since n ≠ 0)
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)] at hq ⊢
  -- hq : p ≠ 0 (after rw); goal: irootN (n * p) a = irootN p (irootN n a)
  rw [mul_comm]
  exact irootN_tower p n a hn hq

end ProfileMonoide

/-! ─────────────────────────────────────────────────────────────────────────
    §10 — General (n,m)-Bigraded Cells
    ─────────────────────────────────────────────────────────────────────────

    The (n,m)-bigraded cell centered at c_n is the intersection
      C(n,m,c_n) := [c_n^n, (c_n+1)^n) ∩ [c_m^m, (c_m+1)^m)
    where c_m = irootN m (c_n^n) = ⌊c_n^{n/m}⌋.

    From irootN_pow_le it follows that c_m^m ≤ c_n^n, hence max(c_n^n, c_m^m) = c_n^n
    and the width reduces to:
      biGradedCellSize n m c_n = min((c_n+1)^n, (c_m+1)^m) - c_n^n.

    Formula (FourDiamond §D2, Thm 2.6 generalized):
    • Full cell:    (c_n+1)^n ≤ (c_m+1)^m  →  width = gap(n, c_n)
    • Jump cell:    (c_m+1)^m < (c_n+1)^n  →  width = (c_m+1)^m - c_n^n

    Connection with §4: the discontinuitySet D(k,h,n) corresponds exactly to
    the degrees m for which the bigraded cell of c_n = k is of "jump" type
    with respect to degree n.
    ───────────────────────────────────────────────────────────────────────── -/

section BiGradedCell

/-- Width of the (n,m)-bigraded cell centered at c_n.
    c_m = irootN m (c_n^n) is the degree-m chapter containing c_n^n. -/
def biGradedCellSize (n m c_n : ℕ) : ℕ :=
  let c_m := irootN m (c_n ^ n)
  min ((c_n + 1) ^ n) ((c_m + 1) ^ m) - c_n ^ n

#eval (List.range 15).map (fun i => (i + 1, biGradedCellSize 2 3 (i + 1)))
#eval (List.range 10).map (fun i => (i + 1, biGradedCellSize 2 5 (i + 1)))
#eval (List.range 8).map  (fun i => (i + 1, biGradedCellSize 3 5 (i + 1)))

/-- The upper boundary strictly exceeds c_n^n: the cell is always nonempty (step 1). -/
private lemma biGradedCellSize_hi_gt (n m c_n : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    c_n ^ n < min ((c_n + 1) ^ n) ((irootN m (c_n ^ n) + 1) ^ m) := by
  rw [lt_min_iff]
  exact ⟨Nat.pow_lt_pow_left (by omega) hn,
         irootN_lt_succ_pow m (c_n ^ n) hm⟩

/-- **Full cell**: if (c_n+1)^n ≤ (c_m+1)^m, width = gap(n, c_n). -/
theorem biGradedCellSize_full (n m c_n : ℕ)
    (hfull : (c_n + 1) ^ n ≤ (irootN m (c_n ^ n) + 1) ^ m) :
    biGradedCellSize n m c_n = gap n c_n := by
  simp only [biGradedCellSize, gap]
  rw [min_eq_left hfull]

/-- **Jump cell**: if (c_m+1)^m < (c_n+1)^n, width = (c_m+1)^m - c_n^n. -/
theorem biGradedCellSize_jump (n m c_n : ℕ)
    (hjump : (irootN m (c_n ^ n) + 1) ^ m < (c_n + 1) ^ n) :
    biGradedCellSize n m c_n = (irootN m (c_n ^ n) + 1) ^ m - c_n ^ n := by
  simp only [biGradedCellSize]
  rw [min_eq_right (Nat.le_of_lt hjump)]

/-- **Formula of the (n,m)-bigraded cell** (Thm 2.6 generalized). -/
theorem biGradedCellSize_formula (n m c_n : ℕ) :
    let c_m := irootN m (c_n ^ n)
    biGradedCellSize n m c_n =
      if (c_n + 1) ^ n ≤ (c_m + 1) ^ m
      then gap n c_n
      else (c_m + 1) ^ m - c_n ^ n := by
  simp only
  split_ifs with h
  · exact biGradedCellSize_full n m c_n h
  · push_neg at h; exact biGradedCellSize_jump n m c_n h

/-- The cell is always nonempty. -/
theorem biGradedCellSize_pos (n m c_n : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    0 < biGradedCellSize n m c_n :=
  Nat.sub_pos_of_lt (biGradedCellSize_hi_gt n m c_n hn hm)

/-- gap 2 k = 2*k + 1. -/
lemma gap_two_eq (k : ℕ) : gap 2 k = 2 * k + 1 := by
  simp only [gap]; zify [Nat.pow_le_pow_left (Nat.le_succ k) 2]; ring

/-- Alias for the (2,3) case of the original document. -/
abbrev cellSize23 (c₂ : ℕ) : ℕ := biGradedCellSize 2 3 c₂

/-- Full (2,3) case: width = 2*c₂+1. -/
theorem cellSize23_full (c₂ : ℕ)
    (hfull : (c₂ + 1) ^ 2 ≤ (irootN 3 (c₂ ^ 2) + 1) ^ 3) :
    cellSize23 c₂ = 2 * c₂ + 1 := by
  rw [cellSize23, biGradedCellSize_full 2 3 c₂ hfull, gap_two_eq]

end BiGradedCell


/-! ─────────────────────────────────────────────────────────────────────────
    §9 — Cross-Degree Coincidence Blocks at Common Perfect Powers
    ─────────────────────────────────────────────────────────────────────────

    Specialization of the bigraded cell dichotomy (`biGradedCellSize_formula`)
    to the case in which the two chapter bases coincide. This happens exactly
    at the shared perfect L-th powers, with L = lcm(n₁, n₂): the base of
    degree n₁ is m^(L/n₁), and (m^(L/n₁))^{n₁} = m^L. Analogously for n₂. Both
    bases raised to their respective exponents yield the same number m^L.

    In that window (t < min of the two chapter gaps) the two radRem coincide
    **literally**, not merely co-localize in the same cell.

    Main results:
      · `pow_lcm_div_eq`  : (m^(L/n))^n = m^L  for n ∣ L.
      · `crossDegree_coincidence` : both radRem equal exactly t.
      · `crossDegree_radRem_eq`   : the two radRem coincide.
      · `coincidenceBlockSize`    : width of the coincidence window.
      · `crossDegree_coincidence_block` : unified form via `coincidenceBlockSize`.
    ───────────────────────────────────────────────────────────────────────── -/

section CoincidenceBlock

/-- If n ∣ L, then (m^(L/n))^n = m^L. -/
lemma pow_lcm_div_eq (n m L : ℕ) (_hn : n ≠ 0) (hdvd : n ∣ L) :
    (m ^ (L / n)) ^ n = m ^ L := by
  rw [← pow_mul, Nat.div_mul_cancel hdvd]

/-- **Cross-Degree Coincidence Block**: for n₁, n₂ ≠ 0, setting L = lcm(n₁, n₂)
    and k_i = m^(L/n_i), if t < gap(n_i, k_i) for both i = 1, 2, then
    `radRem n₁ (m^L + t) = radRem n₂ (m^L + t) = t`.

    Proof: k_i^{n_i} = m^L via `pow_lcm_div_eq`, so each radRem reduces to
    `radRem_base_add`. -/
theorem crossDegree_coincidence (n₁ n₂ m t : ℕ)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (ht₁ : t < gap n₁ (m ^ (Nat.lcm n₁ n₂ / n₁)))
    (ht₂ : t < gap n₂ (m ^ (Nat.lcm n₁ n₂ / n₂))) :
    radRem n₁ (m ^ Nat.lcm n₁ n₂ + t) = t ∧
    radRem n₂ (m ^ Nat.lcm n₁ n₂ + t) = t := by
  set L := Nat.lcm n₁ n₂
  have hdvd₁ : n₁ ∣ L := Nat.dvd_lcm_left n₁ n₂
  have hdvd₂ : n₂ ∣ L := Nat.dvd_lcm_right n₁ n₂
  have h1 : (m ^ (L / n₁)) ^ n₁ = m ^ L := pow_lcm_div_eq n₁ m L hn₁ hdvd₁
  have h2 : (m ^ (L / n₂)) ^ n₂ = m ^ L := pow_lcm_div_eq n₂ m L hn₂ hdvd₂
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact radRem_base_add n₁ (m ^ (L / n₁)) t hn₁ ht₁
  · rw [← h2]; exact radRem_base_add n₂ (m ^ (L / n₂)) t hn₂ ht₂

/-- The two radRem coincide in the min-gap window (corollary of `crossDegree_coincidence`). -/
theorem crossDegree_radRem_eq (n₁ n₂ m t : ℕ)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (ht₁ : t < gap n₁ (m ^ (Nat.lcm n₁ n₂ / n₁)))
    (ht₂ : t < gap n₂ (m ^ (Nat.lcm n₁ n₂ / n₂))) :
    radRem n₁ (m ^ Nat.lcm n₁ n₂ + t) = radRem n₂ (m ^ Nat.lcm n₁ n₂ + t) := by
  obtain ⟨h1, h2⟩ := crossDegree_coincidence n₁ n₂ m t hn₁ hn₂ ht₁ ht₂
  rw [h1, h2]

/-- Width of the coincidence block: min of the two gaps at the shared chapter bases. -/
def coincidenceBlockSize (n₁ n₂ m : ℕ) : ℕ :=
  min (gap n₁ (m ^ (Nat.lcm n₁ n₂ / n₁)))
      (gap n₂ (m ^ (Nat.lcm n₁ n₂ / n₂)))

#eval coincidenceBlockSize 2 3 1   -- min(gap 2 1, gap 3 1) = min(3, 7) = 3
#eval coincidenceBlockSize 2 3 2   -- L=6; k₁=8, k₂=4; min(gap 2 8, gap 3 4) = min(17, 61) = 17
#eval coincidenceBlockSize 2 3 3   -- L=6; k₁=27, k₂=9; min(gap 2 27, gap 3 9) = min(55, 271) = 55
#eval coincidenceBlockSize 2 5 2   -- L=10; k₁=2^5=32, k₂=2^2=4; min(gap 2 32, gap 3 4) = min(65, 61)
#eval coincidenceBlockSize 3 5 2   -- L=15; k₁=2^5=32, k₂=2^3=8; min(gap 3 32, gap 5 8) = min(3169, …)

/-- Unified formulation: in the window [0, coincidenceBlockSize) the radRem coincide. -/
theorem crossDegree_coincidence_block (n₁ n₂ m t : ℕ)
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (ht : t < coincidenceBlockSize n₁ n₂ m) :
    radRem n₁ (m ^ Nat.lcm n₁ n₂ + t) = radRem n₂ (m ^ Nat.lcm n₁ n₂ + t) := by
  rw [coincidenceBlockSize, lt_min_iff] at ht
  exact crossDegree_radRem_eq n₁ n₂ m t hn₁ hn₂ ht.1 ht.2

/-- The block is always nonempty: both gaps are positive. -/
theorem coincidenceBlockSize_pos (n₁ n₂ m : ℕ) (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) :
    0 < coincidenceBlockSize n₁ n₂ m := by
  rw [coincidenceBlockSize]
  refine lt_min_iff.mpr ⟨?_, ?_⟩
  · exact gap_pos' n₁ (m ^ (Nat.lcm n₁ n₂ / n₁)) hn₁
  · exact gap_pos' n₂ (m ^ (Nat.lcm n₁ n₂ / n₂)) hn₂

end CoincidenceBlock

end CampiOperazionistici
