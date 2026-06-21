/-
  CapitolarTransportStructure.lean — CampiOperazionistici

  Paper: §16 (The Capitolar Groupoid and Transport of Structure)

  Transport of the chapter group structure along capitolar translations.

  Studies how the capAdd / capMul operations from GroupStructure.lean interact with
  the τ_j family from CapitolarTranslations.lean.

  **Central finding**: τ_j is a *coordinate-preserving horizontal lift* — it moves
  the chapter index while keeping the local coordinate (radRem) intact.  However,
  it does NOT intertwine capAdd across chapters, because the chapter gap changes:
  capAdd in chapter k operates modulo capGap n k, while capAdd in chapter k+j
  operates modulo capGap n (k+j) ≠ capGap n k (for j > 0, n ≥ 2).

  The obstruction is concrete and quantified exactly:

    obstruction(n,k,j,r,s) = [(k+j)^n + r + s] mod capGap n (k+j)
                             − [k^n + r + s]  mod capGap n k

  which is nonzero whenever the two moduli differ and r+s is in a "conflict zone".

  **Positive result**: τ_j induces an injective map on local coordinates,
  tauJ_Fin : Fin (capGap n k) → Fin (capGap n (k+j)), sending each local coordinate
  to the same value.  The image has size capGap n k, leaving exactly
  capGap n (k+j) − capGap n k elements of chapter k+j unreachable from chapter k
  via a single τ_j.  These are the "new" elements created by the widening gap.

  **Imports**:
  - CampiOperazionistici.GroupStructure    (capAdd, capMul, capGap, …)
  - CampiOperazionistici.CapitolarTranslations  (tauJ, tauJ_base_add, …)

  GroupStructure uses `capGap`; CampiOperazionistici uses `gap`.  Both equal
  (k+1)^n − k^n.  The first lemma reconciles them.

  **Section ordering**:
  §1  Reconciling capGap and gap
  §2  τ_j as a Coordinate-Preserving Horizontal Lift
  §3  τ_j as an Injective Coordinate Embedding (tauJ_Fin definition)
  §4  The capAdd Obstruction (tauJ_Fin does not intertwine capAdd)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.GroupStructure
import CampiOperazionistici.TranslationReencounter
import CampiOperazionistici.CapitolarTranslations
import CampiOperazionistici.FirstOccurrence

namespace CampiOperazionistici

/-! ─────────────────────────────────────────────────────────────────────────
    §1  Reconciling capGap and gap
    ─────────────────────────────────────────────────────────────────────────
    GroupStructure defines `capGap n k := (k+1)^n − k^n`.
    CampiOperazionistici defines `gap n k := (k+1)^n − k^n`.
    They are definitionally equal.
    ───────────────────────────────────────────────────────────────────────── -/

section CapGapReconciliation

lemma capGap_eq_gap (n k : ℕ) : capGap n k = gap n k := by
  simp [capGap, gap]

lemma gap_eq_capGap (n k : ℕ) : gap n k = capGap n k :=
  (capGap_eq_gap n k).symm

/-- capGap is strictly monotone in k for n ≥ 2 (from gap_strictMono). -/
lemma capGap_strictMono (n : ℕ) (hn : 2 ≤ n) (k j : ℕ) (hkj : k < j) :
    capGap n k < capGap n j := by
  rw [capGap_eq_gap, capGap_eq_gap]; exact gap_strictMono n hn k j hkj

/-- capGap n (k+j) > capGap n k for j > 0 and n ≥ 2.
    This is the arithmetic root of the capAdd obstruction. -/
lemma capGap_lt_of_add (n k j : ℕ) (hn : 2 ≤ n) (hj : 0 < j) :
    capGap n k < capGap n (k + j) := by
  rw [capGap_eq_gap, capGap_eq_gap]; exact gap_strictMono n hn k (k + j) (by omega)

end CapGapReconciliation

/-! ─────────────────────────────────────────────────────────────────────────
    §2  τ_j as a Coordinate-Preserving Horizontal Lift

    Think of ℕ as a "chapter bundle": the base is the chapter index (irootN n)
    and the fiber over k is {a | irootN n a = k} with local coordinate radRem n.

    τ_j is a **horizontal lift**: it changes the base (chapter) by j while
    keeping the fiber coordinate (radRem) unchanged.  In bundle language,
    τ_j is a section of the chapter projection along the direction j.
    ───────────────────────────────────────────────────────────────────────── -/

section HorizontalLift

/-- **radRem is preserved by τ_j** (on elements in canonical form k^n+t).
    The local coordinate is a complete invariant of the fiber: it is
    unchanged when the chapter index shifts. -/
theorem tauJ_radRem_eq (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    radRem n (tauJ n j (k ^ n + t)) = t := by
  have hnn : n ≠ 0 := by omega
  rw [tauJ_base_add n k j t hnn ht]
  exact radRem_base_add n (k + j) t hnn (gap_lt_of_add n k j t hn ht)

/-- **Chapter index advances by j**: τ_j moves the chapter index from k to k+j. -/
theorem tauJ_chapter_eq (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    irootN n (tauJ n j (k ^ n + t)) = k + j := by
  have hnn : n ≠ 0 := by omega
  rw [tauJ_base_add n k j t hnn ht]
  exact sum_in_chapter n (k + j) t hnn (gap_lt_of_add n k j t hn ht)

/-- **radRem invariance in general form** (without assuming canonical decomposition).
    For any a : ℕ, radRem n (τ_j(a)) = radRem n a. -/
theorem tauJ_radRem_general (n j a : ℕ) (hn : 2 ≤ n) :
    radRem n (tauJ n j a) = radRem n a := by
  have hnn : n ≠ 0 := by omega
  -- Decompose a into its chapter and local coordinate
  have hle := irootN_pow_le n a hnn
  have hlt := irootN_lt_succ_pow n a hnn
  have ht_bound : radRem n a < gap n (irootN n a) := by simp [gap, radRem]; omega
  have ha : a = (irootN n a) ^ n + radRem n a := by simp [radRem]; omega
  conv_lhs => rw [ha]
  exact tauJ_radRem_eq n (irootN n a) j (radRem n a) hn ht_bound

end HorizontalLift

/-! ─────────────────────────────────────────────────────────────────────────
    §3  τ_j as an Injective Coordinate Embedding

    Although τ_j breaks the modular group structure, it has a clean positive story
    on local coordinates: it sends Fin(capGap n k) into Fin(capGap n (k+j)) by the
    identity function on values.  This embedding is injective (trivially), and its
    image is exactly the "small coordinates" {0, …, capGap n k − 1} of chapter k+j.

    The remaining capGap n (k+j) − capGap n k local coordinates of chapter k+j are
    "new": they belong to elements in chapter k+j that cannot be reached from
    chapter k by a single τ_j.  These are the "growth elements" added by the
    widening gap.
    ───────────────────────────────────────────────────────────────────────── -/

section CoordinateEmbedding

/-- **tauJ_Fin**: the embedding of local coordinates from chapter k into chapter k+j.
    Since capGap n k < capGap n (k+j) (for j > 0, n ≥ 2), any local coord of chapter k
    is a valid local coord of chapter k+j.  τ_j acts as the identity on coord values. -/
def tauJ_Fin (n k j : ℕ) (hn : 2 ≤ n) (r : Fin (capGap n k)) : Fin (capGap n (k + j)) :=
  ⟨r.val, by
    rcases Nat.eq_or_lt_of_le (Nat.zero_le j) with rfl | hj
    · simp [capGap_eq_gap]; exact r.isLt  -- j = 0: capGap n (k+0) = capGap n k
    · exact Nat.lt_of_lt_of_le r.isLt (Nat.le_of_lt (capGap_lt_of_add n k j hn hj))⟩

/-- **tauJ_Fin is injective**: different local coords stay different. -/
theorem tauJ_Fin_injective (n k j : ℕ) (hn : 2 ≤ n) :
    Function.Injective (tauJ_Fin n k j hn) := by
  intro r s h; simp [tauJ_Fin] at h; exact Fin.ext h

/-- **Consistency**: tauJ n j of the k-th chapter embedding equals the (k+j)-th chapter embedding.
    In other words, localCoord and tauJ_Fin commute with the chapter translation. -/
theorem tauJ_Fin_consistent (n k j : ℕ) (hn : 2 ≤ n) (r : Fin (capGap n k)) :
    tauJ n j (k ^ n + r.val) = (k + j) ^ n + (tauJ_Fin n k j hn r).val := by
  have hnn : n ≠ 0 := by omega
  have hr : r.val < gap n k := by rw [← capGap_eq_gap]; exact r.isLt
  rw [tauJ_base_add n k j r.val hnn hr]
  simp [tauJ_Fin]

/-- **Image size**: the image of tauJ_Fin has exactly capGap n k elements inside chapter k+j,
    while chapter k+j has capGap n (k+j) elements total.
    The "new" elements (unreachable from chapter k via τ_j) number
    capGap n (k+j) − capGap n k. -/
theorem tauJ_image_complement_size (n k j : ℕ) (hn : 2 ≤ n) (hj : 0 < j) :
    capGap n k + (capGap n (k + j) - capGap n k) = capGap n (k + j) := by
  have hlt := capGap_lt_of_add n k j hn hj; omega

end CoordinateEmbedding

/-! ─────────────────────────────────────────────────────────────────────────
    §4  The capAdd Obstruction

    capAdd in chapter k computes modulo capGap n k.
    capAdd in chapter k+j computes modulo capGap n (k+j).
    Since capGap n (k+j) > capGap n k for j > 0 (the gaps grow),
    the two operations are NOT interchangeable via τ_j.

    Explicit formula for the two competing quantities (for r, s : Fin (capGap n k)):

    τ_j-image of capAdd in chapter k:
      tauJ n j (k^n + (k^n + r + s) mod capGap n k)
      = (k+j)^n + (k^n + r + s) mod capGap n k    [local coord preserved by τ_j]

    capAdd in chapter k+j of the τ_j-images:
      (k+j)^n + ((k+j)^n + r + s) mod capGap n (k+j)

    These are equal iff the two modular reductions coincide, which requires
    (k+j)^n ≡ k^n (mod capGap n k) — a condition that fails in general.
    ───────────────────────────────────────────────────────────────────────── -/

section CapAddObstruction

/-- The local coordinate of a capAdd result. -/
lemma capAdd_val_eq (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    (capAdd n k hn r s).val = (k ^ n + r.val + s.val) % capGap n k := rfl

/-- The local coordinate of the τ_j-image is the same as the original. -/
lemma tauJ_fin_radRem (n k j : ℕ) (hn : 2 ≤ n) (r : Fin (capGap n k)) :
    radRem n (tauJ n j (k ^ n + r.val)) = r.val := by
  have hnn : n ≠ 0 := by omega
  have hr : r.val < gap n k := by rw [← capGap_eq_gap]; exact r.isLt
  exact tauJ_radRem_eq n k j r.val hn hr

/-- **The capAdd obstruction formula**:
    The local coordinate of capAdd_{k+j}(tauJ_Fin r, tauJ_Fin s) is
      ((k+j)^n + r + s) mod capGap n (k+j)
    while the local coordinate of tauJ_Fin(capAdd_k(r, s)) is
      (k^n + r + s) mod capGap n k.
    These differ whenever the two moduli differ (i.e., j > 0, n ≥ 2).

    This lemma computes the left-hand side; the counterexample below shows they diverge. -/
lemma capAdd_in_target_chapter (n k j : ℕ) (hn2 : 2 ≤ n) (r s : Fin (capGap n k)) :
    (capAdd n (k + j) (by omega) (tauJ_Fin n k j hn2 r) (tauJ_Fin n k j hn2 s)).val =
    ((k + j) ^ n + r.val + s.val) % capGap n (k + j) := by
  simp [capAdd, tauJ_Fin]

/-- **Explicit counterexample**: for n=2, k=1, j=1, r=s=1:

    Chapter 1: capGap 2 1 = 3, capAdd(1,1) has local coord (1+1+1)%3 = 0.
    After τ_1: τ_1(1^2+0) = 4 = 2^2+0, local coord 0.

    Chapter 2: capGap 2 2 = 5, capAdd(1,1) in chapter 2 has local coord (4+1+1)%5 = 1.

    So the local coord of [capAdd_2(τ_1(r), τ_1(s))] = 1
    while the local coord of [τ_1(capAdd_1(r,s))]     = 0.

    This proves τ_1 does NOT intertwine capAdd_1 and capAdd_2. -/
theorem capAdd_tauJ_fails_n2_k1 :
    -- In chapter 1: capAdd of local coords (1,1) gives local coord 0
    (capAdd 2 1 (by norm_num) ⟨1, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩).val = 0 ∧
    -- In chapter 2: capAdd of local coords (1,1) gives local coord 1
    (capAdd 2 2 (by norm_num) ⟨1, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩).val = 1 ∧
    -- The two are different: τ_1 does NOT intertwine capAdd
    (capAdd 2 1 (by norm_num) ⟨1, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩).val ≠
    (capAdd 2 2 (by norm_num) ⟨1, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩).val := by
  decide

/-- **tauJ_Fin does not intertwine capAdd in general**.
    The image of tauJ_Fin is closed under neither addition nor multiplication
    modulo capGap n (k+j) (since the modulus is larger).

    Specifically: tauJ_Fin(r) + tauJ_Fin(s) mod capGap n (k+j) need not equal
    tauJ_Fin(r + s mod capGap n k), because the reduction moduli differ.

    The `capAdd_tauJ_fails_n2_k1` counterexample above is a concrete instance for n=2. -/
theorem tauJ_Fin_not_additive :
    ¬ ∀ (k j : ℕ) (r s : Fin (capGap 2 k)),
      (tauJ_Fin 2 k j (by norm_num) (capAdd 2 k (by omega) r s)).val =
      (capAdd 2 (k + j) (by omega)
        (tauJ_Fin 2 k j (by norm_num) r) (tauJ_Fin 2 k j (by norm_num) s)).val := by
  intro h
  -- Specialize to k=1, j=1, r=s=⟨1,_⟩
  have h₁ := h 1 1 ⟨1, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩
  norm_num [capAdd, tauJ_Fin, capGap] at h₁

/-!
### General non-additivity for all n ≥ 2

The n=2 proof above works by `decide`.  Here we give a uniform proof for every n ≥ 2
using a concrete counterexample with k=1, j=1, r=s=⟨0,_⟩ together with two key facts:
- `1 % (2^n − 1) = 1`  (since 1 < 2^n − 1 for n ≥ 2)
- `2^n % (3^n − 2^n) = 2^n`  (since 2^n < 3^n − 2^n for n ≥ 2)
These imply `1 ≠ 2^n` (since 2^n ≥ 4 for n ≥ 2), giving the contradiction.
-/

/-- For n ≥ 2, `2 · 2^n < 3^n` (equivalently, `2^(n+1) < 3^n`).
    Proved by induction: base n=2 gives 8 < 9; step uses 3·3^n > 2·2^(n+1). -/
private lemma two_mul_two_pow_lt_three_pow (n : ℕ) (hn : 2 ≤ n) : 2 * 2^n < 3^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn2 : 2 ≤ n
    · have h1 := ih hn2
      have h3n : (3:ℕ)^n > 0 := pow_pos (by norm_num) n
      linarith [show 3^(n+1) = 3 * 3^n from by ring,
                show 2^(n+1) = 2 * 2^n from by ring]
    · -- hn : 2 ≤ n+1 and ¬(2 ≤ n) so n = 1
      have hn1 : n = 1 := by omega
      subst hn1; norm_num

/-- **General non-additivity** of `tauJ_Fin` with respect to `capAdd`, for all n ≥ 2.

    For every n ≥ 2, there exist chapter k=1, shift j=1, and local coordinates r=s=0
    such that τ_j does NOT intertwine `capAdd_1` and `capAdd_2`:
    - In chapter 1 with modulus `2^n−1`: `(1+0+0) mod (2^n−1) = 1`
    - In chapter 2 with modulus `3^n−2^n`: `(2^n+0+0) mod (3^n−2^n) = 2^n`
    These differ because `1 ≠ 2^n` for n ≥ 2.

    This generalises `tauJ_Fin_not_additive` (which was fixed to n=2). -/
theorem tauJ_Fin_not_additive_general (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ (k j : ℕ) (r s : Fin (capGap n k)),
      (tauJ_Fin n k j hn (capAdd n k (by omega) r s)).val =
      (capAdd n (k + j) (by omega)
        (tauJ_Fin n k j hn r) (tauJ_Fin n k j hn s)).val := by
  intro hall
  have hnn : n ≠ 0 := by omega
  -- Specialize to k=1, j=1, r=s=⟨0,_⟩
  have h1 := hall 1 1 ⟨0, by simp [capGap, hnn]⟩ ⟨0, by simp [capGap, hnn]⟩
  simp only [capAdd, tauJ_Fin, capGap] at h1
  -- After simp: h1 : (1^n + 0 + 0) % ((1+1)^n - 1^n) = ((1+1)^n+0+0) % ((1+1+1)^n - (1+1)^n)
  -- Use norm_num to reduce 1+1 → 2, 1+1+1 → 3, 1^n → 1
  norm_num at h1
  -- Now h1 : 1 % (2^n - 1) = 2^n % (3^n - 2^n)
  -- Compute LHS = 1
  have hLHS : (1 : ℕ) % (2^n - 1) = 1 := by
    apply Nat.mod_eq_of_lt
    have h4 : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hn
    norm_num at h4; omega
  -- Compute RHS = 2^n
  have hRHS : (2:ℕ)^n % (3^n - 2^n) = 2^n := by
    apply Nat.mod_eq_of_lt
    have h := two_mul_two_pow_lt_three_pow n hn
    have h2le : 2^n ≤ 3^n := Nat.pow_le_pow_left (by norm_num) n
    omega
  rw [hLHS, hRHS] at h1
  -- h1 : 1 = 2^n, but 2^n ≥ 4 for n ≥ 2
  have h4 : 4 ≤ 2^n := by
    have : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hn
    norm_num at this; exact this
  omega

end CapAddObstruction

/-! ─────────────────────────────────────────────────────────────────────────
    §5  firstOcc as the Canonical Section of tauJ_Fin

    The image of tauJ_Fin (local coords 0..capGap n k − 1 inside chapter k+j)
    decomposes chapter k+j into:
    - "old" coordinates [0, capGap n k):  reachable from chapter k via τ_j;
      these are exactly the coords r with minCap n r ≤ k.
    - "new" coordinates [capGap n k, capGap n (k+j)):  NOT reachable from chapter k;
      these are exactly the coords r with minCap n r > k (born in a chapter > k).
    ───────────────────────────────────────────────────────────────────────── -/

section CanonicalSection

/-- **Image characterization**: a coordinate r of chapter k+j is in the image of
    tauJ_Fin iff r < capGap n k.  The image is exactly the "old" block. -/
theorem tauJ_Fin_image_iff (n k j : ℕ) (hn : 2 ≤ n) (r : Fin (capGap n (k + j))) :
    (∃ s : Fin (capGap n k), (tauJ_Fin n k j hn s).val = r.val) ↔ r.val < capGap n k := by
  constructor
  · rintro ⟨s, hs⟩
    simp [tauJ_Fin] at hs
    rw [← hs]; exact s.isLt
  · intro h
    exact ⟨⟨r.val, h⟩, rfl⟩

/-- **New coordinates have large minCap**: the "new" elements of chapter k+j
    (those with local coord ≥ capGap n k) were born in a chapter strictly above k. -/
theorem new_coords_have_large_minCap (n k j : ℕ) (hn : 2 ≤ n) (_hj : 0 < j)
    (r : ℕ) (hr_lower : capGap n k ≤ r) (_hr_upper : r < capGap n (k + j)) :
    k < minCap n r hn := by
  have hr_ne : r ≠ 0 := by
    have := capGap_pos n k (by omega : n ≠ 0); omega
  by_contra h
  push_neg at h  -- h : minCap n r hn ≤ k
  have hspec := minCap_spec n r hn hr_ne
  have hcg : capGap n k = gap n k := capGap_eq_gap n k
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · -- minCap = k: r < gap n k = capGap n k ≤ r — contradiction
    rw [heq] at hspec; omega
  · -- minCap < k: gap n (minCap) < gap n k ≤ r — contradiction
    have hmono := gap_lt_of_lt n (minCap n r hn) k hn hlt
    omega

/-- **Full characterization of tauJ_Fin image via minCap**:
    r is in the image of tauJ_Fin iff minCap n r ≤ k.
    The old coordinates are precisely those whose "birth chapter" is at most k. -/
theorem tauJ_Fin_image_old_coords (n k j : ℕ) (hn : 2 ≤ n) (_ : 0 < j)
    (r : Fin (capGap n (k + j))) :
    (∃ s : Fin (capGap n k), (tauJ_Fin n k j hn s).val = r.val) ↔
    minCap n r.val hn ≤ k := by
  rw [tauJ_Fin_image_iff]
  -- Avoid rw [capGap_eq_gap] in goals with r : Fin (capGap n (k+j)) to prevent motive errors;
  -- instead introduce the equality as a hypothesis and use omega.
  have hcg : capGap n k = gap n k := capGap_eq_gap n k
  constructor
  · intro h
    -- h : r.val < capGap n k
    by_cases hr : r.val = 0
    · simp [hr, minCap_zero]  -- minCap n 0 = 0 ≤ k
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- k = 0: capGap n 0 = 1 and r.val ≠ 0 contradicts r.val < capGap n 0 = 1
        have : capGap n 0 = 1 := by
          rw [hcg]; simp [gap, Nat.zero_pow (by omega : 0 < n)]
        omega
      · exact minCap_minimal n r.val k hn hr hkpos (by omega)
  · intro h
    -- h : minCap n r.val hn ≤ k; show r.val < capGap n k
    by_cases hr : r.val = 0
    · simp [hr]; exact capGap_pos n k (by omega)
    · have hspec := minCap_spec n r.val hn hr
      have hmono : gap n (minCap n r.val hn) ≤ gap n k := by
        rcases Nat.eq_or_lt_of_le h with heq | hlt
        · rw [heq]
        · exact Nat.le_of_lt (gap_lt_of_lt n (minCap n r.val hn) k hn hlt)
      omega  -- r.val < gap n (minCap) ≤ gap n k = capGap n k

end CanonicalSection

end CampiOperazionistici
