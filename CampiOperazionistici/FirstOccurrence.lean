/-
  FirstOccurrence.lean — Campi Operazionistici
  First Occurrence and Structural Power Bound

  Paper: §15 (First Occurrence and the Power Bound)

  cf. the section on First Occurrence and the Power Bound in the main paper (`main.pdf`)

  Notation:
    κ_n(r) := min { k ≥ 1 : r < gap(n,k) }    implemented as `minCap n r hn`
    f_n(r) := κ_n(r)^n + r                      implemented as `firstOcc n r hn`

  Theorem FO: f_n(r) is the smallest m with radRem n m = r.
  Power Bound: every preimage of r is ≥ f_n(r).
  Threshold: for r ≥ 2^n − 1, the bound is strictly greater than the trivial r+1.

  Dependencies:
  - CampiOperazionistici.CampiOperazionistici (irootN, radRem, gap, radRem_base_add, …)
  - CampiOperazionistici.TranslationReencounter (gap_lt_of_lt, gap_strictMono)

  Author: Alessandro Sgarbi
  Date: April 2026
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.TranslationReencounter
import CampiOperazionistici.CapitolarTranslations

namespace CampiOperazionistici

/-! ─────────────────────────────────────────────────────────────────────────
    §1 — Auxiliary lemmas: qualitative estimate of the gap
    ───────────────────────────────────────────────────────────────────────── -/

/-- The gap at chapter 0 is 1 for n ≥ 1: gap n 0 = 1^n − 0^n = 1 − 0 = 1. -/
private lemma gap_zero_eq_one (n : ℕ) (hn : n ≠ 0) : gap n 0 = 1 := by
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  simp [gap, Nat.zero_pow hn', one_pow]

/-- The gap grows with the chapter: gap n k ≥ k + 1 for n ≥ 2.
    Proof by induction using `gap_lt_of_lt`. -/
lemma gap_ge_succ (n k : ℕ) (hn : 2 ≤ n) : k + 1 ≤ gap n k := by
  induction k with
  | zero =>
    simp [gap_zero_eq_one n (by omega)]
  | succ k ih =>
    have hlt := gap_lt_of_lt n k (k + 1) hn (Nat.lt_succ_self k)
    omega

/-- For every r there exists k ≥ 1 with r < gap n k: take k = r+1 (gap ≥ r+2 > r). -/
private lemma minCap_exists (n r : ℕ) (hn : 2 ≤ n) : ∃ k : ℕ, 1 ≤ k ∧ r < gap n k :=
  ⟨r + 1, by omega, by have := gap_ge_succ n (r + 1) hn; omega⟩

/-! ─────────────────────────────────────────────────────────────────────────
    §2 — Main definitions
    ───────────────────────────────────────────────────────────────────────── -/

/-- `minCap n r hn` is the smallest chapter κ_n(r) that hosts r as a local coordinate,
    i.e. the smallest k ≥ 1 with r < gap n k. Convention: κ_n(0) = 0. -/
def minCap (n r : ℕ) (hn : 2 ≤ n) : ℕ :=
  if r = 0 then 0
  else Nat.find (minCap_exists n r hn)

/-- `firstOcc n r hn` is the first occurrence of r in Aod_n: the smallest m with radRem n m = r.
    Closed form: f_n(r) = κ_n(r)^n + r. -/
def firstOcc (n r : ℕ) (hn : 2 ≤ n) : ℕ := (minCap n r hn) ^ n + r

/-! ### Computational checks (table §3 of the paper) -/

-- gap n 1 = 2^n − 1: for n=2 it is 3, for n=3 it is 7
#eval gap 2 1   -- 3
#eval gap 3 1   -- 7
-- minCap 2 r:
#eval minCap 2 1 (by omega)    -- 1  (gap 2 1 = 3 > 1)
#eval minCap 2 3 (by omega)    -- 2  (gap 2 1=3, 3<3 false; gap 2 2=5>3)
#eval minCap 2 5 (by omega)    -- 3  (gap 2 2=5, 5<5 false; gap 2 3=7>5)
-- firstOcc: table from §3 of the paper
#eval firstOcc 2 1 (by omega)  -- 2   = 1^2 + 1  ✓
#eval firstOcc 2 3 (by omega)  -- 7   = 2^2 + 3  ✓
#eval firstOcc 2 5 (by omega)  -- 14  = 3^2 + 5  ✓
#eval firstOcc 3 1 (by omega)  -- 2   = 1^3 + 1  ✓
#eval firstOcc 3 7 (by omega)  -- 15  = 2^3 + 7  ✓
#eval firstOcc 3 19 (by omega) -- 46  = 3^3 + 19 ✓

/-! ─────────────────────────────────────────────────────────────────────────
    §3 — Basic properties of minCap
    ───────────────────────────────────────────────────────────────────────── -/

@[simp] lemma minCap_zero (n : ℕ) (hn : 2 ≤ n) : minCap n 0 hn = 0 := by
  simp [minCap]

/-- For r ≠ 0: r < gap n (minCap n r). Follows from `Nat.find_spec`. -/
lemma minCap_spec (n r : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0) :
    r < gap n (minCap n r hn) := by
  simp only [minCap, hr, ite_false]
  exact (Nat.find_spec (minCap_exists n r hn)).2

/-- For r ≠ 0: minCap n r ≥ 1. Follows from `Nat.find_spec`. -/
lemma minCap_pos (n r : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0) : 1 ≤ minCap n r hn := by
  simp only [minCap, hr, ite_false]
  exact (Nat.find_spec (minCap_exists n r hn)).1

/-- minCap is the minimum: if k ≥ 1 and r < gap n k then minCap n r ≤ k.
    Follows from `Nat.find_min'`. -/
lemma minCap_minimal (n r k : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0)
    (hk : 1 ≤ k) (hlt : r < gap n k) : minCap n r hn ≤ k := by
  simp only [minCap, hr, ite_false]
  exact Nat.find_min' (minCap_exists n r hn) ⟨hk, hlt⟩

/-! ─────────────────────────────────────────────────────────────────────────
    §4 — Theorem FO (First Occurrence)
    ───────────────────────────────────────────────────────────────────────── -/

/-- **Theorem FO — Part 1**: `radRem n (firstOcc n r) = r`.
    The first occurrence does indeed have the correct radical remainder. -/
theorem firstOcc_radRem (n r : ℕ) (hn : 2 ≤ n) :
    radRem n (firstOcc n r hn) = r := by
  simp only [firstOcc]
  by_cases hr : r = 0
  · -- r = 0: firstOcc = 0^n + 0 = 0; radRem n 0 = 0
    subst hr
    simp only [minCap_zero, Nat.zero_pow (show 0 < n by omega), Nat.zero_add]
    -- Goal: radRem n 0 = 0
    have hle := irootN_pow_le n 0 (by omega)  -- (irootN n 0)^n ≤ 0
    simp only [radRem]; omega
  · -- r ≠ 0: use radRem_base_add with r < gap n (minCap n r)
    exact radRem_base_add n (minCap n r hn) r (by omega) (minCap_spec n r hn hr)

/-- **Theorem FO — Part 2**: `firstOcc n r` is the smallest m with `radRem n m = r`. -/
theorem firstOcc_is_minimum (n r m : ℕ) (hn : 2 ≤ n)
    (hm : radRem n m = r) : firstOcc n r hn ≤ m := by
  simp only [firstOcc]
  by_cases hr : r = 0
  · -- r = 0: firstOcc = 0^n + 0 = 0 ≤ m
    subst hr
    simp only [minCap_zero, Nat.zero_pow (show 0 < n by omega), Nat.zero_add]
    exact Nat.zero_le m
  · have hnn : n ≠ 0 := by omega
    -- Decomposition: m = (irootN n m)^n + r
    have hle_iroot := irootN_pow_le n m hnn
    have hdecomp : m = (irootN n m) ^ n + r := by
      simp only [radRem] at hm; omega
    -- r < gap n (irootN n m)
    have hgap : r < gap n (irootN n m) := by
      rw [← hm]
      exact radRem_lt_gap n m hnn
    -- irootN n m ≥ 1 (if it were 0, then m = 0 and radRem n 0 = 0 ≠ r)
    have hpos : 1 ≤ irootN n m := by
      by_contra h
      push_neg at h
      have hiz : irootN n m = 0 := by omega
      have hm0 := (irootN_eq_zero_iff n m hnn).mp hiz
      subst hm0
      have hle0 := irootN_pow_le n 0 hnn  -- (irootN n 0)^n ≤ 0
      simp only [radRem] at hm
      omega  -- hm : 0 - x = r with x ≤ 0, so r = 0, contradicting hr
    -- By minimality of minCap: minCap n r ≤ irootN n m
    have hcap_le := minCap_minimal n r (irootN n m) hn hr hpos hgap
    -- (minCap n r)^n + r ≤ (irootN n m)^n + r = m
    calc (minCap n r hn) ^ n + r
        ≤ (irootN n m) ^ n + r :=
          Nat.add_le_add_right (Nat.pow_le_pow_left hcap_le n) r
      _ = m := hdecomp.symm

/-! ─────────────────────────────────────────────────────────────────────────
    §5 — Power Bound
    ───────────────────────────────────────────────────────────────────────── -/

/-- **Power Bound Theorem**: every a with `radRem n a = r` satisfies `a ≥ firstOcc n r`.

    Unlike ℤ/mℤ (where `a mod m = r` implies only `a ≥ r`), here the lower bound
    `firstOcc n r = κ_n(r)^n + r` carries the extra structural information `κ_n(r)^n`,
    which grows with r. The `radRem` projection is not "opaque" like `mod`. -/
theorem radRem_preimage_lower_bound (n a : ℕ) (hn : 2 ≤ n) :
    firstOcc n (radRem n a) hn ≤ a :=
  firstOcc_is_minimum n (radRem n a) a hn rfl

/-! ─────────────────────────────────────────────────────────────────────────
    §6 — Non-triviality threshold of the Power Bound
    ───────────────────────────────────────────────────────────────────────── -/

/-- **Threshold Theorem**: for r ≥ gap n 1 = 2^n − 1, the power bound strictly exceeds
    the trivial lower bound r + 1.

    Interpretation: the threshold `gap n 1 = 2^n − 1` is exactly the boundary between the
    representatives of chapter 1 (those with `κ_n(r) = 1`, almost-trivial lower bound)
    and all the subsequent ones (with `κ_n(r) ≥ 2`, lower bound `κ_n(r)^n + r ≥ 4 + r`). -/
theorem lower_bound_nontrivial (n r : ℕ) (hn : 2 ≤ n)
    (hr : gap n 1 ≤ r) : r + 1 < firstOcc n r hn := by
  -- r ≥ gap n 1 ≥ 2 (from gap_ge_succ with k=1), so r ≠ 0
  have hgap1_ge2 : 2 ≤ gap n 1 := gap_ge_succ n 1 hn
  have hr_pos : r ≠ 0 := by omega
  -- minCap n r ≥ 2: it cannot be 1 (contradicts minCap_spec) nor 0 (contradicts minCap_pos)
  have hcap_ge_2 : 2 ≤ minCap n r hn := by
    have hspec := minCap_spec n r hn hr_pos
    have hpos  := minCap_pos  n r hn hr_pos
    rcases Nat.lt_or_ge (minCap n r hn) 2 with hlt | hge
    · -- minCap = 1: then r < gap n 1 ≤ r, contradiction
      have hval : minCap n r hn = 1 := by omega
      rw [hval] at hspec; omega
    · exact hge
  -- (minCap n r)^n ≥ 2^n ≥ 4
  have h2n : 2 ^ n ≤ (minCap n r hn) ^ n :=
    Nat.pow_le_pow_left hcap_ge_2 n
  have h2n_ge_4 : 4 ≤ 2 ^ n :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n    := Nat.pow_le_pow_right (by omega) hn
  -- firstOcc n r = (minCap)^n + r ≥ 4 + r > r + 1
  simp only [firstOcc]; omega

/-! ─────────────────────────────────────────────────────────────────────────
    §5 — Chapter of the first occurrence
    ───────────────────────────────────────────────────────────────────────── -/

/-- **firstOcc_irootN**: The chapter of `firstOcc n r` is exactly `minCap n r`.
    Geometrically, the first occurrence of r lives in its "birth chapter" κ_n(r). -/
theorem firstOcc_irootN (n r : ℕ) (hn : 2 ≤ n) :
    irootN n (firstOcc n r hn) = minCap n r hn := by
  simp only [firstOcc]
  by_cases hr : r = 0
  · subst hr
    simp only [minCap_zero, Nat.zero_pow (show 0 < n by omega), Nat.add_zero]
    exact (irootN_eq_zero_iff n 0 (by omega)).mpr rfl
  · exact sum_in_chapter n (minCap n r hn) r (by omega) (minCap_spec n r hn hr)

/-! ─────────────────────────────────────────────────────────────────────────
    §6 — Monotonicity of minCap and firstOcc
    ───────────────────────────────────────────────────────────────────────── -/

/-- **minCap is monotone**: r ≤ s implies minCap n r ≤ minCap n s.
    A larger local coordinate requires a chapter at least as high. -/
lemma minCap_mono (n r s : ℕ) (hn : 2 ≤ n) (hrs : r ≤ s) :
    minCap n r hn ≤ minCap n s hn := by
  by_cases hr : r = 0
  · subst hr; simp [minCap_zero]
  · have hs : s ≠ 0 := by omega
    exact minCap_minimal n r (minCap n s hn) hn hr
          (minCap_pos n s hn hs)
          (Nat.lt_of_le_of_lt hrs (minCap_spec n s hn hs))

/-- **firstOcc is strictly monotone**: r < s implies firstOcc n r < firstOcc n s.
    The canonical section is order-preserving: later radicals occur later. -/
theorem firstOcc_strictMono (n r s : ℕ) (hn : 2 ≤ n) (hrs : r < s) :
    firstOcc n r hn < firstOcc n s hn := by
  simp only [firstOcc]
  have hmono := minCap_mono n r s hn (Nat.le_of_lt hrs)
  have h1 : (minCap n r hn) ^ n ≤ (minCap n s hn) ^ n :=
    Nat.pow_le_pow_left hmono n
  omega

/-! ─────────────────────────────────────────────────────────────────────────
    §7 — The border / contact point
    ───────────────────────────────────────────────────────────────────────── -/

/-- **minCap at the border**: `gap n k - 1` (the maximum local coordinate in chapter k)
    has minCap exactly k.  It is the "contact point" where chapter k's gap meets firstOcc. -/
lemma minCap_border (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    minCap n (gap n k - 1) hn = k := by
  set r := gap n k - 1 with hr_def
  have hgap_ge : k + 1 ≤ gap n k := gap_ge_succ n k hn
  have hr_ne : r ≠ 0 := by omega
  -- Upper bound: r < gap n k, so k is a valid witness for minCap
  have hle : minCap n r hn ≤ k :=
    minCap_minimal n r k hn hr_ne hk (by omega)
  -- Lower bound: by contradiction, if minCap < k then gap n (minCap) ≤ gap n (k-1) < gap n k,
  -- so r < gap n (k-1) < gap n k, hence r ≤ gap n (k-1) - 1 < gap n k - 1 = r. Contradiction.
  have hge : k ≤ minCap n r hn := by
    by_contra h
    push_neg at h
    have hspec := minCap_spec n r hn hr_ne
    have hkm1 : minCap n r hn ≤ k - 1 := by omega
    have hmono_gap : gap n (minCap n r hn) ≤ gap n (k - 1) := by
      rcases Nat.eq_or_lt_of_le hkm1 with heq | hlt
      · rw [heq]
      · exact Nat.le_of_lt (gap_lt_of_lt n (minCap n r hn) (k - 1) hn hlt)
    have hgap_k_k1 : gap n (k - 1) < gap n k := gap_lt_of_lt n (k - 1) k hn (by omega)
    omega
  omega

/-- **Corollary**: the first occurrence of `gap n k - 1` is the LAST element of chapter k. -/
theorem firstOcc_at_border (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    firstOcc n (gap n k - 1) hn = k ^ n + (gap n k - 1) := by
  simp only [firstOcc, minCap_border n k hn hk]

/-! ─────────────────────────────────────────────────────────────────────────
    §8 — Theorem MC: exact characterization of minCap
    ───────────────────────────────────────────────────────────────────────── -/

/-- **Theorem MC**: minCap n r = k (for k ≥ 1, r ≠ 0) iff r lies in [gap n (k-1), gap n k).
    This "chapter-sandwich" pinpoints exactly which chapter r belongs to. -/
theorem minCap_exact_iff (n r k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hr : r ≠ 0) :
    minCap n r hn = k ↔ gap n (k - 1) ≤ r ∧ r < gap n k := by
  constructor
  · intro heq
    subst heq
    constructor
    · -- Show gap n (minCap - 1) ≤ r
      by_contra hlo
      push_neg at hlo
      -- hlo : r < gap n (minCap n r hn - 1)
      rcases Nat.lt_or_ge (minCap n r hn) 2 with hm1 | hm2
      · -- minCap = 1 (it is ≥ 1 by minCap_pos and < 2)
        have hmeq : minCap n r hn = 1 := by have := minCap_pos n r hn hr; omega
        rw [hmeq, Nat.sub_self] at hlo
        rw [gap_zero_eq_one n (by omega)] at hlo
        omega  -- r < 1 and r ≠ 0: contradiction
      · -- minCap ≥ 2, so minCap - 1 ≥ 1 is a strictly smaller valid witness
        exact absurd (minCap_minimal n r (minCap n r hn - 1) hn hr (by omega) hlo) (by omega)
    · exact minCap_spec n r hn hr
  · intro ⟨hlo, hhi⟩
    apply Nat.le_antisymm
    · exact minCap_minimal n r k hn hr hk hhi
    · by_contra h
      push_neg at h
      -- h : minCap n r hn < k, i.e., minCap ≤ k - 1
      have hkm_le : minCap n r hn ≤ k - 1 := by omega
      rcases Nat.eq_zero_or_pos (minCap n r hn) with hm0 | hmpos
      · exact absurd (minCap_pos n r hn hr) (by omega)
      · have hspec := minCap_spec n r hn hr
        have hmono : gap n (minCap n r hn) ≤ gap n (k - 1) := by
          rcases Nat.eq_or_lt_of_le hkm_le with heq | hlt
          · rw [heq]
          · exact Nat.le_of_lt (gap_lt_of_lt n (minCap n r hn) (k - 1) hn hlt)
        omega  -- r < gap n (minCap) ≤ gap n (k-1) ≤ r: contradiction

/-! ─────────────────────────────────────────────────────────────────────────
    §9 — firstOcc as canonical section via τ_j
    ───────────────────────────────────────────────────────────────────────── -/

/-- **τ_j sends firstOcc to any higher-chapter occurrence**.
    For h ≥ minCap n r, applying τ_{h − κ_n(r)} to firstOcc n r gives h^n + r.

    Geometric interpretation: firstOcc n r is the **canonical section** of the radRem
    projection at the "ground level" chapter κ_n(r).  Every other occurrence h^n + r
    (h ≥ κ_n(r)) is reached from the ground section by a single τ_j. -/
theorem tauJ_sends_firstOcc (n r h : ℕ) (hn : 2 ≤ n)
    (hh : minCap n r hn ≤ h) :
    tauJ n (h - minCap n r hn) (firstOcc n r hn) = h ^ n + r := by
  simp only [firstOcc]
  by_cases hr : r = 0
  · subst hr
    simp only [minCap_zero]
    -- Goal: tauJ n (h - 0) (0^n + 0) = h^n + 0
    exact tauJ_connects_same_radRem n 0 h 0 hn (Nat.zero_le h)
          (gap_pos' n 0 (by omega))
  · exact tauJ_connects_same_radRem n (minCap n r hn) h r hn hh
          (minCap_spec n r hn hr)

/-! ─────────────────────────────────────────────────────────────────────────
    §10 — Interaction between minCap and subtractionShift
    ─────────────────────────────────────────────────────────────────────────

    NOTE ON `twistedDomain_iff_minCap` (cf. §6 Step 3 of the main paper):
    The document claimed:
      `subtractionShift n (k+j) (h+j) ≤ t ↔ minCap n t hn ≤ k + j`
    under hypotheses n ≥ 2, 0 < k < h, j ≥ 1, t < gap n k.

    This biconditional is FALSE.  Concrete counterexample:
      n=2, k=1, h=2, j=1, t=1.
    All hypotheses hold (t=1 < gap 2 1 = 3). But:
      LHS: subtractionShift 2 2 3 = gap 2 2 - gap 2 1 = 5 - 3 = 2 ≤ 1? FALSE.
      RHS: minCap 2 1 hn = 1 ≤ 1 + 1 = 2? TRUE.
    LHS is false, RHS is true ⟹ the iff fails.

    Root cause: under ht: t < gap n k, we have t < gap n (k+j) for all j ≥ 0
    (by gap monotonicity), so minCap n t hn ≤ k+j is AUTOMATICALLY TRUE and
    carries no information about the domain condition σ ≤ t.

    What IS true in both directions is stated below.
    -/

-- Computational verification of the counterexample:
#eval subtractionShift 2 2 3  -- 2  (the domain condition requires 2 ≤ t)
#eval minCap 2 1 (by omega)   -- 1  (minCap ≤ 2 is true, but σ ≤ 1 is false)

/-- **Trivial direction** (not an iff):
    Under ht: t < gap n k and 0 < k, the condition `minCap n t hn ≤ k + j`
    holds automatically for all j — it does NOT require the twisted-fiber
    domain condition `subtractionShift n (k+j) (h+j) ≤ t`.

    This means the RHS of the claimed biconditional from
    the naive twisted-fiber characterisation is vacuously true and cannot characterise
    the domain. -/
lemma minCap_le_of_lt_gap_shift (n k j t : ℕ) (hn : 2 ≤ n)
    (hk : 0 < k) (hr : t ≠ 0) (ht : t < gap n k) :
    minCap n t hn ≤ k + j :=
  (minCap_minimal n t k hn hr hk ht).trans (Nat.le_add_right k j)

/-- **Correct sufficient condition** (converse direction of the false iff):
    If t's first-occurrence chapter κ_n(t) is at or above h+j, then t ≥ gap n (h+j-1),
    which implies the twisted-fiber domain condition σ(n, k+j, h+j) ≤ t.

    Geometric reading: a coordinate t born at or after chapter h+j is large enough
    to fit the full subtractive shift from chapter k+j to chapter h+j. -/
lemma minCap_ge_implies_subtractionShift_le (n k h j t : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (hk : 0 < k) (ht : t ≠ 0)
    (hmcap : h + j ≤ minCap n t hn) :
    subtractionShift n (k + j) (h + j) ≤ t := by
  -- minCap n t hn ≥ h+j means: t is NOT < gap n (h+j-1), i.e., t ≥ gap n (h+j-1).
  -- (Proof: if t < gap n (h+j-1) and h+j-1 ≥ 1, then minCap ≤ h+j-1 < h+j, contradiction.)
  have hhj_pos : 0 < h + j := by omega
  have t_ge : gap n (h + j - 1) ≤ t := by
    by_contra hlt
    push_neg at hlt
    have hmin := minCap_minimal n t (h + j - 1) hn ht (by omega) hlt
    omega
  -- subtractionShift n (k+j) (h+j) = gap n (h+j-1) - gap n (k+j-1) ≤ gap n (h+j-1) ≤ t
  simp only [subtractionShift]
  omega

end CampiOperazionistici
