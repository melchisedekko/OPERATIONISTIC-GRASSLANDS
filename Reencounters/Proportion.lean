/-
  Reencounters/Proportion.lean — the proportion of square chapter pairs that meet again.

  These results accompany the note Translations in the Quotient by the n-th Power Remainder.
-/
import Reencounters.SquareCase
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Positivity

/-!
# The proportion of square chapter pairs that meet again

For n = 2, count the chapter pairs `k < h` whose distance `h² − k²` is at most `X`.
The proportion of those that meet again in a later chapter (the predicate of
`forward_reencounter_sq_iff`) tends to 1 as `X → ∞`.

By `forward_reencounter_sq_iff`, the pairs that do not meet again are those with
`h − k ≤ 2`. There are `O(X)` of them, against `≍ X log X` pairs in all.
-/

namespace Reencounters

open CampiOperazionistici Filter Topology

/-- Chapter pairs `k < h` of squares at distance `h² − k² ≤ X` (the range bound is automatic, see
`mem_sqPairs_iff`). -/
def sqPairs (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (X + 1)) ×ˢ (Finset.range (X + 1))).filter
    (fun p => p.1 < p.2 ∧ p.2 ^ 2 - p.1 ^ 2 ≤ X)

open Classical in
/-- The pairs of `sqPairs X` that meet again in a later chapter. -/
noncomputable def sqPairsMeeting (X : ℕ) : Finset (ℕ × ℕ) :=
  (sqPairs X).filter
    (fun p => ∃ k' h' : ℕ, p.1 < k' ∧ k' ^ 2 + (p.2 ^ 2 - p.1 ^ 2) = h' ^ 2)

/-- Adjacent square gap: `h² − (h−1)² = 2h − 1`. -/
lemma sq_pred_diff (h : ℕ) (hpos : 1 ≤ h) : h ^ 2 - (h - 1) ^ 2 = 2 * h - 1 := by
  rw [sq_diff_eq_mul (h - 1) h (Nat.sub_le _ _)]
  have h1 : h - (h - 1) = 1 := by omega
  have h2 : h + (h - 1) = 2 * h - 1 := by omega
  rw [h1, h2, one_mul]

/-- From `k < h` and `h² − k² ≤ X` one gets `h ≤ X` (so both indices fit in `range (X+1)`). -/
lemma le_of_sqPairs_cond {X k h : ℕ} (hkh : k < h) (hΔ : h ^ 2 - k ^ 2 ≤ X) : h ≤ X := by
  have hpos : 1 ≤ h := by omega
  have hge : 2 * h - 1 ≤ h ^ 2 - k ^ 2 := by
    have hk_le : k ≤ h - 1 := by omega
    have hk2 : k ^ 2 ≤ (h - 1) ^ 2 := Nat.pow_le_pow_left hk_le 2
    calc
      h ^ 2 - k ^ 2 ≥ h ^ 2 - (h - 1) ^ 2 := Nat.sub_le_sub_left hk2 _
      _ = 2 * h - 1 := sq_pred_diff h hpos
  omega

/-- `sqPairs X` is exactly the set of pairs `k < h` with `h² − k² ≤ X`. -/
theorem mem_sqPairs_iff (X k h : ℕ) : (k, h) ∈ sqPairs X ↔ k < h ∧ h ^ 2 - k ^ 2 ≤ X := by
  simp only [sqPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun ⟨_, hp⟩ => hp
  · intro ⟨hkh, hΔ⟩
    have hhX : h ≤ X := le_of_sqPairs_cond hkh hΔ
    exact ⟨⟨by omega, by omega⟩, ⟨hkh, hΔ⟩⟩

/-- Membership in `sqPairsMeeting` is membership in `sqPairs` plus `h − k ≥ 3`. -/
lemma mem_sqPairsMeeting_iff (X k h : ℕ) :
    (k, h) ∈ sqPairsMeeting X ↔ (k, h) ∈ sqPairs X ∧ 3 ≤ h - k := by
  simp only [sqPairsMeeting, Finset.mem_filter]
  constructor
  · intro ⟨hm, hex⟩
    refine ⟨hm, ?_⟩
    have hkh : k < h := (mem_sqPairs_iff X k h).1 hm |>.1
    exact (forward_reencounter_sq_iff k h hkh).1 hex
  · intro ⟨hm, h3⟩
    refine ⟨hm, ?_⟩
    have hkh : k < h := (mem_sqPairs_iff X k h).1 hm |>.1
    exact (forward_reencounter_sq_iff k h hkh).2 h3

/-- Non-meeting pairs of `sqPairs X` (those with `h − k ≤ 2`). -/
noncomputable def sqPairsBad (X : ℕ) : Finset (ℕ × ℕ) :=
  (sqPairs X).filter (fun p => ¬(3 ≤ p.2 - p.1))

/-- `sqPairsMeeting` coincides with the filter `3 ≤ h − k`. -/
lemma sqPairsMeeting_eq_filter (X : ℕ) :
    sqPairsMeeting X = (sqPairs X).filter (fun p => 3 ≤ p.2 - p.1) := by
  ext p
  constructor
  · intro hp
    have := (mem_sqPairsMeeting_iff X p.1 p.2).1 hp
    exact Finset.mem_filter.mpr ⟨this.1, this.2⟩
  · intro hp
    obtain ⟨hm, h3⟩ := Finset.mem_filter.mp hp
    exact (mem_sqPairsMeeting_iff X p.1 p.2).2 ⟨hm, h3⟩

/-- Card additivity: meeting + bad = all. -/
lemma sqPairs_card_add (X : ℕ) :
    (sqPairsMeeting X).card + (sqPairsBad X).card = (sqPairs X).card := by
  rw [sqPairsMeeting_eq_filter, sqPairsBad]
  exact Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ => 3 ≤ p.2 - p.1)

/-- Bad pairs are exactly the members of `sqPairs` with `h − k ≤ 2`. -/
lemma mem_sqPairsBad_iff (X k h : ℕ) :
    (k, h) ∈ sqPairsBad X ↔ (k, h) ∈ sqPairs X ∧ h - k ≤ 2 := by
  simp only [sqPairsBad, Finset.mem_filter]
  constructor
  · intro ⟨hm, hbad⟩
    refine ⟨hm, ?_⟩
    have hkh : k < h := (mem_sqPairs_iff X k h).1 hm |>.1
    omega
  · intro ⟨hm, hle⟩
    exact ⟨hm, by omega⟩

/-- Candidate pairs at difference 1 with first coordinate `< X+1`. -/
def sqDiffOneCandidates (X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (X + 1)).image (fun k => (k, k + 1))

/-- Candidate pairs at difference 2 with first coordinate `< X+1`. -/
def sqDiffTwoCandidates (X : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (X + 1)).image (fun k => (k, k + 2))

/-- Bad pairs sit among the difference-1 and difference-2 candidates. -/
lemma sqPairsBad_subset_candidates (X : ℕ) :
    sqPairsBad X ⊆ sqDiffOneCandidates X ∪ sqDiffTwoCandidates X := by
  intro p hp
  have hm : p ∈ sqPairs X := (mem_sqPairsBad_iff X p.1 p.2).1 hp |>.1
  have hle : p.2 - p.1 ≤ 2 := (mem_sqPairsBad_iff X p.1 p.2).1 hp |>.2
  have hkh : p.1 < p.2 := (mem_sqPairs_iff X p.1 p.2).1 hm |>.1
  have hk : p.1 ∈ Finset.range (X + 1) := by
    simp only [sqPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
    exact Finset.mem_range.mpr hm.1.1
  have hd : p.2 - p.1 = 1 ∨ p.2 - p.1 = 2 := by omega
  rcases hd with h1 | h2
  · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p.1, hk, ?_⟩)
    ext <;> omega
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.1, hk, ?_⟩)
    ext <;> omega

/-- There are at most `2(X+1)` non-meeting pairs. -/
lemma sqPairsBad_card_le (X : ℕ) : (sqPairsBad X).card ≤ 2 * (X + 1) := by
  have hcard := Finset.card_le_card (sqPairsBad_subset_candidates X)
  have h1 : (sqDiffOneCandidates X).card ≤ X + 1 :=
    (Finset.card_image_le : (sqDiffOneCandidates X).card ≤ (Finset.range (X + 1)).card).trans
      (by simp)
  have h2 : (sqDiffTwoCandidates X).card ≤ X + 1 :=
    (Finset.card_image_le : (sqDiffTwoCandidates X).card ≤ (Finset.range (X + 1)).card).trans
      (by simp)
  have : (sqDiffOneCandidates X ∪ sqDiffTwoCandidates X).card ≤
      (sqDiffOneCandidates X).card + (sqDiffTwoCandidates X).card :=
    Finset.card_union_le _ _
  omega

/-- Distance-`d` square difference expands as `2kd + d²`. -/
lemma sq_diff_of_add (k d : ℕ) : (k + d) ^ 2 - k ^ 2 = 2 * k * d + d ^ 2 := by
  rw [sq_diff_eq_mul k (k + d) (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  ring

/-- Pairs `(k, k+d)` with `2kd + d² ≤ X` lie in `sqPairs X`. -/
lemma mem_sqPairs_of_mul_bound (X k d : ℕ) (_hd : 1 ≤ d) (hbound : 2 * k * d + d ^ 2 ≤ X) :
    (k, k + d) ∈ sqPairs X := by
  rw [mem_sqPairs_iff]
  refine ⟨by omega, ?_⟩
  rwa [sq_diff_of_add]

/-- The finite set of pairs at fixed distance `d` with `2kd + d² ≤ X`. -/
def sqPairsSlice (X d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range ((X - d ^ 2) / (2 * d) + 1)).image (fun k => (k, k + d))

/-- For `d² ≤ X`, the slice at distance `d` sits in `sqPairs X`. -/
lemma sqPairsSlice_subset (X d : ℕ) (hd : 1 ≤ d) (hdX : d ^ 2 ≤ X) :
    sqPairsSlice X d ⊆ sqPairs X := by
  intro p hp
  simp only [sqPairsSlice, Finset.mem_image] at hp
  obtain ⟨k, hk, rfl⟩ := hp
  have hk' : k ≤ (X - d ^ 2) / (2 * d) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmul : k * (2 * d) ≤ X - d ^ 2 := Nat.mul_le_of_le_div _ _ _ hk'
  have : 2 * k * d + d ^ 2 ≤ X := by
    have : 2 * k * d = k * (2 * d) := by ring
    omega
  exact mem_sqPairs_of_mul_bound X k d hd this

/-- Card of the distance-`d` slice. -/
lemma sqPairsSlice_card (X d : ℕ) :
    (sqPairsSlice X d).card = (X - d ^ 2) / (2 * d) + 1 := by
  simp only [sqPairsSlice]
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (Prod.ext_iff.mp h).1

/-- `↑(m/n) + 1` dominates the real quotient `m/n`. -/
lemma cast_div_add_one_ge (m n : ℕ) (hn : 0 < n) : (m : ℝ) / n ≤ ↑(m / n) + 1 := by
  have hle : m ≤ n * (m / n) + n :=
    calc
      m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
      _ ≤ n * (m / n) + n := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt m hn)) _
  have : (m : ℝ) ≤ (n : ℝ) * ↑(m / n) + n := by exact_mod_cast hle
  have hnpos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  calc
    (m : ℝ) / n ≤ ((n : ℝ) * ↑(m / n) + n) / n := by gcongr
    _ = ↑(m / n) + 1 := by field_simp [hnpos]

/-- Real lower bound for one distance slice when `d² ≤ X`. -/
lemma sqPairsSlice_cast_ge (X d : ℕ) (hd : 1 ≤ d) (hdX : d ^ 2 ≤ X) :
    (X : ℝ) / ((2 : ℝ) * d) - (d : ℝ) / 2 ≤ ((sqPairsSlice X d).card : ℝ) := by
  have hdpos : 0 < 2 * d := by omega
  set n : ℕ := (X - d ^ 2) / (2 * d)
  have hcard : ((sqPairsSlice X d).card : ℝ) = (n : ℝ) + 1 := by
    rw [sqPairsSlice_card]
    change ↑(n + 1) = (n : ℝ) + 1
    exact Nat.cast_add_one n
  rw [hcard]
  have hdiv : ((X - d ^ 2 : ℕ) : ℝ) / ↑(2 * d) ≤ (n : ℝ) + 1 := by
    simpa [n] using cast_div_add_one_ge (X - d ^ 2) (2 * d) hdpos
  have hXsub : ((X - d ^ 2 : ℕ) : ℝ) = (X : ℝ) - (d : ℝ) ^ 2 := by
    rw [Nat.cast_sub hdX, Nat.cast_pow]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd)
  have h2d : ((2 * d : ℕ) : ℝ) = (2 : ℝ) * d := by simp
  have hsplit : ((X : ℝ) - (d : ℝ) ^ 2) / ((2 : ℝ) * d) =
      (X : ℝ) / ((2 : ℝ) * d) - (d : ℝ) / 2 := by
    have : (d : ℝ) ^ 2 / ((2 : ℝ) * d) = (d : ℝ) / 2 := by field_simp [hd0]
    field_simp
  calc
    (X : ℝ) / ((2 : ℝ) * d) - (d : ℝ) / 2 =
        ((X : ℝ) - (d : ℝ) ^ 2) / ((2 : ℝ) * d) := hsplit.symm
    _ = ((X - d ^ 2 : ℕ) : ℝ) / ((2 : ℝ) * d) := by rw [← hXsub]
    _ = ((X - d ^ 2 : ℕ) : ℝ) / ↑(2 * d) := by rw [← h2d]
    _ ≤ (n : ℝ) + 1 := hdiv

/-- Distance slices for distinct `d` are pairwise disjoint. -/
lemma sqPairsSlice_pairwiseDisjoint (X : ℕ) (s : Set ℕ) :
    s.PairwiseDisjoint (sqPairsSlice X) := by
  intro d _hd e _he hde
  refine Finset.disjoint_iff_ne.mpr ?_
  intro p hp q hq hpq
  simp only [sqPairsSlice, Finset.mem_image] at hp hq
  obtain ⟨k, _, rfl⟩ := hp
  obtain ⟨k', _, rfl⟩ := hq
  exact hde (by
    have := Prod.ext_iff.mp hpq
    omega)

/-- Nat card lower bound by the first `D` slices (`D² ≤ X`). -/
lemma sqPairs_card_ge_sum (X D : ℕ) (hDX : D ^ 2 ≤ X) :
    ∑ d ∈ Finset.Icc 1 D, (sqPairsSlice X d).card ≤ (sqPairs X).card := by
  classical
  have hsub : ∀ d ∈ Finset.Icc 1 D, sqPairsSlice X d ⊆ sqPairs X := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
    exact sqPairsSlice_subset X d hd1 (le_trans (Nat.pow_le_pow_left hdD 2) hDX)
  have hdisj : ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint (sqPairsSlice X) :=
    sqPairsSlice_pairwiseDisjoint X _
  have hbun := Finset.card_biUnion hdisj
  have hle : ((Finset.Icc 1 D).biUnion (sqPairsSlice X)).card ≤ (sqPairs X).card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  rw [← hbun]
  exact hle

/-- Gauss sum as a real: `Σ_{d=1}^D d = D(D+1)/2`. -/
lemma sum_Icc_id_real (D : ℕ) : ∑ d ∈ Finset.Icc 1 D, (d : ℝ) = (D : ℝ) * (D + 1) / 2 := by
  induction' D with D ih
  · simp
  · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D.succ)]
    rw [ih]
    push_cast
    ring

/-- Two consecutive naturals give an even product. -/
lemma two_dvd_mul_succ (D : ℕ) : 2 ∣ D * (D + 1) := by
  rcases Nat.mod_two_eq_zero_or_one D with h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega : (D + 1) % 2 = 0)) _

/-- Real lower bound `#sqPairs X ≥ (X/2)·H_D − D(D+1)/4` when `1 ≤ D` and `D² ≤ X`. -/
lemma sqPairs_card_ge_harmonic (X D : ℕ) (_hD : 1 ≤ D) (hDX : D ^ 2 ≤ X) :
    (X : ℝ) / 2 * (harmonic D : ℝ) - (D : ℝ) * (D + 1) / 4 ≤ ((sqPairs X).card : ℝ) := by
  have hnat := sqPairs_card_ge_sum X D hDX
  have hcast : ∑ d ∈ Finset.Icc 1 D, ((sqPairsSlice X d).card : ℝ) ≤ ((sqPairs X).card : ℝ) := by
    exact_mod_cast hnat
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      (X : ℝ) / (2 * d) - (d : ℝ) / 2 ≤ ((sqPairsSlice X d).card : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
    exact sqPairsSlice_cast_ge X d hd1 (le_trans (Nat.pow_le_pow_left hdD 2) hDX)
  refine le_trans ?_ (le_trans (Finset.sum_le_sum hterm) hcast)
  have hleft :
      ∑ d ∈ Finset.Icc 1 D, ((X : ℝ) / (2 * d) - (d : ℝ) / 2) =
        (X : ℝ) / 2 * ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / d -
          (1 : ℝ) / 2 * ∑ d ∈ Finset.Icc 1 D, (d : ℝ) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · calc
        ∑ d ∈ Finset.Icc 1 D, (X : ℝ) / (2 * d) =
            ∑ d ∈ Finset.Icc 1 D, ((X : ℝ) / 2) * (1 / d) := by
          congr 1; ext d; field_simp
        _ = (X : ℝ) / 2 * ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / d := by rw [← Finset.mul_sum]
    · calc
        ∑ d ∈ Finset.Icc 1 D, (d : ℝ) / 2 =
            ∑ d ∈ Finset.Icc 1 D, ((1 : ℝ) / 2) * d := by congr 1; ext d; ring
        _ = (1 : ℝ) / 2 * ∑ d ∈ Finset.Icc 1 D, (d : ℝ) := by rw [← Finset.mul_sum]
  rw [hleft, sum_Icc_id_real]
  have hharm : ∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / d = (harmonic D : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hharm]
  ring_nf
  rfl

/-- For every `M`, eventually `#sqPairs X ≥ M · (X+1)`. -/
lemma sqPairs_card_ge_mul_eventually (M : ℕ) :
    ∀ᶠ X : ℕ in atTop, (M : ℝ) * (X + 1) ≤ (sqPairs X).card := by
  -- Pick D so that log(D+1) ≥ 2(M+1); then the harmonic lower bound beats M(X+1).
  have hlog : Tendsto (fun D : ℕ => Real.log ((D : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ (1 : ℝ)
      tendsto_natCast_atTop_atTop)
  obtain ⟨D0, hD0⟩ := (hlog.eventually_ge_atTop (2 * (M + 1 : ℝ))).exists
  let D : ℕ := max D0 1
  have hD1 : 1 ≤ D := Nat.le_max_right _ _
  have hlogD : 2 * (M + 1 : ℝ) ≤ Real.log ((D : ℝ) + 1) := by
    have hD0le : D0 ≤ D := Nat.le_max_left _ _
    have : Real.log ((D0 : ℝ) + 1) ≤ Real.log ((D : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hD0le)
    exact le_trans hD0 this
  -- X₀ large enough that D² ≤ X and D(D+1)/4 + M ≤ X
  let X0 : ℕ := max (D ^ 2) (4 * D * (D + 1) + M)
  filter_upwards [eventually_ge_atTop X0] with X hX0
  have hDX : D ^ 2 ≤ X := le_trans (Nat.le_max_left _ _) hX0
  have hbound := sqPairs_card_ge_harmonic X D hD1 hDX
  have hharm : Real.log ((D : ℝ) + 1) ≤ (harmonic D : ℝ) := by
    simpa using log_add_one_le_harmonic D
  have hXge : (D : ℝ) * (D + 1) / 4 + (M : ℝ) ≤ (X : ℝ) := by
    have hX0' : 4 * D * (D + 1) + M ≤ X := le_trans (Nat.le_max_right _ _) hX0
    have hquarter : (D : ℝ) * (D + 1) / 4 ≤ (4 : ℝ) * D * (D + 1) := by
      have hpos : (0 : ℝ) < 4 := by norm_num
      rw [div_le_iff₀ hpos]
      have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      nlinarith
    have : (D : ℝ) * (D + 1) / 4 + (M : ℝ) ≤ ((4 * D * (D + 1) + M : ℕ) : ℝ) := by
      have hcast : ((4 * D * (D + 1) + M : ℕ) : ℝ) = (4 : ℝ) * D * (D + 1) + M := by
        push_cast; rfl
      rw [hcast]
      linarith [hquarter]
    exact le_trans this ((Nat.cast_le (α := ℝ)).mpr hX0')
  have hcalc : (M : ℝ) * (X + 1) ≤
      (X : ℝ) / 2 * Real.log ((D : ℝ) + 1) - (D : ℝ) * (D + 1) / 4 := by
    have h1 : (X : ℝ) / 2 * (2 * (M + 1 : ℝ)) - (D : ℝ) * (D + 1) / 4 ≤
        (X : ℝ) / 2 * Real.log ((D : ℝ) + 1) - (D : ℝ) * (D + 1) / 4 := by gcongr
    have h2 : (M : ℝ) * (X + 1) ≤
        (X : ℝ) / 2 * (2 * (M + 1 : ℝ)) - (D : ℝ) * (D + 1) / 4 := by
      linarith [hXge]
    exact le_trans h2 h1
  calc
    (M : ℝ) * (X + 1)
        ≤ (X : ℝ) / 2 * Real.log ((D : ℝ) + 1) - (D : ℝ) * (D + 1) / 4 := hcalc
    _ ≤ (X : ℝ) / 2 * (harmonic D : ℝ) - (D : ℝ) * (D + 1) / 4 := by gcongr
    _ ≤ (sqPairs X).card := hbound

/-- `#sqPairs X / (X+1) → ∞`. -/
lemma sqPairs_card_div_tendsto_atTop :
    Tendsto (fun X : ℕ => ((sqPairs X).card : ℝ) / (X + 1)) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun C => ?_
  obtain ⟨N, hN⟩ := (eventually_atTop.mp
    (sqPairs_card_ge_mul_eventually (Nat.ceil (max C 0))))
  refine ⟨N, fun X hX => ?_⟩
  have hcard := hN X hX
  have hC : (C : ℝ) ≤ ↑(Nat.ceil (max C 0)) :=
    (le_max_left C 0).trans (Nat.le_ceil _)
  have hpos : (0 : ℝ) ≤ X + 1 := by positivity
  calc
    (C : ℝ) ≤ ↑(Nat.ceil (max C 0)) := hC
    _ = ↑(Nat.ceil (max C 0)) * (X + 1) / (X + 1) := by field_simp
    _ ≤ (sqPairs X).card / (X + 1) :=
      div_le_div_of_nonneg_right hcard hpos

/-- Bound `bad/all ≤ 2(X+1)/all` (both sides 0 when `all = 0`). -/
lemma sqPairsBad_div_le (X : ℕ) :
    ((sqPairsBad X).card : ℝ) / (sqPairs X).card ≤
      (2 : ℝ) * (X + 1) / (sqPairs X).card := by
  by_cases h0 : (sqPairs X).card = 0
  · simp [h0]
  · have hc : (0 : ℝ) < (sqPairs X).card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have hle : ((sqPairsBad X).card : ℝ) ≤ (2 : ℝ) * (X + 1) := by
      exact_mod_cast sqPairsBad_card_le X
    exact div_le_div_of_nonneg_right hle hc.le

/-- Identity `2(X+1)/card = 2 / (card/(X+1))`. -/
lemma two_mul_div_eq (X : ℕ) :
    (2 : ℝ) * (X + 1) / (sqPairs X).card =
      2 / (((sqPairs X).card : ℝ) / (X + 1)) := by
  by_cases h0 : (sqPairs X).card = 0
  · simp [h0]
  · field_simp

/-- The proportion of bad pairs tends to 0. -/
lemma sqPairsBad_proportion_tendsto_zero :
    Tendsto (fun X : ℕ => ((sqPairsBad X).card : ℝ) / (sqPairs X).card) atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun X : ℕ => (2 : ℝ) * (X + 1) / (sqPairs X).card) atTop (𝓝 0) := by
    have hcongr : (fun X : ℕ => (2 : ℝ) * (X + 1) / (sqPairs X).card) =ᶠ[atTop]
        fun X => 2 / (((sqPairs X).card : ℝ) / (X + 1)) :=
      Filter.Eventually.of_forall two_mul_div_eq
    refine Tendsto.congr' hcongr.symm ?_
    have hinv := sqPairs_card_div_tendsto_atTop.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  exact squeeze_zero
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    sqPairsBad_div_le hupper

/-- For squares, the proportion of chapter pairs at distance at most `X` that meet again in a later
chapter tends to 1. -/
theorem sq_meeting_proportion_tendsto_one :
    Tendsto (fun X : ℕ => ((sqPairsMeeting X).card : ℝ) / (sqPairs X).card) atTop (𝓝 1) := by
  have hpos : ∀ᶠ X : ℕ in atTop, 0 < (sqPairs X).card := by
    filter_upwards [sqPairs_card_ge_mul_eventually 1] with X hX
    have hlt : (0 : ℝ) < (1 : ℝ) * (X + 1) := by positivity
    have hX' : (1 : ℝ) * (X + 1) ≤ (sqPairs X).card := by
      convert hX using 1; norm_cast
    exact Nat.cast_pos.mp (lt_of_lt_of_le hlt hX')
  have heq : ((fun X : ℕ => ((sqPairsMeeting X).card : ℝ) / (sqPairs X).card) =ᶠ[atTop]
      fun X => 1 - ((sqPairsBad X).card : ℝ) / (sqPairs X).card) := by
    filter_upwards [hpos] with X hX
    have hne : ((sqPairs X).card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hX)
    have hadd := sqPairs_card_add X
    have hme : (sqPairsMeeting X).card = (sqPairs X).card - (sqPairsBad X).card := by omega
    have hmeR : ((sqPairsMeeting X).card : ℝ) =
        ((sqPairs X).card : ℝ) - (sqPairsBad X).card := by
      rw [hme]
      exact Nat.cast_sub (by omega : (sqPairsBad X).card ≤ (sqPairs X).card)
    rw [hmeR]
    field_simp [hne]
  have hsub : Tendsto
      (fun X : ℕ => (1 : ℝ) - ((sqPairsBad X).card : ℝ) / (sqPairs X).card)
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub sqPairsBad_proportion_tendsto_zero
    norm_num
  exact Tendsto.congr' (EventuallyEq.symm heq) hsub

end Reencounters
