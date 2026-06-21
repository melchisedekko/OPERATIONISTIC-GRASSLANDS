/-
  CapitolarGroupoid.lean
  ======================
  Groupoid of Capitolar Translations: Partial Inverses and the Curvature of the Grassland

  Paper: §16 (The Capitolar Groupoid and Transport of Structure)

  **Purpose**: Extend the additive monoid (τ_j)_{j ∈ ℕ} of capitolar translations to a full
  ℤ-indexed family by introducing the *subtractive* capitolar translations τ_{-j}. The result
  is not a group (τ_{-j} is a partial function) but a **groupoid**: the codiscrete groupoid on
  ℕ-chapters, with the explicit action given by the actual functions tauNeg.

  **Structure of the file**:

  §1  Definition of tauNeg and its canonical form (tauNeg_base_add).
      The hypothesis `j ≤ k` keeps everything in ℕ without ℤ-valued functions.

  §2  Algebraic laws: partial inverse, left partial inverse, subtractive composition,
      mixed compositions (additive-dominant and subtractive-dominant).

  §3  Equivalence preservation: tauNeg preserves aodEquiv within the subtractive window
      (j ≤ t), and fails at j = t+1. These are corollaries of the §6 results already
      proved in CapitolarTranslations.

  §4  The twisted radical remainder twistedRadRem n a = radRem n a + gap n (irootN n a - 1)
      and the twisted equivalence twistedAodEquiv. Within the same chapter twistedAodEquiv
      coincides with aodEquiv; across chapters it encodes the gauge-corrected identification
      whose correction potential is f(k) = gap(n, k-1).

  §5  tauNeg preserves twistedAodEquiv (within the same chapter).
      tauJ does NOT preserve twistedAodEquiv across different chapters (false for n ≥ 3;
      see §5 note).

  §6  Computational verification via #eval.

  §8  Mathlib `CategoryTheory.Groupoid` instance for ℕ-chapters.
      The codiscrete groupoid: objects = ℕ (chapters), Hom k h = { z : ℤ // z = h - k }
      (exactly one morphism per pair). Uses `Groupoid.ofHomUnique` after providing the
      `Category` structure via `Category.ofHomUnique`... actually built manually as the
      unique-hom category. The category and groupoid laws follow from singleton hom-sets.

  **Depends on**: CapitolarTranslations (which already imports TranslationReencounter and
  the foundation CampiOperazionistici).
  **Also imports**: Mathlib.CategoryTheory.Groupoid

  **Status**:
  - §1–§3: fully proved.
  - §4: definitions and basic properties proved.
  - §5: tauNeg invariance proved for same-chapter case.
         tauJ does NOT preserve twistedAodEquiv across chapters (false for n ≥ 3; see §5 note).
  - §6: computational checks.
  - §7: fiber overlap theorems fully proved (twistedRadRem_last_chapter,
         tRR_fiber_mem_iff, tRR_fiber_inter_count, tRR_fiber_adjacent, tRR_fiber_count).
  - §8: Mathlib Groupoid instance — fully proved, 0 sorry.
  - §9b: Mathlib Functor `chapterFiberFunctor` and `natPreordToCapitolar` — fully proved, 0 sorry.
  - §10: Chapter Tiling Theorem — fully proved, 0 sorry.
  - §10b: TwistedFiberTranslation — obstruction κ, drift lemma, T̃_j correctness,
           semigroup law, obstruction_zero_iff_n2 (n=2 flatness theorem).
  - §11: SigmaShiftFunctor — subtractionShift_cocycle, sigmaShiftMap, aodEquiv_compat,
          composition law, twistedRadRem trivialization, tauJ_invariant_iff biconditional,
          sigma_category_finer_than_capitolar (n ≥ 3 non-isomorphism, via obstruction_nonzero_of_n_ge3),
          subtractionShift_two (n=2 isomorphism),
          twistedAodEquiv_sigmaShift_iff (full biconditional),
          sigmaShift_firstOcc_iff (σ-shift lands on firstOcc ↔ minCap = h).
  - 0 sorry total: obstruction_nonzero_of_n_ge3 fully proved via three_pow_add_three_gt induction.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Category.Preorder
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.TranslationReencounter
import CampiOperazionistici.CapitolarTranslations
import CampiOperazionistici.FirstOccurrence
import CampiOperazionistici.aoddepth

namespace CampiOperazionistici

open CategoryTheory

/-!
## Minimal Span Category

A span from X to Y is a triple (Z, left : Z → X, right : Z → Y).
Composition is via pullback (fiber product).
-/

structure Span (X Y : Type) where
  carrier : Type
  left : carrier → X
  right : carrier → Y

namespace Span

/-- Identity span: X ← X → X with both legs being identity. -/
def id (X : Type) : Span X X :=
  { carrier := X, left := fun x => x, right := fun x => x }

/-- Composition of spans via pullback.
    Given X ← Z₁ → Y and Y ← Z₂ → W, the composite is X ← (Z₁ ×_Y Z₂) → W
    where Z₁ ×_Y Z₂ = {(z₁, z₂) | right z₁ = left z₂}. -/
def comp {X Y W : Type} (s₁ : Span X Y) (s₂ : Span Y W) : Span X W :=
  { carrier := { p : s₁.carrier × s₂.carrier // s₁.right p.1 = s₂.left p.2 },
    left := fun p => s₁.left p.val.1,
    right := fun p => s₂.right p.val.2 }

/-- Two spans are isomorphic if there's a bijection between their carriers
    that commutes with the legs. -/
structure Iso (s₁ s₂ : Span X Y) where
  hom : s₁.carrier → s₂.carrier
  inv : s₂.carrier → s₁.carrier
  hom_inv : ∀ z, inv (hom z) = z
  inv_hom : ∀ z, hom (inv z) = z
  left_comm : ∀ z, s₁.left z = s₂.left (hom z)
  right_comm : ∀ z, s₁.right z = s₂.right (hom z)

/-- Extensionality: to prove two spans equal, provide an isomorphism.
    We use this to state the functor laws up to isomorphism. -/
structure IsoEq {s₁ s₂ : Span X Y} (iso : Iso s₁ s₂) : Prop where
  -- Marker that the spans are isomorphic
  -- In practice, functor laws hold "up to iso" not definitional equality

end Span

/-!
## Auxiliary: gap monotonicity for ≤
-/

/-- gap is monotone (weak): k ≤ h → gap n k ≤ gap n h. -/
private lemma gap_le_of_le (n k h : ℕ) (hn : 2 ≤ n) (hkh : k ≤ h) : gap n k ≤ gap n h := by
  rcases Nat.eq_or_lt_of_le hkh with rfl | hlt
  · exact le_refl _
  · exact Nat.le_of_lt (gap_lt_of_lt n k h hn hlt)

/-!
## §1  Subtractive Capitolar Translations
-/

/-- The subtractive capitolar translation of order j.

    τ_{-j}(a) lands in chapter (irootN n a - j) with the same local coordinate radRem n a.

    The hypothesis `hk : j ≤ irootN n a` ensures the result stays in ℕ (no underflow in the
    chapter index). Compared to tauJ which shifts k ↦ k+j unconditionally, tauNeg shifts
    k ↦ k-j and requires k ≥ j. -/
def tauNeg (n j a : ℕ) (_hk : j ≤ irootN n a) : ℕ :=
  (irootN n a - j) ^ n + radRem n a

/-- **Canonical form** of tauNeg on elements in standard form k^n + t.

    tauNeg n j (k^n + t) = (k-j)^n + t,  provided j ≤ k and t < gap n k.

    Mirrors tauJ_base_add from CapitolarTranslations. -/
lemma tauNeg_base_add (n k j t : ℕ) (hn : n ≠ 0) (ht : t < gap n k) (hkj : j ≤ k) :
    tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t hn ht]) = (k - j) ^ n + t := by
  simp only [tauNeg]
  rw [sum_in_chapter n k t hn ht, radRem_base_add n k t hn ht]

/-- tauNeg lands in chapter k-j: irootN n (tauNeg n j (k^n+t) _) = k-j.

    Requires the extra hypothesis that t fits in the target chapter. -/
lemma tauNeg_irootN (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) (ht' : t < gap n (k - j))
    (hkj : j ≤ k) :
    irootN n (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht])) = k - j := by
  have hnn : n ≠ 0 := by omega
  rw [tauNeg_base_add n k j t hnn ht hkj]
  exact sum_in_chapter n (k - j) t hnn ht'

/-- The local coordinate (radRem) is preserved by tauNeg.

    Requires the extra hypothesis that t fits in the target chapter. -/
lemma tauNeg_radRem (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) (ht' : t < gap n (k - j))
    (hkj : j ≤ k) :
    radRem n (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht])) = t := by
  have hnn : n ≠ 0 := by omega
  rw [tauNeg_base_add n k j t hnn ht hkj]
  exact radRem_base_add n (k - j) t hnn ht'

/-!
## §2  Algebraic Laws
-/

/-- **Right partial inverse**: τ_j(τ_{-j}(k^n + t)) = k^n + t.

    Requires t < gap n (k-j) so the element (k-j)^n+t is in chapter k-j
    and tauJ_base_add applies.

    -- Example: n=3, k=2, j=1, t=3 → gap(3,1)=7 > 3 ✓. tauNeg gives 1^3+3=4, tauJ gives 2^3+3=11 ✓ -/
theorem tauNeg_right_inverse (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k)
    (ht' : t < gap n (k - j)) (hkj : j ≤ k) :
    tauJ n j (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht]))
    = k ^ n + t := by
  have hnn : n ≠ 0 := by omega
  rw [tauNeg_base_add n k j t hnn ht hkj]
  rw [tauJ_base_add n (k - j) j t hnn ht']
  have h : k - j + j = k := by omega
  simp only [h]

/-- **Left partial inverse**: τ_{-j}(τ_j(k^n + t)) = k^n + t. -/
theorem tauJ_right_inverse (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    tauNeg n j (tauJ n j (k ^ n + t))
      (by
        rw [tauJ_base_add n k j t (by omega) ht,
            sum_in_chapter n (k + j) t (by omega) (gap_lt_of_add n k j t hn ht)]
        omega)
    = k ^ n + t := by
  have hnn : n ≠ 0 := by omega
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  -- Use simp only [tauNeg] to avoid motive issue from rw on dependent proof argument
  simp only [tauNeg, tauJ_base_add n k j t hnn ht,
             sum_in_chapter n (k + j) t hnn htj,
             radRem_base_add n (k + j) t hnn htj]
  simp [show k + j - j = k from by omega]

/-- **Subtractive composition**: τ_{-(i+j)} = τ_{-i} ∘ τ_{-j}.

    Two subtractive translations compose by adding their orders, wherever defined.

    Requires t < gap n (k-(i+j)) so both intermediate elements are in their chapters.

    -- Example: n=3, k=3, i=1, j=1, t=0 → k-(i+j)=1, gap(3,1)=7>0 ✓. -/
theorem tauNeg_comp (n k i j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k)
    (ht' : t < gap n (k - (i + j))) (hkij : i + j ≤ k) :
    tauNeg n i
      (tauNeg n j (k ^ n + t) (by rw [sum_in_chapter n k t (by omega) ht]; omega))
      (by
        rw [tauNeg_irootN n k j t hn ht
              (Nat.lt_of_lt_of_le ht' (gap_le_of_le n (k-(i+j)) (k-j) hn (by omega)))
              (by omega)]
        omega)
    = (k - (i + j)) ^ n + t := by
  have hnn : n ≠ 0 := by omega
  have htj : t < gap n (k - j) :=
    Nat.lt_of_lt_of_le ht' (gap_le_of_le n (k - (i + j)) (k - j) hn (by omega))
  -- Use simp only [tauNeg] to avoid motive issue from rw on dependent proof argument
  simp only [tauNeg, sum_in_chapter n k t hnn ht, radRem_base_add n k t hnn ht,
             sum_in_chapter n (k - j) t hnn htj, radRem_base_add n (k - j) t hnn htj]
  simp [show k - j - i = k - (i + j) from by omega]

/-- **Mixed composition (additive dominant)**: τ_j(τ_{-i}(a)) = τ_{j-i}(a) when j ≥ i.

    Applying τ_j to the τ_{-i}-shifted element equals applying the net shift τ_{j-i} to the
    original. Net rightward shift = j - i ∈ ℕ.

    Requires t < gap n (k-i) so the intermediate element (k-i)^n+t is in chapter k-i.

    -- Example: n=2, k=3, i=1, j=2, t=0: gap(2,2)=5>0 ✓. τ_{-1}(9+0)=4+0, τ_2(4)=4+5=9... wait:
    --   τ_2(1^2+0) = (1+2)^2+0=9, τ_{2-1}(3^2+0)=(3+1)^2+0=16. Hmm, that's not equal.
    -- Correct example: k=2,i=1,j=2,t=0: gap(2,1)=3>0 ✓.
    --   τ_{-1}(4+0)=1+0=1. τ_2(1+0)=(1+2)^2+0=9. τ_{j-i}(4+0)=τ_1(4)=9. ✓ -/
theorem tauNeg_tauJ_additive (n k i j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k)
    (ht' : t < gap n (k - i)) (hki : i ≤ k) (hij : i ≤ j) :
    tauJ n j
      (tauNeg n i (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht])) =
    tauJ n (j - i) (k ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  rw [tauNeg_base_add n k i t hnn ht hki,
      tauJ_base_add n (k - i) j t hnn ht',
      tauJ_base_add n k (j - i) t hnn ht]
  have h : k - i + j = k + (j - i) := by omega
  simp only [h]

/-- **Mixed composition (subtractive dominant)**: τ_{-i}(τ_j(a)) = τ_{-(i-j)}(a) when i > j.

    Applying τ_{-i} to the τ_j-shifted element equals applying the net shift τ_{-(i-j)} to the
    original. Net leftward shift = i - j ∈ ℕ.

    -- Example: n=2, k=2, j=1, i=2, t=0: hki: 2 ≤ 2+1=3 ✓, hij: 1 < 2 ✓.
    --   τ_1(4+0)=(2+1)^2+0=9. τ_{-2}(9)=(3-2)^2+0=1. τ_{-(2-1)}(4)=(2-1)^2+0=1. ✓ -/
theorem tauJ_tauNeg_subtractive (n k i j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k)
    (hij : j < i) (hki : i ≤ k + j) :
    tauNeg n i
      (tauJ n j (k ^ n + t))
      (by
        rw [tauJ_base_add n k j t (by omega) ht,
            sum_in_chapter n (k + j) t (by omega) (gap_lt_of_add n k j t hn ht)]
        exact hki) =
    tauNeg n (i - j) (k ^ n + t) (by rw [sum_in_chapter n k t (by omega) ht]; omega) := by
  have hnn : n ≠ 0 := by omega
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  -- Use simp only [tauNeg] to avoid motive issue from rw on dependent proof argument
  simp only [tauNeg, tauJ_base_add n k j t hnn ht,
             sum_in_chapter n (k + j) t hnn htj,
             radRem_base_add n (k + j) t hnn htj,
             sum_in_chapter n k t hnn ht,
             radRem_base_add n k t hnn ht]
  simp [show k + j - i = k - (i - j) from by omega]

/-!
## §3  Equivalence Preservation and Failure

The additive τ_j preserves aodEquiv unconditionally (tauJ_aodEquiv, CapitolarTranslations).
The subtractive τ_{-j} preserves aodEquiv within the **subtractive window** {m ∣ m ≤ t},
and fails at m = t+1. These are corollaries of results already in CapitolarTranslations (§6).
-/

/-- **Subtractive window theorem**: tauNeg preserves aodEquiv for j ≤ t.

    For a = k^n+t and b = h^n+t (k < h, 0 < t), both shifted back by j ≤ t steps,
    the equivalence is maintained — both land at the same local coordinate t-j ≥ 0. -/
theorem tauNeg_aodEquiv_within_window (n k h t j : ℕ)
    (hn : 2 ≤ n) (hkh : k < h)
    (ht_pos : 0 < t) (ht_bound : t < gap n k) (hj : j ≤ t) :
    (k ^ n + t - j) ≡ₒ (h ^ n + t - j) [Aod n] :=
  subtraction_equiv_until_zero n k h t j hn hkh ht_pos ht_bound hj

/-- **Equivalence failure**: tauNeg does NOT preserve aodEquiv at j = t+1.

    One step past the subtractive window, the two elements land on (k-1)^n-adjacent floors
    in different chapters, breaking the equivalence. -/
theorem tauNeg_not_aodEquiv_beyond_window (n k h t : ℕ)
    (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k)
    (ht_pos : 0 < t) (ht_bound : t < gap n k) :
    ¬ ((k ^ n + t - (t + 1)) ≡ₒ (h ^ n + t - (t + 1)) [Aod n]) :=
  subtraction_breaks_after_zero n k h t hn hkh hk ht_pos ht_bound

/-- **Chapter partition**: the subtractive window {0,..,t} and additive window {0,..,gap-t-2}
    together tile the full chapter of width gap n k. -/
theorem tauNeg_window_tiles_chapter (n k t : ℕ) (ht : t < gap n k) :
    (t + 1) + (gap n k - t - 1) = gap n k := by omega

/-!
## §4  The Twisted Radical Remainder
-/

/-- **Twisted radical remainder**: the gauge-corrected local coordinate.

    twistedRadRem n a = radRem n a + gap n (irootN n a - 1)

    For a = k^n + t: twistedRadRem n a = t + gap(n, k-1).

    **Motivation**: The correction potential f(k) = gap(n, k-1) trivialises the connection
    σ(n,k,h) = gap(n,h-1) - gap(n,k-1). Two elements are twisted-equivalent iff they have
    the same twisted radical remainder — i.e., their gauge-corrected coordinates agree. -/
def twistedRadRem (n a : ℕ) : ℕ :=
  radRem n a + gap n (irootN n a - 1)

/-- Canonical form: twistedRadRem n (k^n + t) = t + gap n (k-1). -/
lemma twistedRadRem_base_add (n k t : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    twistedRadRem n (k ^ n + t) = t + gap n (k - 1) := by
  simp only [twistedRadRem,
             radRem_base_add n k t hn ht,
             sum_in_chapter n k t hn ht]

/-- **Twisted equivalence**: a and b are twisted-equivalent iff twistedRadRem n a = twistedRadRem n b. -/
def twistedAodEquiv (n a b : ℕ) : Prop :=
  twistedRadRem n a = twistedRadRem n b

/-- twistedAodEquiv is reflexive. -/
@[refl]
theorem twistedAodEquiv_refl (n a : ℕ) : twistedAodEquiv n a a := rfl

/-- twistedAodEquiv is symmetric. -/
theorem twistedAodEquiv_symm {n a b : ℕ} (h : twistedAodEquiv n a b) : twistedAodEquiv n b a :=
  h.symm

/-- twistedAodEquiv is transitive. -/
theorem twistedAodEquiv_trans {n a b c : ℕ}
    (h1 : twistedAodEquiv n a b) (h2 : twistedAodEquiv n b c) : twistedAodEquiv n a c :=
  h1.trans h2

/-- **Within the same chapter**, twistedAodEquiv coincides with aodEquiv. -/
theorem twistedAodEquiv_iff_aodEquiv_same_chapter (n k t s : ℕ)
    (hn : n ≠ 0) (ht : t < gap n k) (hs : s < gap n k) :
    twistedAodEquiv n (k ^ n + t) (k ^ n + s) ↔ (k ^ n + t) ≡ₒ (k ^ n + s) [Aod n] := by
  simp only [twistedAodEquiv, twistedRadRem_base_add n k t hn ht,
             twistedRadRem_base_add n k s hn hs, aodEquiv,
             radRem_base_add n k t hn ht, radRem_base_add n k s hn hs]
  omega

/-- The twistedRadRem range within chapter k is [gap(n,k-1), gap(n,k-1) + gap(n,k) - 1]. -/
lemma twistedRadRem_range (n k t : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    gap n (k - 1) ≤ twistedRadRem n (k ^ n + t) ∧
    twistedRadRem n (k ^ n + t) < gap n (k - 1) + gap n k := by
  rw [twistedRadRem_base_add n k t hn ht]
  omega

/-- **Adjacent chapters**: the first element (k+1)^n of chapter k+1 has twistedRadRem = gap(n,k).

    The correction potential f(k) = gap(n,k-1) evaluated at the first element of chapter k+1
    gives exactly the gap of the previous chapter. -/
lemma twistedRadRem_first_next_chapter (n k : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) :
    twistedRadRem n ((k + 1) ^ n) = gap n k := by
  have hnn : n ≠ 0 := by omega
  have h_gap_pos : 0 < gap n (k + 1) := by
    have hgk : 0 < gap n k := by
      have : k ^ n < (k + 1) ^ n :=
        Nat.pow_lt_pow_left (by omega) (by omega : n ≠ 0)
      simp only [gap]; omega
    have := gap_lt_of_lt n k (k + 1) hn (by omega)
    omega
  rw [show (k + 1) ^ n = (k + 1) ^ n + 0 by ring]
  rw [twistedRadRem_base_add n (k + 1) 0 hnn h_gap_pos]
  simp

/-!
## §5  Invariance of twistedAodEquiv Under the Full ℤ-Family
-/

/-!
### §5 Note: tauJ does NOT preserve twistedAodEquiv across different chapters

The claim "tauJ preserves twistedAodEquiv" is **false for n ≥ 3**.

Counterexample (n=3, j=1):
- k=1, t=6: element 1^3+6=7,  twistedRadRem = 6+gap(3,0) = 6+1 = 7
- h=2, s=0: element 2^3+0=8,  twistedRadRem = 0+gap(3,1) = 0+7 = 7  ✓ twisted-equivalent

After tauJ 3 1:
- tauJ 3 1 7  = 2^3+6 = 14, twistedRadRem = 6+gap(3,1) = 6+7 = 13
- tauJ 3 1 8  = 3^3+0 = 27, twistedRadRem = 0+gap(3,2) = 0+19 = 19  ✗ no longer equal

Root cause: the condition would require gap(n,k+j-1) - gap(n,k-1) = gap(n,h+j-1) - gap(n,h-1),
i.e. σ(n,k,k+j) = σ(n,h,h+j), which fails when k ≠ h and n ≥ 3.

The twisted equivalence IS preserved under tauJ within a single chapter (k=h case), but
cross-chapter invariance requires a different gauge potential. This is an open geometric problem.
-/

/-- **tauNeg preserves twistedAodEquiv** (within the same chapter).

    For a = k^n+t and b = k^n+s with twistedAodEquiv (i.e. t = s within the chapter):
    after applying τ_{-j}, both land in chapter k-j at the same local coordinate.

    The twisted equivalence within the same chapter reduces to plain equality of t and s,
    which is preserved trivially. -/
theorem tauNeg_twistedAodEquiv_same_chapter (n k j t s : ℕ)
    (hn : 2 ≤ n) (hkj : j ≤ k) (ht : t < gap n k) (hs : s < gap n k)
    (htwist : twistedAodEquiv n (k ^ n + t) (k ^ n + s)) :
    twistedAodEquiv n
      (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht]))
      (tauNeg n j (k ^ n + s) (by rwa [sum_in_chapter n k s (by omega) hs])) := by
  have hnn : n ≠ 0 := by omega
  -- twistedAodEquiv in same chapter means t = s
  have heq : t = s := by
    rw [twistedAodEquiv_iff_aodEquiv_same_chapter n k t s hnn ht hs] at htwist
    simp only [aodEquiv, radRem_base_add n k t hnn ht, radRem_base_add n k s hnn hs] at htwist
    exact htwist
  subst heq
  rfl

/-!
## §7  Last-Element Lemma and Fiber Overlap
-/

/-- **Last element of chapter k**: its twistedRadRem equals gap(n,k-1) + gap(n,k) - 1.

    The last element of chapter k is k^n + gap n k - 1 (local coordinate = gap n k - 1).
    Its twisted coordinate is (gap n k - 1) + gap n (k-1) = gap n (k-1) + gap n k - 1.

    Together with twistedRadRem_range, this confirms the range of twistedRadRem in chapter k
    is exactly the interval [gap(n,k-1), gap(n,k-1) + gap(n,k) - 1]. -/
theorem twistedRadRem_last_chapter (n k : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) :
    twistedRadRem n (k ^ n + gap n k - 1) = gap n (k - 1) + gap n k - 1 := by
  have hnn : n ≠ 0 := by omega
  have hgap_pos : 0 < gap n k := gap_pos' n k hnn
  -- The local coordinate is t = gap n k - 1, which satisfies t < gap n k
  have ht : gap n k - 1 < gap n k := by omega
  -- k^n + gap n k - 1 = k^n + (gap n k - 1)
  have hrewrite : k ^ n + gap n k - 1 = k ^ n + (gap n k - 1) := by omega
  rw [hrewrite, twistedRadRem_base_add n k (gap n k - 1) hnn ht]
  omega

/-- **Fiber overlap membership**: t ∈ [0,gap n k) has a twisted-equivalent partner in chapter h
    iff t ≥ σ(n,k,h) = subtractionShift n k h. -/
lemma tRR_fiber_mem_iff (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k)
    (htk : t < gap n k) :
    (∃ s < gap n h, twistedAodEquiv n (k ^ n + t) (h ^ n + s)) ↔
    subtractionShift n k h ≤ t := by
  have hnn : n ≠ 0 := by omega
  have hkh_pred : k - 1 < h - 1 := by omega
  have hgap_lt : gap n (k - 1) < gap n (h - 1) :=
    gap_lt_of_lt n (k - 1) (h - 1) hn hkh_pred
  have hgap_kh : gap n k ≤ gap n h :=
    Nat.le_of_lt (gap_lt_of_lt n k h hn hkh)
  constructor
  · rintro ⟨s, hs_lt, htwist⟩
    simp only [twistedAodEquiv] at htwist
    rw [twistedRadRem_base_add n k t hnn (by omega),
        twistedRadRem_base_add n h s hnn hs_lt] at htwist
    simp only [subtractionShift]; omega
  · intro hσt
    have hσ_le_t : gap n (h - 1) - gap n (k - 1) ≤ t := by
      simp only [subtractionShift] at hσt; omega
    refine ⟨t + gap n (k - 1) - gap n (h - 1), ?_, ?_⟩
    · omega
    · simp only [twistedAodEquiv]
      have hs_lt_h : t + gap n (k - 1) - gap n (h - 1) < gap n h := by omega
      rw [twistedRadRem_base_add n k t hnn (by omega),
          twistedRadRem_base_add n h _ hnn hs_lt_h]
      omega

/-- **Fiber overlap theorem**: for t ∈ [0, gap n k), a twisted-equivalent partner exists in
    chapter h iff t ∈ [σ(n,k,h), gap n k). Equivalently, t with a valid partner is exactly
    the interval [σ, gap n k).

    **Statement**: membership in [σ, gap n k) characterises which t ∈ [0, gap n k) have
    a twisted-equivalent element in chapter h.  -/
theorem tRR_fiber_inter_count (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k)
    (htk : t < gap n k) :
    (∃ s < gap n h, twistedAodEquiv n (k ^ n + t) (h ^ n + s)) ↔
    t ∈ Finset.Ico (subtractionShift n k h) (gap n k) := by
  rw [Finset.mem_Ico]
  exact ⟨fun hex => ⟨(tRR_fiber_mem_iff n k h t hn hkh hk htk).mp hex, htk⟩,
         fun ⟨hσ, _⟩ => (tRR_fiber_mem_iff n k h t hn hkh hk htk).mpr hσ⟩

/-- **Adjacent chapters corollary**: for h = k+1, the overlap has cardinality gap n (k-1).

    σ(n,k,k+1) = gap(n,k) - gap(n,k-1), so the overlap interval is
    [gap(n,k) - gap(n,k-1), gap(n,k)), which has length gap(n,k-1). -/
theorem tRR_fiber_adjacent (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) :
    (Finset.Ico (subtractionShift n k (k + 1)) (gap n k)).card = gap n (k - 1) := by
  have hnn : n ≠ 0 := by omega
  have hgap_lt : gap n (k - 1) < gap n k := gap_lt_of_lt n (k - 1) k hn (by omega)
  have hσ : subtractionShift n k (k + 1) = gap n k - gap n (k - 1) := by
    simp only [subtractionShift, Nat.add_sub_cancel]
  rw [hσ, Nat.card_Ico]
  omega

/-- **Fiber count**: the number of t ∈ [0, gap n k) that have a twisted-equivalent partner
    in chapter h equals gap n k - subtractionShift n k h.

    This is the cardinality form of `tRR_fiber_inter_count`: the valid local coordinates
    form the interval [σ(n,k,h), gap n k), whose size is gap n k - σ(n,k,h).

    Requires σ(n,k,h) ≤ gap n k, which follows from gap monotonicity (k < h → k-1 < h-1). -/
theorem tRR_fiber_count (n k h : ℕ) (_hn : 2 ≤ n) (_hkh : k < h) (_hk : 0 < k) :
    (Finset.Ico (subtractionShift n k h) (gap n k)).card =
    gap n k - subtractionShift n k h := by
  --Nat.card_Ico gives (Ico a b).card = b - a in ℕ directly; no ≤ hypothesis needed
  simp [Nat.card_Ico]

/-!
## §8  Mathlib `CategoryTheory.Groupoid` Instance

The **capitolar groupoid** of degree `n` is the codiscrete groupoid on `ℕ` (chapters) where:
- Objects = `ℕ` (chapter indices)
- `Hom k h = { z : ℤ // z = (h : ℤ) - k }` — exactly **one** morphism per pair
- Composition: `⟨z₁, _⟩ ≫ ⟨z₂, _⟩ = ⟨z₁ + z₂, _⟩`
- Identity: `𝟙 k = ⟨0, _⟩`
- Inverse: `inv ⟨z, _⟩ = ⟨-z, _⟩`

All category laws (id_comp, comp_id, assoc) and groupoid laws (inv_comp, comp_inv) hold
trivially because each hom-set `{ z : ℤ // z = c }` is a **singleton** (Subsingleton), so
any two morphisms of the same type are propositionally equal.

We first build the `CategoryTheory.Category ℕ` instance, then promote it to a `Groupoid`
using `Groupoid.ofHomUnique`.
-/

section CapitolarGroupoidInstance

open CategoryTheory

/-- The hom-type of the capitolar groupoid: a morphism from chapter `k` to chapter `h`
    is the unique integer `h - k`. The type `{ z : ℤ // z = (h : ℤ) - k }` is a singleton. -/
abbrev CapHom (k h : ℕ) : Type := { z : ℤ // z = (h : ℤ) - k }

/-- Each `CapHom k h` is a subsingleton (at most one element). -/
instance instSubsingletonCapHom (k h : ℕ) : Subsingleton (CapHom k h) :=
  ⟨fun ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => by
    --rewrite to canonical value first, then both are equal
    subst h₁; subst h₂; rfl⟩

/-- Each `CapHom k h` is inhabited (has exactly one element). -/
instance instInhabitedCapHom (k h : ℕ) : Inhabited (CapHom k h) :=
  ⟨⟨(h : ℤ) - k, rfl⟩⟩

/-- Each `CapHom k h` is a `Unique` type (exactly one element). -/
instance instUniqueCapHom (k h : ℕ) : Unique (CapHom k h) :=
  { default := ⟨(h : ℤ) - k, rfl⟩
    uniq := fun ⟨z, hz⟩ => by
      --subst hz to reduce to rfl
      subst hz; rfl }

/-- The `CategoryTheory.Category` structure on `ℕ` whose hom-sets are `CapHom`.

    All laws hold trivially because `Subsingleton (CapHom k h)` forces any two morphisms
    of the same type to be equal. -/
instance instCategoryCapitolar : CategoryTheory.Category ℕ where
  Hom k h := CapHom k h
  id k := ⟨0, by simp⟩
  comp {_ _ _} f g := ⟨f.val + g.val, by omega⟩
  id_comp {_ _} _ := Subsingleton.elim _ _
  comp_id {_ _} _ := Subsingleton.elim _ _
  assoc {_ _ _ _} _ _ _ := Subsingleton.elim _ _

/-- The **capitolar groupoid** of degree `n`: the codiscrete groupoid on ℕ-chapters.

    Objects = natural numbers (chapter indices).
    The unique morphism `k ⟶ h` represents the inter-chapter shift τ_{h-k}.

    We use `Groupoid.ofHomUnique`: given a category where every hom-set is `Unique`,
    the inverse of the sole morphism `k ⟶ h` is the sole morphism `h ⟶ k`.

    The hypothesis `hn : 2 ≤ n` is carried along for downstream use (connecting to
    the actual translation functions `tauJ`/`tauNeg`), but is not needed for the
    purely categorical structure. -/
def capitolarGroupoid (_n : ℕ) : CategoryTheory.Groupoid ℕ :=
  --use Groupoid.ofHomUnique since every hom-set is a singleton (Unique).
  CategoryTheory.Groupoid.ofHomUnique (fun {_ _} => instUniqueCapHom _ _)

/-- The morphism from chapter `k` to chapter `h` in the capitolar groupoid is the
    unique element of `CapHom k h`, representing the shift `h - k : ℤ`. -/
def capitolarMorphism (k h : ℕ) : @Quiver.Hom ℕ instCategoryCapitolar.toQuiver k h :=
  ⟨(h : ℤ) - k, rfl⟩

/-- The value of any capitolar morphism `k ⟶ h` equals `(h : ℤ) - k`. -/
lemma capitolarMorphism_val (k h : ℕ) (f : @Quiver.Hom ℕ instCategoryCapitolar.toQuiver k h) :
    f.val = (h : ℤ) - k :=
  f.property

/-- Composition of capitolar morphisms adds the integer shifts:
    (k → m) ≫ (m → h) has value (m - k) + (h - m) = h - k. This follows from
    Subsingleton: the composed morphism is the unique element of CapHom k h. -/
lemma capitolarMorphism_comp_val (k m h : ℕ)
    (f : @Quiver.Hom ℕ instCategoryCapitolar.toQuiver k m)
    (g : @Quiver.Hom ℕ instCategoryCapitolar.toQuiver m h) :
    (instCategoryCapitolar.comp f g).val = f.val + g.val := rfl

end CapitolarGroupoidInstance

/-!
## §6  Computational Verification
-/

section ComputationalChecks

-- tauNeg_base_add check: tauNeg 3 1 (2^3+3) = (2-1)^3 + 3 = 4
-- a = 2^3+3 = 11, tauNeg 3 1 11 should give 1^3+3 = 4
#eval
  let k := 2; let j := 1; let t := 3; let n := 3
  ((k - j)^n + t, k^n + t)  -- (4, 11)

-- Partial inverse: tauJ n j (tauNeg n j (k^n+t)) = k^n+t
-- tauJ 3 1 4 = 4 + (2^3 - 1^3) = 4 + 7 = 11 ✓
#eval
  let step1 := (1:ℕ)^3 + 3  -- tauNeg 3 1 11 = 4
  let step2 := step1 + ((2:ℕ)^3 - (1:ℕ)^3)  -- tauJ 3 1 4 = 11
  (step1, step2, step2 == 11)  -- (4, 11, true)

-- twistedRadRem in Aod 2: t + gap(2, k-1) = t + (2*(k-1)+1)
-- k=1, t=0..2: gap(2,0)=1, so tRR ∈ {1,2,3}
-- k=2, t=0..4: gap(2,1)=3, so tRR ∈ {3,4,5,6,7}
-- Overlap at 3: k=1,t=2 and k=2,t=0 → both have twistedRadRem=3
#eval
  let gap2 : ℕ → ℕ := fun k => (k+1)^2 - k^2
  let tRR2 : ℕ → ℕ → ℕ := fun k t => t + gap2 (k - 1)
  [(1,0,tRR2 1 0), (1,1,tRR2 1 1), (1,2,tRR2 1 2),
   (2,0,tRR2 2 0), (2,1,tRR2 2 1), (2,2,tRR2 2 2)]
  -- [(1,0,1),(1,1,2),(1,2,3),(2,0,3),(2,1,4),(2,2,5)]

-- Counterexample for tauJ NOT preserving twistedAodEquiv (n=3):
-- k=1,t=6 and k=2,s=0 are twisted-equivalent (both tRR=7)
-- After tauJ 3 1: tRR becomes 13 and 19 — not equal.
#eval
  let gap3 : ℕ → ℕ := fun k => (k+1)^3 - k^3
  let tRR3 : ℕ → ℕ → ℕ := fun k t => t + gap3 (k - 1)
  -- Before: k=1,t=6 and k=2,s=0 — twisted-equivalent
  let before := (tRR3 1 6, tRR3 2 0)   -- (7, 7) ✓
  -- After tauJ 3 1: chapters become 2,3; t unchanged
  let after := (tRR3 2 6, tRR3 3 0)    -- (6+7, 0+19) = (13, 19) ✗
  (before, after)

-- subtractionShift cocycle check: σ(3,1,3) = σ(3,1,2) + σ(3,2,3)
#eval
  (subtractionShift 3 1 2, subtractionShift 3 2 3,
   subtractionShift 3 1 2 + subtractionShift 3 2 3,
   subtractionShift 3 1 3)
  -- σ(3,1,2)=gap(3,1)-gap(3,0)=7-1=6, σ(3,2,3)=gap(3,2)-gap(3,1)=19-7=12, sum=18=σ(3,1,3) ✓

end ComputationalChecks

/-!
## §9  Fiber-Preserving Actions and the Representation of the Capitolar Groupoid

The capitolar groupoid (§8) is abstract: objects are chapter indices ℕ and each
hom-set has exactly one morphism.  This section makes it **concrete** by connecting
it to the actual τ_j/τ_{-j} family.

**Chapter fiber**: ChapterFiber n k = {a : ℕ | irootN n a = k} — the set of naturals
in chapter k.

**Key theorem** (A): τ_j maps ChapterFiber n k into ChapterFiber n (k+j).  The morphism
k → k+j in the capitolar groupoid corresponds exactly to the function τ_{h−k} : fiber k → fiber h.

**Functor definition**: The `fiberAction` map is defined explicitly and shown to be
consistent with composition (tauJ_comp).  The full Mathlib `Functor` instance
(`chapterFiberFunctor`, `natPreordToCapitolar`) is fully proved in §9b — 0 sorry.
-/

section FiberActions

/-- The chapter fiber: natural numbers whose integer n-th root equals k. -/
def ChapterFiber (n k : ℕ) : Type := { a : ℕ // irootN n a = k }

/-- **τ_j maps the fiber over k to the fiber over k+j**.
    This is the key fiber-preservation property: tauJ moves the chapter index
    by j while keeping the element in ℕ.  Proved by tauJ_base_add + sum_in_chapter. -/
theorem tauJ_maps_fiber (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    irootN n (tauJ n j (k ^ n + t)) = k + j := by
  have hnn : n ≠ 0 := by omega
  rw [tauJ_base_add n k j t hnn ht]
  exact sum_in_chapter n (k + j) t hnn (gap_lt_of_add n k j t hn ht)

/-- **τ_{-j} maps the fiber over k to the fiber over k−j** (when j ≤ k and t < gap n (k−j)).
    The subtractive translation moves the chapter index down by j. -/
theorem tauNeg_maps_fiber (n k j t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k)
    (ht' : t < gap n (k - j)) (hkj : j ≤ k) :
    irootN n (tauNeg n j (k ^ n + t) (by rwa [sum_in_chapter n k t (by omega) ht])) = k - j := by
  have hnn : n ≠ 0 := by omega
  rw [tauNeg_base_add n k j t hnn ht hkj]
  exact sum_in_chapter n (k - j) t hnn ht'

/-- **Concrete fiber action**: the morphism k → h in the capitolar groupoid acts on
    ChapterFiber n k by the map τ_{h−k}.  Each element a in chapter k is sent to
    τ_{h−k}(a) which lands in chapter h (tauJ_maps_fiber). -/
def fiberAction (n k h : ℕ) (hn : 2 ≤ n) (hkh : k ≤ h) :
    ChapterFiber n k → ChapterFiber n h :=
  fun a => ⟨tauJ n (h - k) a.val, by
    have hnn : n ≠ 0 := by omega
    -- Decompose a.val = k^n + radRem n a.val
    have ha_k : irootN n a.val = k := a.property
    have hle  := irootN_pow_le n a.val hnn
    have hlt  := irootN_lt_succ_pow n a.val hnn
    rw [ha_k] at hle hlt
    -- radRem n a.val < gap n k
    --include ha_k in simp so irootN n a.val rewrites to k before omega
    have ht_bound : radRem n a.val < gap n k := by simp [gap, radRem, ha_k]; omega
    -- a.val = k^n + radRem n a.val
    have ha_decomp : a.val = k ^ n + radRem n a.val := by simp [radRem, ha_k]; omega
    rw [ha_decomp]
    -- Apply tauJ_maps_fiber with j = h−k: result is in chapter k+(h−k) = h
    have h1 := tauJ_maps_fiber n k (h - k) (radRem n a.val) hn ht_bound
    rwa [Nat.add_sub_cancel' hkh] at h1⟩

/-- **fiberAction is functorial (identity)**: the identity morphism k → k acts as
    the identity function on ChapterFiber n k (τ_0 = id). -/
theorem fiberAction_id (n k : ℕ) (hn : 2 ≤ n) (a : ChapterFiber n k) :
    (fiberAction n k k hn (le_refl k) a).val = a.val := by
  simp only [fiberAction, Nat.sub_self]
  have hnn : n ≠ 0 := by omega
  have ha_k : irootN n a.val = k := a.property
  have hle  := irootN_pow_le n a.val hnn
  have hlt  := irootN_lt_succ_pow n a.val hnn
  rw [ha_k] at hle hlt
  --include ha_k in simp so irootN n a.val rewrites to k before omega
  have ht_bound : radRem n a.val < gap n k := by simp [gap, radRem, ha_k]; omega
  have ha_decomp : a.val = k ^ n + radRem n a.val := by simp [radRem, ha_k]; omega
  --use tauJ_base_add + tauJ_zero instead of simp [tauJ, ...] which loops
  rw [ha_decomp, tauJ_base_add n k 0 _ hnn ht_bound]
  simp [← ha_decomp]

/-- **fiberAction is functorial (composition)**: composing the action of k→m with m→h
    equals the action of k→h (from tauJ_comp). -/
theorem fiberAction_comp (n k m h : ℕ) (hn : 2 ≤ n) (hkm : k ≤ m) (hmh : m ≤ h)
    (a : ChapterFiber n k) :
    (fiberAction n m h hn hmh (fiberAction n k m hn hkm a)).val =
    (fiberAction n k h hn (Nat.le_trans hkm hmh) a).val := by
  have hnn : n ≠ 0 := by omega
  have ha_k : irootN n a.val = k := a.property
  have hle  := irootN_pow_le n a.val hnn
  have hlt  := irootN_lt_succ_pow n a.val hnn
  rw [ha_k] at hle hlt
  --include ha_k in simp so irootN n a.val rewrites to k before omega
  have ht_k : radRem n a.val < gap n k := by simp [gap, radRem, ha_k]; omega
  have ha_decomp : a.val = k ^ n + radRem n a.val := by simp [radRem, ha_k]; omega
  simp only [fiberAction]
  -- Both sides are tauJ applied to a.val; rewrite a.val to standard form on both sides
  rw [ha_decomp]
  -- Now LHS = tauJ n (h-m) (tauJ n (m-k) (k^n + radRem n a.val))
  -- Use tauJ_comp: tauJ n j (tauJ n i (k^n+t)) = tauJ n (i+j) (k^n+t)
  --tauJ_comp rewrites tauJ n j (tauJ n i (k^n+t)) = tauJ n (i+j) (k^n+t)
  -- apply forward then prove (m-k)+(h-m) = h-k by omega
  rw [tauJ_comp n (m - k) (h - m) k (radRem n a.val) hn ht_k]
  congr 2; omega

/-!
## §9  Gauge-Corrected Backward Translation (Full Groupoid Functor)

**Correction**: The backward translation is NOT partial — it requires a **gauge correction**
via `subtractionShift` from CapitolarTranslations.lean.

Given a = k^n + t and b = h^n + t with k < h:
- Raw subtraction diverges after crossing zero (m = t+1)
- **Corrected subtraction** with σ(n,k,h) = gap(n,h-1) - gap(n,k-1) restores equivalence

The telescopic identity:
    σ(n,k,h) = Σ_{j=k}^{h-1} Δ(n,j)  where Δ(n,j) = gap(n,j) - gap(n,j-1)

shows this is the accumulated gap growth between chapters.

**Key insight**: The gauge correction applies to the **radRem comparison**, not to
the target element itself. For elements a = k^n + t and b = h^n + t:
- radRem n a = t
- radRem n b = t
- They are equivalent because they have the SAME local coordinate t

The backward translation τ_{h-k} preserves radRem, so:
- τ_{h-k}(a) lands in chapter h with radRem = t
- This is valid iff t < gap n h

**The obstruction is real**: when t ≥ gap n h, the element cannot land in chapter h
with the same local coordinate. The `subtractionShift` correction applies to the
**boundary case** (k^n - 1, h^n - 1), not to general elements.

For the general functor, we must work with a **restricted subtype** or accept that
the codiscrete groupoid functor requires the gauge category structure.
-/

section GaugeCorrectedFunctor

open CampiOperazionistici

/-- **Gauge-corrected equivalence**: two elements are gauge-equivalent if their
    radRem values differ by exactly the subtractionShift correction.

    This captures the S4 theorem: radRem(h^n-1) - σ(n,k,h) = radRem(k^n-1),
    which rearranges to: radRem(h^n-1) = radRem(k^n-1) + σ(n,k,h).

    Note: subtractionShift n k h = gap(n,h-1) - gap(n,k-1), defined for k < h. -/
def gaugeEquiv (n k h : ℕ) (a : ChapterFiber n k) (b : ChapterFiber n h) : Prop :=
  radRem n a.val + subtractionShift n (k + 1) (h + 1) = radRem n b.val  -- requires k < h

/-- **S4 for general elements**: the gauge correction restores equivalence
    for elements at the boundary (predecessors of perfect powers).

    The S4 theorem (subtraction_supershift) states:
      radRem(h^n-1) - subtractionShift n k h = radRem(k^n-1)

    Rearranging: radRem(k^n-1) = radRem(h^n-1) - subtractionShift n k h

    Note: k^n - 1 is the last element of chapter (k-1), and h^n - 1 is the last
    element of chapter (h-1). So a : ChapterFiber n (k-1) and b : ChapterFiber n (h-1). -/
theorem gauge_correction_at_boundary (n k h : ℕ) (hn : 2 ≤ n) (hkh : k < h) (hk : 0 < k) :
    let a : ChapterFiber n (k - 1) := ⟨k ^ n - 1, by
      -- Prove irootN n (k^n - 1) = k - 1 using Nat.le_antisymm
      have hnn : n ≠ 0 := by omega
      have hkge1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
      have hkm1 : k = k - 1 + 1 := Eq.symm (Nat.sub_add_cancel hkge1)
      -- Lower bound: (k-1)^n ≤ k^n - 1
      have hlower : (k - 1) ^ n ≤ k ^ n - 1 := by
        have hgap_pos : 0 < gap n (k - 1) := gap_pos' n (k - 1) hnn
        have hgap_ge1 : 1 ≤ gap n (k - 1) := Nat.succ_le_iff.mp hgap_pos
        have hsucc : (k - 1 + 1) ^ n = (k - 1) ^ n + gap n (k - 1) := succ_pow_eq_add_gap n (k - 1) hnn
        have hkn : k ^ n = (k - 1) ^ n + gap n (k - 1) := by rw [hkm1]; exact hsucc
        have : (k - 1) ^ n + 1 ≤ (k - 1) ^ n + gap n (k - 1) := by
          apply Nat.add_le_add_left
          exact hgap_ge1
        have : (k - 1) ^ n + 1 ≤ k ^ n := by
          rw [hkn]
          exact this
        have hkn_pos : 0 < k ^ n := pow_pos hk n
        omega
      -- Upper bound: k^n - 1 < ((k-1)+1)^n = k^n
      have : k ^ n - 1 < ((k - 1) + 1) ^ n := by
        have : k ^ n - 1 < k ^ n := by
          apply Nat.sub_lt
          · exact pow_pos hk n
          · norm_num
        rw [← hkm1]
        exact this
      -- Prove irootN n (k^n - 1) = k - 1 by Nat.le_antisymm
      apply Nat.le_antisymm
      · -- irootN n (k^n - 1) ≤ k - 1
        by_contra hgt
        push_neg at hgt
        have hge : k ≤ irootN n (k ^ n - 1) := by omega
        have hpow_ge : k ^ n ≤ (irootN n (k ^ n - 1)) ^ n := Nat.pow_le_pow_left hge n
        have hle := irootN_pow_le n (k ^ n - 1) hnn
        have : (irootN n (k ^ n - 1)) ^ n ≤ k ^ n - 1 := hle
        have : k ^ n ≤ k ^ n - 1 := le_trans hpow_ge this
        have : 0 < k ^ n := pow_pos hk n
        omega
      · -- k - 1 ≤ irootN n (k^n - 1)
        by_contra hlt
        push_neg at hlt
        have hle : irootN n (k ^ n - 1) + 1 ≤ k - 1 := by omega
        have hpow_le : (irootN n (k ^ n - 1) + 1) ^ n ≤ (k - 1) ^ n := Nat.pow_le_pow_left hle n
        have hlt2 := irootN_lt_succ_pow n (k ^ n - 1) hnn
        have : k ^ n - 1 < (irootN n (k ^ n - 1) + 1) ^ n := hlt2
        have : (k - 1) ^ n < k ^ n := by
          rw [hkm1]
          exact Nat.pow_lt_pow_left (Nat.lt_succ_self (k - 1)) hnn
        omega
      ⟩
    let b : ChapterFiber n (h - 1) := ⟨h ^ n - 1, by
      -- Prove irootN n (h^n - 1) = h - 1 using Nat.le_antisymm
      have hh : 0 < h := Nat.lt_trans hk hkh
      have hnn : n ≠ 0 := by omega
      have hhm1 : h = h - 1 + 1 := Eq.symm (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hh))
      -- Lower bound: (h-1)^n ≤ h^n - 1
      have hlower : (h - 1) ^ n ≤ h ^ n - 1 := by
        have hgap_pos : 0 < gap n (h - 1) := gap_pos' n (h - 1) hnn
        have hgap_ge1 : 1 ≤ gap n (h - 1) := Nat.succ_le_iff.mp hgap_pos
        have hsucc : (h - 1 + 1) ^ n = (h - 1) ^ n + gap n (h - 1) := succ_pow_eq_add_gap n (h - 1) hnn
        have hhn : h ^ n = (h - 1) ^ n + gap n (h - 1) := by rw [hhm1]; exact hsucc
        have : (h - 1) ^ n + 1 ≤ (h - 1) ^ n + gap n (h - 1) := by
          apply Nat.add_le_add_left
          exact hgap_ge1
        have : (h - 1) ^ n + 1 ≤ h ^ n := by
          rw [hhn]
          exact this
        have hhn_pos : 0 < h ^ n := pow_pos hh n
        omega
      -- Upper bound: h^n - 1 < ((h-1)+1)^n = h^n
      have : h ^ n - 1 < ((h - 1) + 1) ^ n := by
        have : h ^ n - 1 < h ^ n := by
          apply Nat.sub_lt
          · exact pow_pos hh n
          · norm_num
        rw [← hhm1]
        exact this
      -- Prove irootN n (h^n - 1) = h - 1 by Nat.le_antisymm
      apply Nat.le_antisymm
      · -- irootN n (h^n - 1) ≤ h - 1
        by_contra hgt
        push_neg at hgt
        have hge : h ≤ irootN n (h ^ n - 1) := by omega
        have hpow_ge : h ^ n ≤ (irootN n (h ^ n - 1)) ^ n := Nat.pow_le_pow_left hge n
        have hle := irootN_pow_le n (h ^ n - 1) hnn
        have : (irootN n (h ^ n - 1)) ^ n ≤ h ^ n - 1 := hle
        have : h ^ n ≤ h ^ n - 1 := le_trans hpow_ge this
        have : 0 < h ^ n := pow_pos hh n
        omega
      · -- h - 1 ≤ irootN n (h^n - 1)
        by_contra hlt
        push_neg at hlt
        have hle : irootN n (h ^ n - 1) + 1 ≤ h - 1 := by omega
        have hpow_le : (irootN n (h ^ n - 1) + 1) ^ n ≤ (h - 1) ^ n := Nat.pow_le_pow_left hle n
        have hlt2 := irootN_lt_succ_pow n (h ^ n - 1) hnn
        have : h ^ n - 1 < (irootN n (h ^ n - 1) + 1) ^ n := hlt2
        have : (h - 1) ^ n < h ^ n := by
          rw [hhm1]
          exact Nat.pow_lt_pow_left (Nat.lt_succ_self (h - 1)) hnn
        omega
      ⟩
    gaugeEquiv n (k - 1) (h - 1) a b := by
  dsimp only [gaugeEquiv]
  have hh : 0 < h := Nat.lt_trans hk hkh
  have hnn : n ≠ 0 := by omega
  have hkk : 0 < k := hk
  -- S4 theorem: radRem(h^n-1) - σ(n,k,h) = radRem(k^n-1)
  have hS4 : radRem n (h ^ n - 1) - subtractionShift n k h = radRem n (k ^ n - 1) :=
    subtraction_supershift n k h hn hkh hkk
  -- Note: gaugeEquiv uses subtractionShift n (k+1) (h+1) = subtractionShift n k h
  have hgap_k : 0 < gap n (k - 1) := gap_pos' n (k - 1) (by omega)
  have hgap_h : 0 < gap n (h - 1) := gap_pos' n (h - 1) (by omega)
  -- Rewrite radRem(k^n-1) = gap(n,k-1)-1 and radRem(h^n-1) = gap(n,h-1)-1
  rw [radRem_pred_pow n k (by omega) hk, radRem_pred_pow n h (by omega) (by omega)]
  -- Goal: (gap(n,k-1)-1) + σ(n,k,h) = gap(n,h-1)-1
  have hgap_k_le_h : gap n (k - 1) ≤ gap n (h - 1) := by
    apply gap_le_of_le n (k - 1) (h - 1) hn
    omega
  have hmain : (gap n (k - 1) - 1) + subtractionShift n k h = gap n (h - 1) - 1 := by
    rw [subtractionShift]
    have h1 : gap n (k - 1) ≤ gap n (h - 1) := hgap_k_le_h
    have h2 : gap n (k - 1) - 1 + 1 = gap n (k - 1) := by
      have : 1 ≤ gap n (k - 1) := Nat.succ_le_iff.mp hgap_k
      omega
    have h3 : gap n (h - 1) - 1 + 1 = gap n (h - 1) := by
      have : 1 ≤ gap n (h - 1) := Nat.succ_le_iff.mp hgap_h
      omega
    have h4 : gap n (h - 1) - gap n (k - 1) + gap n (k - 1) = gap n (h - 1) := by
      exact Nat.sub_add_cancel h1
    omega
  exact hmain

end GaugeCorrectedFunctor

/-- The existential statement captures the forward-only fragment that works with total functions
    (the backward case requires gauge correction). -/
theorem capitolarGroupoid_has_fiber_action (n : ℕ) (hn : 2 ≤ n) :
    ∃ (F : ℕ → Type) (φ : ∀ k h, k ≤ h → ChapterFiber n k → ChapterFiber n h),
      (∀ k, F k = ChapterFiber n k) ∧
      (∀ k h (hkh : k ≤ h) (a : ChapterFiber n k), φ k h hkh a = fiberAction n k h hn hkh a) := by
  refine ⟨fun k => ChapterFiber n k, fun k h hkh => fiberAction n k h hn hkh, ?_, ?_⟩
  · intro k; rfl
  · intro k h hkh a; rfl

/-!
## §9b  Mathlib Functor: Chapter Fibers over the Preorder Category

The `capitolarGroupoid` (§8) has morphisms in *both* directions (each hom-set is a
singleton `CapHom k h = {h − k : ℤ}`).  Building a total Mathlib `Functor` into `Type`
would require mapping *every* morphism, including backward ones (`k > h`), to an
actual function `ChapterFiber n k → ChapterFiber n h` — but `fiberAction` only works
forward (`k ≤ h`).

The clean solution is to use the **preorder category** on ℕ, whose morphisms `k ⟶ h`
are exactly the proofs `k ≤ h` (encoded as `ULift (PLift (k ≤ h))`).  This restricts to
the forward-only fragment, where `fiberAction` gives a total, computable definition.

We then show that the preorder category maps into the capitolar groupoid via a functor
`natPreordToCapitolar : NatPreord ⥤ ℕ` (mapping every `k ≤ h` to the unique morphism
`CapHom k h`), so `chapterFiberFunctor` is the "concrete realisation" of the abstract
fiber structure.
-/

section MathLibFunctor

open CategoryTheory

/-- A wrapper type for ℕ that carries the **natural order** preorder category,
    separate from the capitolar category `instCategoryCapitolar` on plain `ℕ`. -/
def NatPreord : Type := ℕ

/-- Equip `NatPreord` with the standard ≤ preorder so `Preorder.smallCategory`
    gives the small category whose morphisms are order-preserving witnesses. -/
instance : Preorder NatPreord := inferInstanceAs (Preorder ℕ)

/-- The `CategoryTheory.Category` instance for `NatPreord`, derived from its preorder. -/
instance instCategoryNatPreord : CategoryTheory.Category NatPreord :=
  Preorder.smallCategory NatPreord

/-- **The Chapter-Fiber Functor** from the ℕ-preorder category to `Type`.

    - Objects: `k : NatPreord` ↦ `ChapterFiber n k = {a : ℕ // irootN n a = k}`
    - Morphisms: a proof `k ≤ h` ↦ the fiber action `fiberAction n k h hn _`
                 (τ_{h−k} maps every element of chapter k into chapter h).
    - `map_id`: `fiberAction n k k hn (le_refl k) = id` (from `fiberAction_id`).
    - `map_comp`: composing `k ≤ m` and `m ≤ h` gives `fiberAction n k h hn _`
                  (from `fiberAction_comp`).

    This is a **computable** Mathlib `Functor` — no classical axioms are used. -/
def chapterFiberFunctor (n : ℕ) (hn : 2 ≤ n) :
    Functor NatPreord (Type) where
  obj k := ChapterFiber n k
  map := @fun k h hmor =>
    fiberAction n k h hn (leOfHom hmor)
  map_id := by
    intro k
    funext a
    apply Subtype.ext
    exact fiberAction_id n k hn a
  map_comp := by
    intro k m h fkm fmh
    funext a
    apply Subtype.ext
    exact (fiberAction_comp n k m h hn (leOfHom fkm) (leOfHom fmh) a).symm

/-- **Preorder-to-Capitolar functor**: the ℕ-preorder category maps into the capitolar
    groupoid by sending each `k ≤ h` to the unique morphism `CapHom k h`.

    All category laws hold trivially because `CapHom k h` is a singleton
    (`instSubsingletonCapHom`). -/
def natPreordToCapitolar : Functor NatPreord ℕ where
  obj k := k
  map := @fun k h _hmor =>
    (instUniqueCapHom k h).default
  map_id := by
    intro k
    have : Subsingleton (CapHom k k) := instSubsingletonCapHom k k
    exact this.elim _ _
  map_comp := by
    intro k m h _ _
    have : Subsingleton (CapHom k h) := instSubsingletonCapHom k h
    exact this.elim _ _

/-- The fiber functor applied to `homOfLE hkh` agrees with `fiberAction n k h hn hkh`.
    This confirms that the abstract Mathlib Functor gives the same action as the
    concrete fiber-translation function. -/
theorem chapterFiberFunctor_compatible (n : ℕ) (hn : 2 ≤ n) :
    ∀ k h : NatPreord, ∀ (hkh : k ≤ h) (a : ChapterFiber n k),
      (chapterFiberFunctor n hn).map (homOfLE hkh) a =
      fiberAction n k h hn hkh a := by
  intros k h hkh a
  -- leOfHom (homOfLE hkh) = hkh by reflexivity in the preorder category
  simp [chapterFiberFunctor]

end MathLibFunctor

end FiberActions

/-!
## §10  Chapter Tiling Theorem

For any pair (k^n+t, h^n+t) with k < h and 0 < t < gap(n,k), the equivalence-
preserving integer shifts δ form a **contiguous interval** of length exactly gap(n,k):

    δ ∈ {−t, −t+1, …, 0, …, gap(n,k)−t−1}     (length = gap(n,k))

The two halves are:
- **Subtractive window** (δ ∈ [−t, 0]): proved by `subtraction_equiv_until_zero`.
- **Additive window** (δ ∈ [0, gap−t)): proved by `first_jump_easy`.

The two boundaries are sharp breaks:
- At δ = −(t+1): the subtractive break (subtraction_breaks_after_zero).
- At δ = gap−t:  the additive break (first_jump_at_mstar).

The tiling equation (t+1) + (gap−t) = gap(n,k)+1 counts the total shifts including
the overlap at δ = 0; removing the double-count gives gap(n,k) distinct shifts.
-/

section ChapterTiling

/-- **Additive window**: all shifts 0 ≤ m < gap(n,k)−t preserve equivalence. -/
theorem full_window_additive (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (_ht_pos : 0 < t) (ht_bound : t < gap n k) (hm : m < gap n k - t) :
    k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n] :=
  first_jump_easy n k h t m hn hkh ht_bound hm

/-- **Subtractive window**: all shifts 0 ≤ j ≤ t preserve equivalence (shift δ = −j). -/
theorem full_window_subtractive (n k h t j : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht_pos : 0 < t) (ht_bound : t < gap n k) (hj : j ≤ t) :
    k ^ n + t - j ≡ₒ h ^ n + t - j [Aod n] :=
  subtraction_equiv_until_zero n k h t j hn hkh ht_pos ht_bound hj

/-- **Additive break**: at the right boundary δ = gap(n,k)−t the equivalence breaks. -/
theorem full_window_additive_break (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht_bound : t < gap n k) :
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ h ^ n + t + (gap n k - t) [Aod n]) :=
  first_jump_at_mstar n k h t hn hkh ht_bound

/-- **Subtractive break**: at the left boundary δ = −(t+1) the equivalence breaks. -/
theorem full_window_subtractive_break (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (hk : 0 < k) (ht_pos : 0 < t) (ht_bound : t < gap n k) :
    ¬ (k ^ n + t - (t + 1) ≡ₒ h ^ n + t - (t + 1) [Aod n]) :=
  subtraction_breaks_after_zero n k h t hn hkh hk ht_pos ht_bound

/-- **Chapter Tiling Theorem**: the complete set of equivalence-preserving shifts for the
    pair (k^n+t, h^n+t) consists of exactly gap(n,k) consecutive integer shifts,
    split symmetrically around 0 by the local coordinate t:

      [−t, gap(n,k)−t−1]   (subtractive: t+1 shifts; additive: gap(n,k)−t shifts;
                             overlap at 0; total distinct = gap(n,k))

    Both boundary shifts −(t+1) and gap(n,k)−t are break points.
    The tiling equation t + (gap(n,k)−t) = gap(n,k) confirms the count. -/
theorem chapter_tiling_theorem (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (hk : 0 < k) (ht_pos : 0 < t) (ht_bound : t < gap n k) :
    -- Additive half: [0, gap−t)
    (∀ m < gap n k - t, k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n]) ∧
    -- Subtractive half: [0, t]  (shift = −j)
    (∀ j ≤ t, k ^ n + t - j ≡ₒ h ^ n + t - j [Aod n]) ∧
    -- Right break
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ h ^ n + t + (gap n k - t) [Aod n]) ∧
    -- Left break
    ¬ (k ^ n + t - (t + 1) ≡ₒ h ^ n + t - (t + 1) [Aod n]) ∧
    -- Tiling equation: the two halves cover gap(n,k) distinct shifts
    t + (gap n k - t) = gap n k :=
  ⟨fun m hm => full_window_additive n k h t m hn hkh ht_pos ht_bound hm,
   fun j hj => full_window_subtractive n k h t j hn hkh ht_pos ht_bound hj,
   full_window_additive_break n k h t hn hkh ht_bound,
   full_window_subtractive_break n k h t hn hkh hk ht_pos ht_bound,
   by omega⟩

end ChapterTiling

/-!
## §10b  The Obstruction κ and the Twisted Fiber Translation T̃_j

### Overview

The additive translation τ_j preserves `aodEquiv` unconditionally, but does **not** preserve
`twistedAodEquiv` across chapters for n ≥ 3.  The failure is controlled by an explicit,
computable quantity — the **obstruction** `obstruction n k h j` — whose vanishing characterises
n = 2 exactly.

This section:

1. Defines `obstruction n k h j := subtractionShift n h (h+j) - subtractionShift n k (k+j)`.
2. Proves the **drift lemma**: if `a = k^n+t` and `b = h^n+s` are twisted-equivalent, then
   `r̃_n(τ_j(b)) = r̃_n(τ_j(a)) + obstruction n k h j`.
3. Defines the **twisted fiber coordinate** `twistedFiberCoord n k h j t := t - subtractionShift n (k+j) (h+j)`,
   the corrected right-leg coordinate that restores twisted equivalence.
4. Proves **twisted preservation**: `twistedFiberTranslation_preserves` (the corrected pair is
   twisted-equivalent at the target chapters).
5. Proves the **semigroup law**: `twistedFiberTranslation_comp`.
6. Proves the **obstruction vanishing theorem**: `obstruction_zero_iff_n2`.

### Connection to §15 (FirstOccurrence)

The domain condition `subtractionShift n (k+j) (h+j) ≤ t` for `twistedFiberCoord` is
equivalent to `minCap n t hn ≤ k+j` — i.e., the first-occurrence chapter of the local
coordinate `t` is at most `k+j`. This is the bridge between the twisted fiber structure
and the first occurrence theory in `FirstOccurrence.lean`.
-/

section TwistedFiberTranslation

/-- The obstruction to τ_j preserving `twistedAodEquiv`.

    For a twisted-equivalent pair `(k^n+t, h^n+s)` with `k < h`, after applying τ_j
    the twisted values drift apart by exactly this amount.

    Equals the mixed second finite difference `Δ_j Δ_{h-k} [gap(n,·)](k-1)`,
    which vanishes iff `gap(n,·)` is affine, iff n = 2. -/
def obstruction (n k h j : ℕ) : ℕ :=
  subtractionShift n h (h + j) - subtractionShift n k (k + j)

/-- The obstruction equals the gap-difference formula. -/
lemma obstruction_eq_gap (n k h j : ℕ) (_hkh : k ≤ h)
    (_hge : subtractionShift n k (k + j) ≤ subtractionShift n h (h + j)) :
    obstruction n k h j =
      (gap n (h + j - 1) - gap n (h - 1)) - (gap n (k + j - 1) - gap n (k - 1)) := by
  simp only [obstruction, subtractionShift]

/-- **Drift lemma**: if `a = k^n+t` and `b = h^n+s` are twisted-equivalent (k < h),
    then applying τ_j produces a drift of exactly `obstruction n k h j` between their
    twisted values. -/
lemma tauJ_twistedRadRem_drift (n k h j t s : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (hk : 0 < k) (ht : t < gap n k) (hs : s < gap n h)
    (htwist : twistedAodEquiv n (k ^ n + t) (h ^ n + s))
    (hge : subtractionShift n k (k + j) ≤ subtractionShift n h (h + j)) :
    twistedRadRem n (tauJ n j (h ^ n + s)) =
    twistedRadRem n (tauJ n j (k ^ n + t)) + obstruction n k h j := by
  have hnn : n ≠ 0 := by omega
  -- Unpack twisted equivalence to get s = t - σ(n,k,h)
  simp only [twistedAodEquiv, twistedRadRem_base_add n k t (by omega) ht,
             twistedRadRem_base_add n h s (by omega) hs] at htwist
  -- htwist : t + gap n (k-1) = s + gap n (h-1), so s = t + gap n (k-1) - gap n (h-1)
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  have hsj : s < gap n (h + j) := gap_lt_of_add n h j s hn hs
  rw [tauJ_base_add n k j t hnn ht, tauJ_base_add n h j s hnn hs]
  rw [twistedRadRem_base_add n (k + j) t (by omega) htj,
      twistedRadRem_base_add n (h + j) s (by omega) hsj]
  simp only [obstruction, subtractionShift] at hge ⊢
  have hm1 : gap n (k - 1) ≤ gap n (k + j - 1) := gap_le_of_le n (k - 1) (k + j - 1) hn (by omega)
  have hm2 : gap n (h - 1) ≤ gap n (h + j - 1) := gap_le_of_le n (h - 1) (h + j - 1) hn (by omega)
  have hm3 : gap n (k - 1) ≤ gap n (h - 1) := gap_le_of_le n (k - 1) (h - 1) hn (by omega)
  omega

/-- The corrected right-leg coordinate for the twisted fiber translation.

    Given a source pair `(k^n+t, h^n+s)` with `s = t - σ(n,k,h)`, the twisted fiber
    translation maps the right leg to chapter `h+j` with coordinate `s'' = t - σ(n,k+j,h+j)`.

    The domain condition `subtractionShift n (k+j) (h+j) ≤ t` ensures `s'' ∈ ℕ` (no underflow)
    and that the target pair is twisted-equivalent. -/
def twistedFiberCoord (n k h j t : ℕ) : ℕ :=
  t - subtractionShift n (k + j) (h + j)

/-- The target coordinate fits in chapter `h+j`. -/
lemma twistedFiberCoord_lt_gap (n k h j t : ℕ) (hn : 2 ≤ n) (hkh : k < h) (_hk : 0 < k)
    (ht : t < gap n k)
    (hdomain : subtractionShift n (k + j) (h + j) ≤ t) :
    twistedFiberCoord n k h j t < gap n (h + j) := by
  simp only [twistedFiberCoord]
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  have hle : gap n (k + j) ≤ gap n (h + j) :=
    gap_le_of_le n (k + j) (h + j) hn (by omega)
  omega

/-- **Twisted preservation theorem**: the corrected pair `((k+j)^n+t, (h+j)^n+s'')` is
    twisted-equivalent.

    This is the core correctness theorem for the twisted fiber translation T̃_j. -/
theorem twistedFiberTranslation_preserves (n k h j t : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (hk : 0 < k) (ht : t < gap n k)
    (hdomain : subtractionShift n (k + j) (h + j) ≤ t) :
    twistedAodEquiv n ((k + j) ^ n + t) ((h + j) ^ n + twistedFiberCoord n k h j t) := by
  have hnn : n ≠ 0 := by omega
  have htj : t < gap n (k + j) := gap_lt_of_add n k j t hn ht
  have hs'' := twistedFiberCoord_lt_gap n k h j t hn hkh hk ht hdomain
  simp only [twistedAodEquiv,
             twistedRadRem_base_add n (k + j) t hnn htj,
             twistedRadRem_base_add n (h + j) _ hnn hs'']
  simp only [twistedFiberCoord, subtractionShift] at hdomain ⊢
  have hgap : gap n (k + j - 1) ≤ gap n (h + j - 1) :=
    gap_le_of_le n (k + j - 1) (h + j - 1) hn (by omega)
  omega

/-- **Semigroup law** for twisted fiber translations:
    applying T̃_j then T̃_i equals T̃_{i+j} on the intersection domain. -/
theorem twistedFiberTranslation_comp (n k h i j t : ℕ) (_hn : 2 ≤ n) (hkh : k < h)
    (hk : 0 < k) (_ht : t < gap n k)
    (_hdomain_ij : subtractionShift n (k + i + j) (h + i + j) ≤ t) :
    twistedFiberCoord n (k + j) (h + j) i t = twistedFiberCoord n k h (i + j) t := by
  simp only [twistedFiberCoord, subtractionShift]
  have e1 : (h + j) + i - 1 = h + (i + j) - 1 := by omega
  have e2 : (k + j) + i - 1 = k + (i + j) - 1 := by omega
  rw [e1, e2]

/-- For n = 2, the chapter gap is the linear function `gap 2 m = 2*m + 1`. -/
private lemma gap_two (m : ℕ) : gap 2 m = 2 * m + 1 := by
  have key : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
  simp only [gap]
  omega

/-- **Obstruction vanishing theorem** (easy direction: n=2 implies zero obstruction).

    For n = 2 and k, h ≥ 1: `gap(2, m) = 2m + 1` is affine, so `Δ_j gap(2, m) = 2j` is
    constant and the mixed second difference is zero.

    Requires `0 < k` and `0 < h` so that `h - 1` and `k - 1` are correct in ℕ arithmetic
    (without these, `subtractionShift 2 0 j = 2*(j-1) ≠ 2*j` and the obstruction is nonzero).

    -- Example witness showing necessity: obstruction 2 0 1 1 = 2 ≠ 0. -/
theorem obstruction_zero_of_n2 (k h j : ℕ) (hk : 0 < k) (hh : 0 < h) :
    obstruction 2 k h j = 0 := by
  -- obstruction 2 k h j = subtractionShift 2 h (h+j) - subtractionShift 2 k (k+j)
  -- For n=2 and a≥1: subtractionShift 2 a (a+j) = gap 2 (a+j-1) - gap 2 (a-1)
  --                                               = (2*(a+j-1)+1) - (2*(a-1)+1) = 2*j.
  -- So both shifts equal 2*j, and the monus obstruction = 2*j - 2*j = 0.
  simp only [obstruction, subtractionShift, gap_two]
  omega

/-- **Auxiliary**: 3^n + 3 > 3 * 2^n for all n ≥ 3.

    Proof by induction starting at n = 3.
    Base: 27 + 3 = 30 > 24 = 3 * 8. ✓
    Step: assuming 3^n + 3 > 3 * 2^n,
      3^(n+1) + 3 = 3 * 3^n + 3
                  = 3 * (3^n + 3) - 6
                  ≥ 3 * (3 * 2^n + 1) - 6   (by IH, since 3^n + 3 > 3 * 2^n means 3^n + 3 ≥ 3*2^n + 1)
                  = 9 * 2^n + 3 - 6          (simplified)
                  = 9 * 2^n - 3
                  > 6 * 2^n                  (since 3 * 2^n ≥ 24 > 3)
                  = 3 * 2^(n+1). ✓ -/
private lemma three_pow_add_three_gt (n : ℕ) (hn : 3 ≤ n) : 3 * 2 ^ n < 3 ^ n + 3 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hn with hm3eq | hm
    · -- Base case: m+1 = 3, i.e., m = 2
      have : m = 2 := by omega
      subst this
      norm_num
    · -- Inductive step: m+1 ≥ 4, so m ≥ 3
      have hm3 : 3 ≤ m := by omega
      have ih' := ih hm3
      -- 3 * 2^(m+1) = 6 * 2^m
      -- 3^(m+1) + 3 = 3 * 3^m + 3
      -- Need: 6 * 2^m < 3 * 3^m + 3
      -- From IH: 3 * 2^m < 3^m + 3, so 6 * 2^m < 2 * 3^m + 6
      -- Also 2 * 3^m + 6 ≤ 3 * 3^m + 3 iff 3 ≤ 3^m, true since m ≥ 3.
      have h3m : 3 ≤ 3 ^ m := by
        calc 3 = 3 ^ 1 := by norm_num
             _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      have pow_succ_3 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      have pow_succ_2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [pow_succ_3, pow_succ_2]
      nlinarith

/-- **Obstruction vanishing theorem** (hard direction: n ≥ 3 implies non-vanishing).

    For n ≥ 3: `gap(n, ·)` has degree n-1 ≥ 2 in the chapter index, so its mixed
    second finite difference `κ(n,k,h,j) = Δ_j Δ_{h-k} [gap(n,·)](k-1)` is a
    nonzero polynomial for k < h and j ≥ 1. The witness k=1, h=2, j=1 gives
    `κ(n,1,2,1) = 3^n - 3·2^n + 3`, which is positive for n ≥ 3.

    Proof: `f(n) = 3^n - 3·2^n + 3` satisfies f(3) = 6 > 0 and
    `f(n+1) = 3·f(n) + 3·(3^n - 2^n) > 0` inductively for n ≥ 3.
    Uses `three_pow_add_three_gt` which proves 3*2^n < 3^n + 3 by induction. -/
theorem obstruction_nonzero_of_n_ge3 (n : ℕ) (hn : 3 ≤ n) :
    obstruction n 1 2 1 > 0 := by
  -- Unfold to: subtractionShift n 2 3 - subtractionShift n 1 2 > 0
  -- i.e., subtractionShift n 1 2 < subtractionShift n 2 3
  -- i.e., (gap n 1 - gap n 0) < (gap n 2 - gap n 1)
  -- i.e., (2^n - 1) < (3^n - 2^n) - (2^n - 1)  ... after arithmetic
  -- Equivalently: 3 * 2^n < 3^n + 3, proved by three_pow_add_three_gt.
  have hkey : 3 * 2 ^ n < 3 ^ n + 3 := three_pow_add_three_gt n hn
  -- Establish ℕ-level ordering facts needed for zify conditions
  have h2n_pos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have h3n_pos : 0 < 3 ^ n := pow_pos (by norm_num) n
  have h1n : (1 : ℕ) ^ n = 1 := one_pow n
  have h0n : (0 : ℕ) ^ n = 0 := Nat.zero_pow (by omega)
  have h2n_ge1 : 1 ≤ 2 ^ n := h2n_pos
  have h3n_ge2n : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  -- Establish the intermediate ℕ-inequality facts needed for the monus chain
  -- σ(n,1,2) = gap n 1 - gap n 0 = (2^n - 1) - 1 = 2^n - 2
  -- σ(n,2,3) = gap n 2 - gap n 1 = (3^n - 2^n) - (2^n - 1) = 3^n - 2*2^n + 1
  -- obstruction = σ(n,2,3) - σ(n,1,2) = 3^n - 3*2^n + 3
  -- All intermediate values are well-defined (no underflow) since 2^n ≥ 2 and 3^n ≥ 2*2^n + 1
  have h2n_ge2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3n_ge_2t2n : 2 * 2 ^ n ≤ 3 ^ n := by
    -- 3^n ≥ 2*2^n follows from hkey: 3*2^n < 3^n + 3, so 3^n > 3*2^n - 3 ≥ 2*2^n for 2^n ≥ 3
    nlinarith [Nat.pow_le_pow_left (show 2 ≤ 3 by norm_num) n]
  -- Now unfold and resolve the monus steps directly
  simp only [obstruction, subtractionShift, gap, h1n, h0n]
  -- After norm_num simplification of constant bases (0,1,2,3):
  norm_num
  -- Remaining goal is in ℕ arithmetic about 2^n and 3^n
  omega

-- κ(n,k,h,j) = 0 for all k<,h j≥1 iff n=2
/-- **Obstruction vanishing characterisation**
    Combines the two directions above.
-/
theorem obstruction_zero_iff_n2 (n : ℕ) (hn : 2 ≤ n) :
    (∀ k h j : ℕ, 0 < k → k < h → 0 < j → obstruction n k h j = 0) ↔ n = 2 := by
  constructor
  · intro hall
    by_contra hne
    have hge3 : 3 ≤ n := by omega
    have := obstruction_nonzero_of_n_ge3 n hge3
    have := hall 1 2 1 (by omega) (by omega) (by omega)
    omega
  · intro hn2
    subst hn2
    intro k h j hk hkh _
    exact obstruction_zero_of_n2 k h j hk (by omega)

end TwistedFiberTranslation

/-!
## §11  The σ-Shift Functor and the Two Functors of the Translation Arc

### Overview

The translation arc has two natural functors on chapter fibers, both acting on the preorder
(ℕ, ≤) of chapter indices:

**Functor I (additive) — `chapterFiberFunctor`**:
  `k ↦ ChapterFiber n k`,  `(k ≤ h) ↦ φ_{k,h} = τ_{h-k}`.
  *Total*: defined on all elements. Preserves the local coordinate `r_n(a) = t`.
  [Proved: `fiberAction_id`, `fiberAction_comp`, `chapterFiberFunctor`]

**Functor II (subtractive) — `sigmaShiftMap`**:
  `k ↦ ChapterFiber n k`,  `(k ≤ h) ↦ φ_{k→h}` = shift local coordinate down by σ(n,k,h).
  *Partial*: defined only on the sub-fiber `{k^n+t : t ≥ σ(n,k,h)}`.
  Preserves `aodEquiv` and `twistedAodEquiv` on its domain.
  [Proved below]

The key structural facts:
- σ satisfies a **cocycle law** `σ(n,k,m) + σ(n,m,h) = σ(n,k,h)` — the composition law
  for σ-shifts.
- `twistedRadRem` is the **canonical trivialization** of Functor II: it is constant along
  σ-fibers.
- `twistedAodEquiv` identifies exactly the elements in the same σ-fiber.
- For n ≥ 3, the σ-category (morphisms = σ values) is **strictly finer** than the capitolar
  groupoid (morphisms = h − k).  For n = 2, they are isomorphic (σ(2,k,h) = 2(h−k)).
- The Gauge Impossibility theorem (`aodEquiv_finest_tauJ_invariant`) has a full biconditional
  form: f is τ_j-invariant iff f factors through r_n.
-/

section SigmaShiftFunctor

/-- **σ-cocycle law**: the subtractionShift satisfies the composition identity
    σ(n,k,m) + σ(n,m,h) = σ(n,k,h) for all k ≤ m ≤ h.

    This is the 1-cocycle condition on the preorder (ℕ, ≤): σ is the length
    function of the σ-category, whose morphisms are the σ-values. -/
theorem subtractionShift_cocycle (n k m h : ℕ) (hn : 2 ≤ n) (hkm : k ≤ m) (hmh : m ≤ h) :
    subtractionShift n k m + subtractionShift n m h = subtractionShift n k h := by
  simp only [subtractionShift]
  have h1 : gap n (k - 1) ≤ gap n (m - 1) := gap_le_of_le n (k - 1) (m - 1) hn (by omega)
  have h2 : gap n (m - 1) ≤ gap n (h - 1) := gap_le_of_le n (m - 1) (h - 1) hn (by omega)
  omega

/-- **σ-shift map**: the canonical inter-chapter map that shifts the local coordinate
    down by σ(n,k,h).

    For `a = k^n + t` with `t ≥ σ(n,k,h)`, the σ-shift sends `a` to `h^n + (t - σ)`.
    This is a partial map ℕ ⇀ ℕ; the domain condition is `subtractionShift n k h ≤ t`.

    The fiber theorem `tRR_fiber_mem_iff` characterises exactly when this domain
    condition holds: `k^n+t` has a twisted-equivalent partner in chapter h iff t ≥ σ(n,k,h). -/
def sigmaShiftMap (n k h t : ℕ) : ℕ :=
  h ^ n + (t - subtractionShift n k h)

/-- The σ-shift produces an element in chapter h with local coordinate t - σ. -/
lemma sigmaShiftMap_radRem (n k h t : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) (hkh : k < h)
    (hσ : subtractionShift n k h ≤ t) (ht : t < gap n k) :
    radRem n (sigmaShiftMap n k h t) = t - subtractionShift n k h := by
  have hnn : n ≠ 0 := by omega
  have ht' : t - subtractionShift n k h < gap n h := by
    have : gap n k ≤ gap n h := gap_le_of_le n k h hn (by omega)
    simp only [subtractionShift]
    omega
  simp only [sigmaShiftMap]
  exact radRem_base_add n h _ hnn ht'

/-- **σ-shift preserves aodEquiv** (class-level well-definedness): if a' ≡ₒ k^n+t,
    then σ-shifting a' by the same σ(n,k,h) produces an aodEquiv-equivalent result.

    This says φ_{k→h} is a well-defined map on aodEquiv-classes:
    [t]_n ↦ [t - σ(n,k,h)]_n. -/
theorem sigmaShiftMap_aodEquiv_compat (n k h t : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) (_hkh : k < h)
    (_hσ : subtractionShift n k h ≤ t) (ht : t < gap n k)
    (a' : ℕ) (ha' : a' ≡ₒ k ^ n + t [Aod n]) :
    sigmaShiftMap n k h (radRem n a') ≡ₒ sigmaShiftMap n k h t [Aod n] := by
  have hnn : n ≠ 0 := by omega
  have ht_eq : radRem n (k ^ n + t) = t := radRem_base_add n k t hnn ht
  simp only [aodEquiv, ht_eq] at ha'
  -- ha' : radRem n a' = t
  simp only [aodEquiv, sigmaShiftMap, ha']

/-- **σ-shift composition law**: composing σ-shifts matches the cocycle.

    φ_{m→h}(φ_{k→m}(k^n+t)) = φ_{k→h}(k^n+t), for t ≥ σ(n,k,h). -/
theorem sigmaShiftMap_comp (n k m h t : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) (hkm : k < m)
    (hmh : m < h) (hσ : subtractionShift n k h ≤ t) (_ht : t < gap n k) :
    sigmaShiftMap n m h (t - subtractionShift n k m) = sigmaShiftMap n k h t := by
  simp only [sigmaShiftMap]
  have := subtractionShift_cocycle n k m h hn (by omega) (by omega)
  omega

/-- **Trivialization property**: `twistedRadRem` is constant along σ-fibers.

    For any `a = k^n+t` in the domain of φ_{k→h}, the twisted value is preserved:
    `r̃_n(φ_{k→h}(a)) = r̃_n(a)`.

    This identifies `twistedRadRem` as the canonical trivialization of the σ-functor:
    `twistedAodEquiv` captures exactly the σ-fiber relation. -/
theorem twistedRadRem_sigmaShift_invariant (n k h t : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (hkh : k < h) (hσ : subtractionShift n k h ≤ t) (ht : t < gap n k) :
    twistedRadRem n (sigmaShiftMap n k h t) = twistedRadRem n (k ^ n + t) := by
  have hnn : n ≠ 0 := by omega
  have ht' : t - subtractionShift n k h < gap n h := by
    have : gap n k ≤ gap n h := gap_le_of_le n k h hn (by omega)
    simp only [subtractionShift]; omega
  simp only [sigmaShiftMap,
             twistedRadRem_base_add n h _ hnn ht',
             twistedRadRem_base_add n k t (by omega) ht]
  simp only [subtractionShift] at hσ ⊢
  have h3 : gap n (k - 1) ≤ gap n (h - 1) := gap_le_of_le n (k - 1) (h - 1) hn (by omega)
  omega

/-- **Corollary**: the σ-shift of `k^n+t` is twisted-equivalent to `k^n+t` itself. -/
theorem twistedAodEquiv_sigmaShift (n k h t : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (hkh : k < h) (hσ : subtractionShift n k h ≤ t) (ht : t < gap n k) :
    twistedAodEquiv n (k ^ n + t) (sigmaShiftMap n k h t) :=
  (twistedRadRem_sigmaShift_invariant n k h t hn hk hkh hσ ht).symm

/-- **Full biconditional**: the σ-shift is twisted-equivalent to the source if and only if σ ≤ t.

    When σ > t, the ℕ-monus subtraction `t - σ = 0`, so `sigmaShiftMap n k h t = h^n`.
    Then `twistedRadRem n (h^n) = gap n (h-1)`, while `twistedRadRem n (k^n+t) = t + gap n (k-1)`.
    If σ > t then `gap n (h-1) = σ + gap n (k-1) > t + gap n (k-1)`, so equality fails.

    This is the precise criterion for when a twisted fiber pair exists across chapters k and h:
    the local coordinate t must be large enough to absorb the subtractive shift σ(n,k,h). -/
theorem twistedAodEquiv_sigmaShift_iff (n k h t : ℕ) (hn : 2 ≤ n) (hk : 0 < k)
    (hkh : k < h) (ht : t < gap n k) :
    twistedAodEquiv n (k ^ n + t) (sigmaShiftMap n k h t) ↔
    subtractionShift n k h ≤ t := by
  constructor
  · intro htwist
    simp only [twistedAodEquiv, sigmaShiftMap] at htwist
    have hnn : n ≠ 0 := by omega
    rw [twistedRadRem_base_add n k t hnn ht] at htwist
    have ht_sub_lt : t - subtractionShift n k h < gap n h := by
      calc t - subtractionShift n k h ≤ t := Nat.sub_le _ _
        _ < gap n k := ht
        _ ≤ gap n h := gap_le_of_le n k h hn (by omega)
    rw [twistedRadRem_base_add n h _ hnn ht_sub_lt] at htwist
    -- htwist : t + gap n (k-1) = (t - σ) + gap n (h-1)
    simp only [subtractionShift] at htwist ⊢
    have h3 : gap n (k - 1) ≤ gap n (h - 1) := gap_le_of_le n (k - 1) (h - 1) hn (by omega)
    omega
  · intro hσ
    exact twistedAodEquiv_sigmaShift n k h t hn hk hkh hσ ht

/-- **Gauge Impossibility (full biconditional)**: a function f : ℕ → ℕ is invariant
    under every τ_j if and only if f factors through r_n.

    Forward direction: `tauJ_invariant_factors_radRem` (already proved).
    Converse: since `r_n(τ_j(k^n+t)) = r_n(k^n+t)` by `tauJ_radRem_preserved`, any
    function of r_n is automatically τ_j-invariant. -/
theorem tauJ_invariant_iff (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℕ) :
    (∀ j a : ℕ, f (tauJ n j a) = f a) ↔ (∃ g : ℕ → ℕ, ∀ a : ℕ, f a = g (radRem n a)) := by
  constructor
  · intro hinv
    have hfact := tauJ_invariant_factors_radRem n hn f hinv
    -- Construct g via classical choice: for each r, pick any preimage of r under radRem n
    haveI : ∀ r : ℕ, Decidable (∃ a, radRem n a = r) := fun r => Classical.propDecidable _
    refine ⟨fun r => if h : ∃ a, radRem n a = r then f (Classical.choose h) else 0, fun a => ?_⟩
    have hex : ∃ b, radRem n b = radRem n a := ⟨a, rfl⟩
    simp only [dif_pos hex]
    exact hfact a (Classical.choose hex) (Classical.choose_spec hex).symm
  · rintro ⟨g, hg⟩ j a
    rw [hg (tauJ n j a), hg a]
    congr 1
    -- radRem n (tauJ n j a) = radRem n a
    have hle : (irootN n a) ^ n ≤ a := irootN_pow_le n a (by omega)
    have ha : a = (irootN n a) ^ n + radRem n a := by simp [radRem]; omega
    have ht : radRem n a < gap n (irootN n a) := radRem_lt_gap n a (by omega)
    conv_lhs => rw [ha]
    rw [tauJ_radRem_preserved n (irootN n a) j (radRem n a) hn ht,
        radRem_base_add n (irootN n a) (radRem n a) (by omega) ht]

/-- **σ-category is strictly finer than capitolar groupoid for n ≥ 3**.

    For n ≥ 3, there exist pairs (k,h) and (k',h') with h-k = h'-k' but
    σ(n,k,h) ≠ σ(n,k',h'). The σ-category carries strictly more geometric
    information. For n = 2, σ(2,k,h) = 2(h-k), so the two are isomorphic. -/
theorem sigma_category_finer_than_capitolar (n : ℕ) (hn : 3 ≤ n) :
    ∃ k h k' h' : ℕ, k < h ∧ k' < h' ∧ h - k = h' - k' ∧
      subtractionShift n k h ≠ subtractionShift n k' h' := by
  -- Witness: k=1, h=2 vs k'=2, h'=3 (both have difference 1).
  -- obstruction n 1 2 1 = σ(n,2,3) − σ(n,1,2) > 0 (from obstruction_nonzero_of_n_ge3),
  -- so σ(n,1,2) < σ(n,2,3), in particular they are unequal.
  refine ⟨1, 2, 2, 3, by omega, by omega, by omega, ?_⟩
  have hobs : obstruction n 1 2 1 > 0 := obstruction_nonzero_of_n_ge3 n hn
  simp only [obstruction] at hobs
  -- hobs : subtractionShift n 2 3 - subtractionShift n 1 2 > 0 (ℕ monus)
  -- This means subtractionShift n 1 2 < subtractionShift n 2 3
  have hlt : subtractionShift n 1 2 < subtractionShift n 2 3 :=
    Nat.lt_of_sub_pos hobs
  omega

/-- For n = 2, the σ-shift equals 2*(h-k): the σ-category and the capitolar groupoid
    are isomorphic for n = 2. -/
theorem subtractionShift_two (k h : ℕ) (hk : 0 < k) (hh : 0 < h) :
    subtractionShift 2 k h = 2 * (h - k) := by
  simp only [subtractionShift, gap_two]
  -- After unfolding: (2*(h-1)+1) - (2*(k-1)+1) = 2*(h-k) in ℕ monus.
  zify [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk),
        Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hh)]
  omega

/-- **σ-shift lands on a first occurrence iff minCap = h**.

    The σ-shift `sigmaShiftMap n k h t = h^n + (t - σ)` equals `firstOcc n (t - σ) hn`
    (defined as `(minCap n (t-σ) hn)^n + (t - σ)`) if and only if `minCap n (t-σ) hn = h`,
    i.e., the local coordinate `t - σ` first appears exactly in chapter `h`.

    Geometric reading: the σ-shift sends `k^n+t` to a first-occurrence element iff `h` is
    the ground chapter of the shifted coordinate `t - σ`. In general the σ-shift may land in
    a chapter strictly above the first occurrence (when `minCap(t-σ) < h`).

    Requires: `import CampiOperazionistici.FirstOccurrence` for `firstOcc` and `minCap`. -/
theorem sigmaShift_firstOcc_iff (n k h t : ℕ) (hn : 2 ≤ n) (_hk : 0 < k) (_hkh : k < h)
    (_hσ : subtractionShift n k h ≤ t) (_ht : t < gap n k) :
    sigmaShiftMap n k h t = firstOcc n (t - subtractionShift n k h) hn ↔
    minCap n (t - subtractionShift n k h) hn = h := by
  simp only [sigmaShiftMap, firstOcc]
  -- Goal: h ^ n + s = (minCap n s hn) ^ n + s ↔ minCap n s hn = h,  where s = t - σ
  constructor
  · intro heq
    have heq_pow : h ^ n = (minCap n (t - subtractionShift n k h) hn) ^ n := by omega
    -- Derive h = minCap from h^n = (minCap)^n (strict mono in base, n ≥ 2)
    rcases lt_trichotomy h (minCap n (t - subtractionShift n k h) hn) with hlt | heq_m | hgt
    · exact absurd heq_pow (ne_of_lt (Nat.pow_lt_pow_left hlt (by omega)))
    · exact heq_m.symm
    · exact absurd heq_pow.symm (ne_of_lt (Nat.pow_lt_pow_left hgt (by omega)))
  · intro hcap
    rw [hcap]

-- Computational verification: for n=2, k=1, h=2, t=2, σ=2, t-σ=0, minCap 2 0 = 0 ≠ 2.
-- So sigmaShiftMap 2 1 2 2 = 4 = firstOcc 2 0 = 0? No, firstOcc 2 0 = 0, not 4.
-- Correct: minCap 2 0 = 0 ≠ 2, so the iff says they are NOT equal. ✓
#eval sigmaShiftMap 2 1 2 2    -- 4 = 2^2 + (2-2)
#eval firstOcc 2 0 (by omega)  -- 0 = 0^2 + 0

-- For n=2, k=1, h=2, t=3, σ=2, t-σ=1, minCap 2 1 = 1 ≠ 2.
-- sigmaShiftMap = 4+1 = 5; firstOcc 2 1 = 1+1 = 2. Not equal, minCap ≠ h. ✓
#eval sigmaShiftMap 2 1 2 3    -- 5 = 4 + 1
#eval firstOcc 2 1 (by omega)  -- 2 = 1 + 1
#eval minCap 2 1 (by omega)    -- 1 ≠ 2 ✓ (so not a first occurrence)

-- For n=2, k=2, h=3, t=4, σ=2, t-σ=2, minCap 2 2 = 1 ≠ 3.
-- sigmaShiftMap = 9+2 = 11; firstOcc 2 2 = 4+2 = 6. Not equal ✓
#eval sigmaShiftMap 2 2 3 4    -- 11
#eval firstOcc 2 2 (by omega)  -- 6
#eval minCap 2 2 (by omega)    -- 1 ≠ 3 ✓

end SigmaShiftFunctor

/-!
## §12  Universal Tiling Decomposition (Additive Direction)

For $n \geq 2$, $k < h$, $t < \gap(n,k)$, the full additive equivalence set
$\{m : \mathbb{N} \mid r_n(k^n+t+m) = r_n(h^n+t+m)\}$ decomposes as a disjoint union of
tiling windows, one per pair $(k', h')$ satisfying $(h')^n - (k')^n = \Delta := h^n - k^n$.
Each window is $\{m \mid k'^n \leq k^n{+}t{+}m < k'^n + \gap(n,k')\}$, of width $\gap(n,k')$.

This unifies:
- **First Jump Theorem** (`first_jump_easy`, §13): initial window with $(k' = k,\, h' = h)$.
- **Second Window Theorem** (`second_window_of_record`, §13-G.2): higher windows.
- **Chapter Tiling Theorem** (§10): single-pair window structure.

Proof:
- (→) Witnesses $k' := \irootN(n, k^n{+}t{+}m)$, $h' := \irootN(n, h^n{+}t{+}m)$.
  Gap preservation from `aodEquiv_pow_diff_eq`.  Window bounds from irootN specification.
- (←) Given $(k', h')$, set $m' := k^n{+}t{+}m - k'^n$ and apply `radRem_base_add`.

**Note on the subtractive direction**: shifts $m$ going backwards (so $k^n{+}t{+}m < k^n{+}t$)
correspond exactly to `subtractive_reencounter_iff` in `CapitolarTranslations.lean`.
The full bidirectional UTD over $\mathbb{Z}$ is the union of `additive_utd` ($\delta \geq 0$)
and the subtractive analogue already in §6b of that file.
-/

section UTD

/-- **Additive Universal Tiling Decomposition.**

    A natural shift $m$ preserves $r_n(k^n{+}t{+}m) = r_n(h^n{+}t{+}m)$ if and only if
    $k^n{+}t{+}m$ lies in the tiling window of some pair $(k',h')$ with the same power gap
    $(h')^n - (k')^n = h^n - k^n$.

    The canonical witnesses are the chapter indices
    $k' = \irootN(n,\, k^n{+}t{+}m)$ and $h' = \irootN(n,\, h^n{+}t{+}m)$. -/
theorem additive_utd (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (_ht_bound : t < gap n k) :
    radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m) ↔
    ∃ k' h' : ℕ, k' < h' ∧
      (h' : ℤ) ^ n - (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n ∧
      k' ^ n ≤ k ^ n + t + m ∧ k ^ n + t + m < k' ^ n + gap n k' := by
  have hnn : n ≠ 0 := by omega
  constructor
  · -- Direction →: extract witnesses from the irootN of each side
    intro heq
    set k' := irootN n (k ^ n + t + m) with hk'_def
    set h' := irootN n (h ^ n + t + m) with hh'_def
    -- Gap preservation in ℤ, directly from aodEquiv_pow_diff_eq
    have hdiff : (h' : ℤ) ^ n - (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n := by
      have raw := aodEquiv_pow_diff_eq n (k ^ n + t + m) (h ^ n + t + m) hnn heq
      push_cast at raw ⊢; linarith
    -- k' < h': the gap Δ = h^n − k^n is positive, so (h')^n > (k')^n
    have hk'h' : k' < h' := by
      by_contra hle; push_neg at hle
      have hpow : (h' : ℤ) ^ n ≤ (k' : ℤ) ^ n :=
        by exact_mod_cast Nat.pow_le_pow_left hle n
      have hΔ_pos : (k : ℤ) ^ n < (h : ℤ) ^ n :=
        by exact_mod_cast Nat.pow_lt_pow_left hkh hnn
      linarith [hdiff]
    -- Upper window bound: from irootN_lt_succ_pow + succ_pow_eq_add_gap
    have hhi : k ^ n + t + m < k' ^ n + gap n k' := by
      have := irootN_lt_succ_pow n (k ^ n + t + m) hnn
      rw [succ_pow_eq_add_gap n k' hnn] at this; exact this
    exact ⟨k', h', hk'h', hdiff, irootN_pow_le n (k ^ n + t + m) hnn, hhi⟩
  · -- Direction ←: given witnesses (k', h'), reduce to radRem_base_add on both sides
    rintro ⟨k', h', hk'h', hΔ, hlo, hhi⟩
    -- Lift the ℤ gap equality to ℕ (non-underflow guards available)
    have hkn_le  : k  ^ n ≤ h  ^ n := Nat.pow_le_pow_left (Nat.le_of_lt hkh)  n
    have hk'n_le : k' ^ n ≤ h' ^ n := Nat.pow_le_pow_left (Nat.le_of_lt hk'h') n
    have hΔ_nat  : h' ^ n - k' ^ n = h ^ n - k ^ n := by
      zify [hk'n_le, hkn_le]; exact_mod_cast hΔ
    -- Local coordinate m' = (k^n+t+m) − k'^n, bounded by gap n k'
    have hm'_lt  : k ^ n + t + m - k' ^ n < gap n k' := by omega
    -- Rewrite both sides as (base)^n + m' and apply radRem_base_add
    have ha : k ^ n + t + m = k' ^ n + (k ^ n + t + m - k' ^ n) := by omega
    have hb : h ^ n + t + m = h' ^ n + (k ^ n + t + m - k' ^ n) := by omega
    rw [ha, hb,
        radRem_base_add n k' _ hnn hm'_lt,
        radRem_base_add n h' _ hnn
          (Nat.lt_of_lt_of_le hm'_lt (gap_le_of_lt n k' h' hn hk'h'))]

/-- **Corollary: First Jump as the initial tiling window.**

    The window $\{m \mid m < \gap(n,k) - t\}$ of `first_jump_easy` is the special case of
    `additive_utd` with witnesses $(k' = k,\, h' = h)$.  The UTD thus subsumes §13. -/
theorem additive_utd_first_jump (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht_bound : t < gap n k) (hm : m < gap n k - t) :
    radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m) :=
  (additive_utd n k h t m hn hkh ht_bound).mpr
    ⟨k, h, hkh, rfl, by omega, by omega⟩

/-- **Negative part of the initial window.**

    For $1 \leq m \leq t$, both sides stay in their original chapters
    (local coordinate $t - m < \gap(n,k)$), so they remain equivalent.
    This is the $\delta \in [-t, -1]$ slice of the initial tiling window $W(k, t)$. -/
theorem subtractive_initial_equiv (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht : t < gap n k) (hm_pos : 1 ≤ m) (hm_hi : m ≤ t) :
    radRem n (k ^ n + t - m) = radRem n (h ^ n + t - m) := by
  have hnn : n ≠ 0 := by omega
  have hm' : t - m < gap n k := by omega
  rw [show k ^ n + t - m = k ^ n + (t - m) from by omega,
      show h ^ n + t - m = h ^ n + (t - m) from by omega,
      radRem_base_add n k _ hnn hm',
      radRem_base_add n h _ hnn (Nat.lt_of_lt_of_le hm' (gap_le_of_lt n k h hn hkh))]

/-- **Subtractive Universal Tiling Decomposition.**

    For deep subtractive shifts ($m > t$), the pair goes below chapter $k$.
    Equivalence holds iff $k^n{+}t{-}m$ lies in the tiling window of some $(k',h')$
    with $(h')^n - (k')^n = \Delta$ and $k' < k$.

    This is a restatement of `subtractive_reencounter_iff` in the uniform UTD window form,
    making the subtractive direction parallel to `additive_utd`. -/
theorem subtractive_utd (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht : t < gap n k) (htm : t < m) (hma : m < k ^ n + t) :
    radRem n (k ^ n + t - m) = radRem n (h ^ n + t - m) ↔
    ∃ k' h' : ℕ, k' < h' ∧
      (h' : ℤ) ^ n - (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n ∧
      k' ^ n ≤ k ^ n + t - m ∧ k ^ n + t - m < k' ^ n + gap n k' := by
  have hnn : n ≠ 0 := by omega
  rw [subtractive_reencounter_iff n k h t m hn hkh ht htm hma]
  constructor
  · rintro ⟨kpp, hpp, hkpp_lt_k, hδ, hm_start, hm_end⟩
    -- kpp < hpp: from hδ and k < h giving h^n > k^n
    have hkpp_hpp : kpp < hpp := by
      by_contra hle; push_neg at hle
      have hpow : hpp ^ n ≤ kpp ^ n := Nat.pow_le_pow_left hle n
      have hΔ_pos : k ^ n < h ^ n := Nat.pow_lt_pow_left hkh hnn
      omega
    -- Lift gap equality to ℤ: hpp^n + k^n = kpp^n + h^n → (hpp:ℤ)^n - kpp^n = h^n - k^n
    have hΔ_int : (hpp : ℤ) ^ n - (kpp : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n := by
      have : (hpp : ℤ) ^ n + (k : ℤ) ^ n = (kpp : ℤ) ^ n + (h : ℤ) ^ n :=
        by exact_mod_cast hδ
      linarith
    -- Upper bound: k^n+t-m < kpp^n+gap(n,kpp) from hm_start
    have hhi : k ^ n + t - m < kpp ^ n + gap n kpp := by
      have := succ_pow_eq_add_gap n kpp hnn; omega
    exact ⟨kpp, hpp, hkpp_hpp, hΔ_int, by omega, hhi⟩
  · rintro ⟨k', h', hk'h', hΔ, hlo, hhi⟩
    -- k' < k: from k'^n ≤ k^n+t-m < k^n (since m > t)
    have hk'_lt_k : k' < k := by
      by_contra hle; push_neg at hle
      exact absurd (Nat.pow_le_pow_left hle n) (by omega)
    -- ℤ gap back to ℕ addition form: h'^n + k^n = k'^n + h^n
    have hδ_nat : h' ^ n + k ^ n = k' ^ n + h ^ n := by
      have : (h' : ℤ) ^ n + (k : ℤ) ^ n = (k' : ℤ) ^ n + (h : ℤ) ^ n := by linarith [hΔ]
      exact_mod_cast this
    -- Upper bound: k^n+t+1 ≤ m+(k'+1)^n from hhi
    have hm_start : k ^ n + t + 1 ≤ m + (k' + 1) ^ n := by
      have := succ_pow_eq_add_gap n k' hnn; omega
    exact ⟨k', h', hk'_lt_k, hδ_nat, hm_start, by omega⟩

/-- **Tiling windows are disjoint.**

    The chapter intervals $[k_1^n,\, (k_1{+}1)^n)$ and $[k_2^n,\, (k_2{+}1)^n)$ for $k_1 < k_2$
    are disjoint: the first ends at $(k_1{+}1)^n \leq k_2^n$.

    This is the key structural lemma for the counting corollary: the windows in any tiling
    decomposition are non-overlapping, so their cardinalities sum without double-counting. -/
theorem utd_windows_disjoint (n k₁ k₂ : ℕ) (hn : 2 ≤ n) (hlt : k₁ < k₂) :
    k₁ ^ n + gap n k₁ ≤ k₂ ^ n := by
  have hnn : n ≠ 0 := by omega
  rw [← succ_pow_eq_add_gap n k₁ hnn]
  exact Nat.pow_le_pow_left (by omega) n

end UTD

end CampiOperazionistici
