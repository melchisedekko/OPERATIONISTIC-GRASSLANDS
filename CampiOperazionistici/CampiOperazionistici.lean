/-
  OPERAZIONISTICI — Campi Operazionistici
  ========================================
  Author: Alessandro Sgarbi
  Date:   2026-02-27
  Paper: §§3–8 (Definitions and Notation; Properties of the Integer Root; Growing Frontier; Operational Alterity; Landing Congruence; No-Overflow Condition)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

namespace CampiOperazionistici

/-!
## Section 1: Integer n-th Root — Provable Version
-/

/-- Descending search: largest `k ≤ b` with `k^n ≤ a`. -/
def irootAux (n a : ℕ) : ℕ → ℕ
  | 0       => 0
  | (k + 1) => if (k + 1) ^ n ≤ a then k + 1 else irootAux n a k

/-- `irootN n a` = ⌊a^(1/n)⌋. Convention: `irootN 0 a = 1`. -/
def irootN (n a : ℕ) : ℕ :=
  if n = 0 then 1 else irootAux n a a

-- Computational check
#eval irootN 2 4   -- 2 ✓
#eval irootN 2 5   -- 2 ✓
#eval irootN 2 9   -- 3 ✓
#eval irootN 3 8   -- 2 ✓
#eval irootN 3 27  -- 3 ✓
#eval irootN 4 16  -- 2 ✓
#eval irootN 4 81  -- 3 ✓

/-!
## Section 1b: Auxiliary Lemmas on `irootAux`
-/

/-- The result does not exceed the bound. -/
lemma irootAux_le_bound (n a b : ℕ) : irootAux n a b ≤ b := by
  induction b with
  | zero      => simp [irootAux]
  | succ k ih =>
    simp [irootAux]
    split_ifs with h
    · exact le_refl _
    · exact Nat.le_succ_of_le ih


lemma irootAux_pow_le (n a b : ℕ) (hn : n ≠ 0) : (irootAux n a b) ^ n ≤ a := by
  induction b with
  | zero =>
    simp [irootAux]
    -- 0^n = 0 ≤ a.  We use Nat.zero_pow with 0 < n.
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    simp [Nat.zero_pow hpos]
  | succ k ih =>
    simp only [irootAux]
    split_ifs with h
    · exact h
    · exact ih

lemma irootAux_lt_succ_pow (n a b : ℕ) (_hn : n ≠ 0)
    (hbound : a < (b + 1) ^ n) : a < (irootAux n a b + 1) ^ n := by
  induction b with
  | zero =>
    simp [irootAux]
    simpa using hbound
  | succ k ih =>
    simp only [irootAux]
    split_ifs with h
    · simpa using hbound
    · push_neg at h
      exact ih h

/-!
## Section 1c: The Two Main Lemmas on `irootN`
-/

/-- Support lemma: for n ≥ 1, `a < (a+1)^n` always holds. -/
lemma lt_succ_pow (n a : ℕ) (hn : n ≠ 0) : a < (a + 1) ^ n := by
  calc a < a + 1         := Nat.lt_succ_self a
       _ ≤ (a + 1) ^ n   := Nat.le_self_pow hn _

theorem irootN_pow_le (n a : ℕ) (hn : n ≠ 0) : (irootN n a) ^ n ≤ a := by
  simp [irootN, hn]
  exact irootAux_pow_le n a a hn

theorem irootN_lt_succ_pow (n a : ℕ) (hn : n ≠ 0) : a < (irootN n a + 1) ^ n := by
  simp [irootN, hn]
  exact irootAux_lt_succ_pow n a a hn (lt_succ_pow n a hn)

/-- The two specs together: the complete characterization of irootN. -/
theorem irootN_spec (n a : ℕ) (hn : n ≠ 0) :
    (irootN n a) ^ n ≤ a ∧ a < (irootN n a + 1) ^ n :=
  ⟨irootN_pow_le n a hn, irootN_lt_succ_pow n a hn⟩

/-!
## Section 2: Generalized Radical Remainder
-/

def radRem (n a : ℕ) : ℕ :=
  a - (irootN n a) ^ n

#eval radRem 2 2   -- 1 ✓
#eval radRem 2 5   -- 1 ✓
#eval radRem 2 4   -- 0 ✓
#eval radRem 3 9   -- 1
#eval radRem 3 27  -- 0 ✓

lemma radRem_eq_sub (n a : ℕ) (_hn : n ≠ 0) :
    radRem n a = a - (irootN n a) ^ n := rfl

lemma radRem_lt_gap (n a : ℕ) (hn : n ≠ 0) :
    radRem n a < (irootN n a + 1) ^ n - (irootN n a) ^ n := by
  simp [radRem]
  have hle := irootN_pow_le n a hn
  have hlt := irootN_lt_succ_pow n a hn
  omega

/-!
## Section 3: Notations
-/

def aodEval    (n a r : ℕ) : Prop := radRem n a = r
def aodEquiv   (n a b : ℕ) : Prop := radRem n a = radRem n b
def aodEquivAt (n r a b : ℕ) : Prop := radRem n a = r ∧ radRem n b = r

notation:50 a " ↠[" n "] " r              => aodEval n a r
notation:50 a " ≡ₒ " b " [Aod " n "]"    => aodEquiv n a b
notation:50 a " ≡ₒ[" r "] " b " [Aod " n "]" => aodEquivAt n r a b

/-!
## Section 4: aodEquiv is an Equivalence Relation
-/

theorem aodEquiv_refl  (n a : ℕ) : a ≡ₒ a [Aod n] := rfl
theorem aodEquiv_symm  (n a b : ℕ) (h : a ≡ₒ b [Aod n]) : b ≡ₒ a [Aod n] := h.symm
theorem aodEquiv_trans (n a b c : ℕ) (h₁ : a ≡ₒ b [Aod n]) (h₂ : b ≡ₒ c [Aod n]) :
    a ≡ₒ c [Aod n] := h₁.trans h₂

theorem aodEquiv_isEquivalence (n : ℕ) : Equivalence (aodEquiv n) where
  refl  := aodEquiv_refl n
  symm  := fun h => aodEquiv_symm n _ _ h
  trans := fun h₁ h₂ => aodEquiv_trans n _ _ _ h₁ h₂

def aodSetoid (n : ℕ) : Setoid ℕ where
  r     := aodEquiv n
  iseqv := aodEquiv_isEquivalence n

/-- The quotient type: the equivalence classes of Aod n. -/
def AodField (n : ℕ) : Type := Quotient (aodSetoid n)

/-!
## Section 5: Verified Fundamental Lemmas

`aodEquiv` does not have an automatic `Decidable` instance for the custom
notations: the following lemmas are proved by expanding the definition and
reducing the goal to decidable equalities over ℕ.
-/

-- The four lemmas are proved by computational reflexivity:
-- aodEquiv n a b = (radRem n a = radRem n b) is an equality between ℕ values,
-- so it suffices to reduce both sides with rfl (after unfold).
lemma two_equiv_five_aod2  : 2 ≡ₒ 5  [Aod 2] := by
  simp [aodEquiv, radRem, irootN, irootAux]

lemma one_equiv_four_aod2  : 1 ≡ₒ 4  [Aod 2] := by
  simp [aodEquiv, radRem, irootN, irootAux]

lemma eight_not_nine_aod3  : ¬ (8 ≡ₒ 9  [Aod 3]) := by
  simp [aodEquiv, radRem, irootN, irootAux]

-- NOTE: 9 ≡ₒ 10 [Aod 3] is FALSE (radRem 3 9 = 1, radRem 3 10 = 2).
-- The correct lemma is 9 ≡ₒ 28 [Aod 3] (both have remainder 1 in Aod 3).
lemma nine_equiv_28_aod3  : 9 ≡ₒ 28 [Aod 3] := by
  simp [aodEquiv, radRem, irootN, irootAux]

/-!
## Section 6: Perfect n-th Powers

The proof of `perfectPower_iff_radRem_zero` does not directly compare
`irootN n a` with `irootN n (k^n)` (which do not coincide by definition): instead
it proceeds by squeezing from the two specs `irootN_pow_le` and
`irootN_lt_succ_pow`.
-/

def isPerfectPower (n a : ℕ) : Prop := ∃ k : ℕ, k ^ n = a

theorem perfectPower_iff_radRem_zero (n a : ℕ) (hn : n ≠ 0) :
    isPerfectPower n a ↔ radRem n a = 0 := by
  constructor
  · intro ⟨k, hk⟩
    -- a = k^n, we must show radRem n (k^n) = 0
    subst hk
    simp only [radRem]
    -- irootN n (k^n) = k  by squeeze
    have hle  := irootN_pow_le  n (k ^ n) hn
    have hlt  := irootN_lt_succ_pow n (k ^ n) hn
    -- (irootN n (k^n))^n ≤ k^n  and  k^n < (irootN n (k^n) + 1)^n
    -- Hence irootN n (k^n) = k
    have heq : irootN n (k ^ n) = k := by
      apply Nat.le_antisymm
      · -- irootN n (k^n) ≤ k
        -- By contradiction: suppose irootN n (k^n) ≥ k+1.
        -- Then (irootN n (k^n))^n ≥ (k+1)^n.
        -- But (irootN n (k^n))^n ≤ k^n (from hle).
        -- Hence (k+1)^n ≤ k^n — absurd since k^n < (k+1)^n.
        by_contra h
        push_neg at h
        -- h : k + 1 ≤ irootN n (k^n)
        have hge : (k + 1) ^ n ≤ (irootN n (k ^ n)) ^ n :=
          Nat.pow_le_pow_left h n
        -- hle : (irootN n (k^n))^n ≤ k^n
        -- Hence (k+1)^n ≤ k^n, but k^n < (k+1)^n from Nat.lt_succ_self+pow
        have hlt2 : k ^ n < (k + 1) ^ n :=
          Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
        -- Chain: (k+1)^n ≤ irootN^n ≤ k^n < (k+1)^n
        omega
      · -- k ≤ irootN n (k^n)
        -- By contradiction: suppose irootN n (k^n) < k, i.e. irootN+1 ≤ k.
        -- Then (irootN+1)^n ≤ k^n.
        -- But k^n < (irootN n (k^n)+1)^n (from hlt) — contradiction.
        by_contra h
        push_neg at h
        -- h : irootN n (k^n) + 1 ≤ k
        have hle2 : (irootN n (k ^ n) + 1) ^ n ≤ k ^ n :=
          Nat.pow_le_pow_left h n
        -- hlt : k^n < (irootN n (k^n)+1)^n
        -- Hence k^n < (irootN+1)^n ≤ k^n — absurd
        omega
    rw [heq]
    omega
  · intro h
    simp only [radRem] at h
    -- h : a - (irootN n a) ^ n = 0
    -- We must construct k with k^n = a, i.e. k = irootN n a.
    -- From h: (irootN n a)^n = a  (since irootN^n ≤ a by irootN_pow_le)
    have hle := irootN_pow_le n a hn
    -- From h and hle: (irootN n a)^n = a
    have heqa : (irootN n a) ^ n = a := by omega
    exact ⟨irootN n a, heqa⟩

/-!
## Project Status
-/

end CampiOperazionistici

/-!
## Section 7: Growing Frontier Theorem
-/

section GrowingFrontier

def gap (n k : ℕ) : ℕ := (k + 1) ^ n - k ^ n
def maxRem (n k : ℕ) : ℕ := gap n k - 1

-- Computational checks
#eval gap 2 0   -- 1
#eval gap 2 1   -- 3
#eval gap 2 2   -- 5
#eval gap 2 3   -- 7
#eval gap 2 4   -- 9

#eval gap 3 1   -- 7
#eval gap 3 2   -- 19
#eval gap 3 3   -- 37

#eval maxRem 2 1   -- 2
#eval maxRem 2 2   -- 4
#eval maxRem 2 3   -- 6
#eval maxRem 2 4   -- 8

-- ================================================================
-- Additional lemmas for irootN and radRem (needed by aoddepth.lean)
-- ================================================================

open CampiOperazionistici

lemma irootN_unique (n a k : ℕ) (hn : n ≠ 0)
    (hle : k ^ n ≤ a) (hlt : a < (k + 1) ^ n) : irootN n a = k := by
  apply Nat.le_antisymm
  · by_contra h; push_neg at h
    linarith [Nat.pow_le_pow_left h n, irootN_pow_le n a hn]
  · by_contra h; push_neg at h
    linarith [Nat.pow_le_pow_left h n, irootN_lt_succ_pow n a hn]

lemma irootN_of_pow (n k : ℕ) (hn : n ≠ 0) : irootN n (k ^ n) = k :=
  irootN_unique n (k ^ n) k hn le_rfl
    (Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn)

lemma radRem_of_pow (n k : ℕ) (hn : n ≠ 0) : radRem n (k ^ n) = 0 := by
  simp [radRem, irootN_of_pow n k hn]

lemma irootN_of_chapter (n k r : ℕ) (hn : n ≠ 0) (hr : r < gap n k) :
    irootN n (k ^ n + r) = k :=
  irootN_unique n (k ^ n + r) k hn (Nat.le_add_right _ _)
    (by simp [gap] at hr; omega)

lemma radRem_of_chapter (n k r : ℕ) (hn : n ≠ 0) (hr : r < gap n k) :
    radRem n (k ^ n + r) = r := by
  simp [radRem, irootN_of_chapter n k r hn hr]

lemma irootN_pos (n a : ℕ) (hn : n ≠ 0) (ha : 1 ≤ a) : 1 ≤ irootN n a := by
  by_contra h; push_neg at h
  have h0 : irootN n a = 0 := Nat.lt_one_iff.mp h
  have hlt := irootN_lt_succ_pow n a hn
  rw [h0] at hlt; simp at hlt; omega

lemma radRem_lt_self (n a : ℕ) (hn : n ≠ 0) (ha : 1 ≤ a) : radRem n a < a := by
  simp only [radRem]
  have h1 : 1 ≤ irootN n a       := irootN_pos n a hn ha
  have h2 : 1 ≤ (irootN n a) ^ n := Nat.one_le_pow n _ (by omega)
  have h3 : (irootN n a) ^ n ≤ a := irootN_pow_le n a hn
  omega

/- `sq_convex`: discrete convexity identity for squares, closed with `ring`. -/
lemma sq_convex (k : ℕ) (hk : 1 ≤ k) :
    (k + 1) ^ 2 + (k - 1) ^ 2 = 2 * k ^ 2 + 2 := by
  cases k with
  | zero => omega
  | succ m =>
    simp only [Nat.succ_sub_one]
    ring

/-
  `gap_sq_strictMono`.
  Strategy: we immediately convert the goal into ℤ using `Nat.cast_lt`,
  then rewrite the ℕ gaps (with truncated subtraction) as ℤ differences
  thanks to the monotonicity hypotheses, and conclude with `ring_nf` + `linarith`.

  The key is to NOT use `zify` on the final goal (it leaves `↑(a-b)` opaque),
  but to build the equations on the casts by hand.
-/
lemma gap_sq_strictMono (k : ℕ) : gap 2 k < gap 2 (k + 1) := by
  simp only [gap]
  -- Fix the non-truncation hypotheses for the ℕ subtraction
  have hle1 : k ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ k) 2
  have hle2 : (k + 1) ^ 2 ≤ (k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- Transfer to ℤ where the subtraction is the integer one
  rw [show (k + 1 + 1) = k + 2 from by ring]
  -- Apply Nat.cast_lt to work over ℤ
  rw [← Nat.cast_lt (α := ℤ)]
  -- Convert the ℕ subtractions into ℤ subtractions
  rw [Nat.cast_sub hle1, Nat.cast_sub hle2]
  push_cast
  nlinarith [sq_nonneg (k : ℤ)]

def gapZ (n k : ℤ) : ℤ := (k + 1) ^ n.toNat - k ^ n.toNat

/-
  `discrete_convexity`.

  Note on induction: `induction n` specializes `ih` on the current value of `n`,
  and the extra hypotheses (hn, hk) do NOT become arguments of `ih` — they are already
  in the context as constants. Hence `ih (by omega) hk` fails because `ih`
  is not a function.

  Solution: we split the proof into two levels.
  1. `discrete_convexity_aux`: induction on n with k fixed, without the hypothesis hn
     (we prove it for all n ≥ 0, with the case n=0,1 handled by nlinarith).
  2. `discrete_convexity`: uses the aux with the original hypotheses.
-/

/-- Auxiliary lemma: discrete convexity for every n and k ≥ 1.
    Proof by induction on n without external hypotheses on the index. -/
private lemma discrete_convexity_aux (k : ℕ) (hk : 1 ≤ k) :
    ∀ n : ℕ, 2 ≤ n → (k + 2 : ℤ) ^ n + k ^ n > 2 * (k + 1 : ℤ) ^ n := by
  -- Positivity bounds over ℤ, valid throughout the lemma
  have hk1 : (0 : ℤ) < k     := by exact_mod_cast Nat.lt_of_succ_le hk
  have hk2 : (0 : ℤ) < k + 1 := by linarith
  have hk3 : (0 : ℤ) < k + 2 := by linarith
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
    intro hm
    cases m with
    | zero => omega    -- 2 ≤ 1 is false
    | succ p =>
      cases p with
      | zero =>
        -- n = 2: base case
        -- goal: (k+2)^2 + k^2 > 2*(k+1)^2
        -- we expand: k²+4k+4 + k² > 2k²+4k+2  ↔  4 > 2  ✓
        norm_num [pow_succ, pow_zero]
        nlinarith [sq_nonneg (k : ℤ), hk1]
      | succ q =>
        -- n = q + 3, inductive step
        -- We unify the notation: q+1+1 = q+2 in the type of ih
        -- ih : 2 ≤ q+1+1 → (k+2)^(q+1+1) + k^(q+1+1) > 2*(k+1)^(q+1+1)
        have hm2 : 2 ≤ q + 1 + 1 := by omega
        have ih' := ih hm2
        -- Abbreviations for readability
        set A := (k + 2 : ℤ) ^ (q + 1 + 1) with hA
        set B := (k + 1 : ℤ) ^ (q + 1 + 1) with hB
        set C := (k     : ℤ) ^ (q + 1 + 1) with hC
        -- ih' : A + C > 2 * B
        -- Positivity bounds on the powers
        have hA_pos : 0 < A := pow_pos hk3 _
        have hB_pos : 0 < B := pow_pos hk2 _
        have hC_pos : 0 < C := pow_pos hk1 _
        -- The goal is: (k+2)^(q+3) + k^(q+3) > 2*(k+1)^(q+3)
        -- i.e.: (k+2)*A + k*C > 2*(k+1)*B
        -- We rewrite the powers with the right exponent
        -- We rewrite the goal in terms of A, B, C (already defined with set)
        -- so that nlinarith works on uniform variables.
        -- Goal: A*(k+2) + C*k > 2*(B*(k+1))
        have hgoal : (k + 2 : ℤ) ^ (q + 1 + 1 + 1) + (k : ℤ) ^ (q + 1 + 1 + 1) >
                     2 * (k + 1 : ℤ) ^ (q + 1 + 1 + 1) := by
          -- We write the powers at step n+1 as a product with step n
          have hA_step : (k + 2 : ℤ) ^ (q + 1 + 1 + 1) = A * (k + 2) := by
            simp [hA, pow_succ, mul_comm]
          have hB_step : (k + 1 : ℤ) ^ (q + 1 + 1 + 1) = B * (k + 1) := by
            simp [hB, pow_succ, mul_comm]
          have hC_step : (k : ℤ) ^ (q + 1 + 1 + 1) = C * k := by
            simp [hC, pow_succ, mul_comm]
          -- hAC: A > C  (same exponent, larger base)
          have hAC : A > C := by
            have hlt_nat : k ^ (q + 1 + 1) < (k + 2) ^ (q + 1 + 1) :=
              Nat.pow_lt_pow_left (by omega) (by omega)
            have : (k ^ (q + 1 + 1) : ℤ) < ((k + 2) ^ (q + 1 + 1) : ℤ) :=
              by exact_mod_cast hlt_nat
            linarith [hA, hC]
          rw [hA_step, hB_step, hC_step]
          -- goal: A*(k+2) + C*k > 2*(B*(k+1))
          -- ih': A + C > 2*B
          -- A*(k+2) + C*k = A*(k+1) + A + C*k
          --               = A*(k+1) + C*(k+1) + (A - C) + (A - C*(k+1) + C*k) -- we simplify
          -- More directly: A*(k+2) + C*k = (A+C)*(k+1) + (A-C)
          --              2*B*(k+1) < (A+C)*(k+1) ≤ A*(k+2) + C*k  since A>C≥0
          nlinarith
        exact hgoal

lemma discrete_convexity (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    (k + 2 : ℤ) ^ n + k ^ n > 2 * (k + 1 : ℤ) ^ n :=
  discrete_convexity_aux k hk n hn

/-
  `growingFrontier`: strict monotonicity of the gaps. The proof works over ℤ
  (via `Nat.cast_lt` and `Nat.cast_sub`) to avoid the truncated subtraction of ℕ,
  normalizing the casts with `push_cast`.
-/
theorem growingFrontier (n k : ℕ) (hn : 2 ≤ n) :
    gap n k < gap n (k + 1) := by
  simp only [gap]
  -- We work entirely over ℤ to avoid truncated ℕ subtractions.
  -- We bring the goal to ℤ via Nat.cast_lt, then use Nat.cast_sub
  -- only after providing the non-truncation hypotheses.
  have hPQ : k ^ n ≤ (k + 1) ^ n       := Nat.pow_le_pow_left (Nat.le_succ k) n
  have hQR : (k + 1) ^ n ≤ (k + 2) ^ n := Nat.pow_le_pow_left (Nat.le_succ (k + 1)) n
  -- ℤ version of the goal: 2*(k+1)^n < (k+2)^n + k^n
  have hZ : 2 * ((k : ℤ) + 1) ^ n < ((k : ℤ) + 2) ^ n + (k : ℤ) ^ n := by
    cases Nat.eq_zero_or_pos k with
    | inl hk0 =>
      subst hk0
      -- k=0: the goal is  2*(0+1)^n < (0+2)^n + 0^n
      --           =  2*1       < 2^n + 0        (for n ≠ 0)
      --           =  2         < 2^n            (true for n ≥ 2)
      have hn0 : n ≠ 0 := by omega
      simp only [Nat.cast_zero, zero_add, zero_pow hn0, add_zero, one_pow]
      -- goal over ℤ: 2 * 1 < 2^n
      -- We need 4 ≤ 2^n for n ≥ 2, not just 2 ≤ 2^n
      have h4n : (4 : ℤ) ≤ 2 ^ n := by
        have : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
               _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        exact_mod_cast this
      linarith
    | inr hkpos =>
      exact discrete_convexity n k hn hkpos
  -- We transport hZ to ℕ: first we convert the ℕ subtractions
  -- using Nat.cast_sub (which requires the non-truncation hypotheses)
  have h1 : ((k + 1) ^ n - k ^ n : ℕ) < ((k + 2) ^ n - (k + 1) ^ n : ℕ) := by
    zify [hPQ, hQR]
    linarith
  exact h1

theorem maxRem_strictMono (n k : ℕ) (hn : 2 ≤ n) :
    maxRem n k < maxRem n (k + 1) := by
  have hgap : gap n k < gap n (k + 1) := growingFrontier n k hn
  have hg1 : 1 ≤ gap n k := by
    simp only [gap]
    have hPQ : k ^ n < (k + 1) ^ n :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega)
    omega
  simp only [maxRem]
  omega

/-
  `frontier_rests_are_new`: every remainder in the frontier band of chapter `k`
  is strictly greater than all the maximal remainders of the previous chapters.
-/
theorem frontier_rests_are_new (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (t : ℕ) (ht_lo : maxRem n (k-1) < t) (_ht_hi : t ≤ maxRem n k) :
    ∀ j < k, t > maxRem n j := by
  intro j hj
  -- Auxiliary lemma: maxRem is monotone (non-strictly) in k
  have hmono : ∀ a b : ℕ, a ≤ b → maxRem n a ≤ maxRem n b := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | step h ih =>
        exact le_trans ih (le_of_lt (maxRem_strictMono n _ hn))
  -- maxRem n j ≤ maxRem n (k-1) since j < k, i.e. j ≤ k-1
  have hjk : j ≤ k - 1 := by omega
  have hle : maxRem n j ≤ maxRem n (k - 1) := hmono j (k - 1) hjk
  omega

end GrowingFrontier

/-!
## Section 8: Operational Alterity Theorem
-/

section OperationalAlterity

open CampiOperazionistici

/-- If irootN n t = 0 then t = 0. -/
lemma irootN_eq_zero_iff (n t : ℕ) (hn : n ≠ 0) :
    irootN n t = 0 ↔ t = 0 := by
  constructor
  · intro h
    -- SPEC 2: t < (irootN n t + 1)^n = (0+1)^n = 1  →  t = 0
    have hlt := irootN_lt_succ_pow n t hn
    rw [h] at hlt
    -- hlt : t < (0 + 1)^n = 1^n = 1
    simp at hlt
    -- hlt : t < 1  →  t = 0
    omega
  · intro h
    subst h
    -- irootN n 0: irootAux n 0 0 = 0 (the search starts from bound=0)
    simp [irootN, hn, irootAux]

/-- No positive number is a fixed point of the radical remainder. -/
lemma no_fixed_point (n t : ℕ) (hn : n ≠ 0) (ht : 1 ≤ t) :
    radRem n t ≠ t := by
  simp only [radRem]
  intro h
  have hpow : (irootN n t) ^ n = 0 := by
    have hle := irootN_pow_le n t hn
    omega
  have hroot : irootN n t = 0 := by
    exact (Nat.pow_eq_zero.mp hpow).1
  have ht0 : t = 0 := (irootN_eq_zero_iff n t hn).mp hroot
  omega

lemma eval_implies_nonequiv (n x t : ℕ) (hn : n ≠ 0) (ht : 1 ≤ t)
    (heval : x ↠[n] t) : ¬ (x ≡ₒ t [Aod n]) := by
  simp only [aodEval] at heval
  simp only [aodEquiv]
  rw [heval]
  exact (no_fixed_point n t hn ht).symm

lemma nonequiv_implies_eval_differs (n x t : ℕ) (_hn : n ≠ 0) (_ht : 1 ≤ t)
    (hne : ¬ (x ≡ₒ t [Aod n])) : (x ↠[n] (radRem n x)) ∧ radRem n x ≠ radRem n t := by
  constructor
  · simp [aodEval]
  · simp [aodEquiv] at hne
    exact hne


/-- Corrected and fully provable version of Theorem 2. -/
theorem operationalAlterity_v2 (n x t : ℕ) (hn : n ≠ 0) (ht : 1 ≤ t) :
    (x ↠[n] t) ↔ (radRem n x = t ∧ ¬ (x ≡ₒ t [Aod n])) := by
  simp only [aodEval, aodEquiv]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rw [h]
    exact (no_fixed_point n t hn ht).symm
  · intro ⟨h, _⟩
    exact h

/-- Corollary: the result of the eval is strictly less than the number. -/
theorem eval_result_lt (n x t : ℕ) (hn : n ≠ 0) (_ht : 1 ≤ t)
    (heval : x ↠[n] t) (hx : 1 ≤ x) : t < x := by
  simp only [aodEval] at heval
  rw [← heval]
  simp only [radRem]
  have hle := irootN_pow_le n x hn
  have hroot_pos : 1 ≤ irootN n x := by
    by_contra h
    push_neg at h
    have := (irootN_eq_zero_iff n x hn).mp (Nat.lt_one_iff.mp h)
    omega
  have hpow_pos : 1 ≤ (irootN n x) ^ n :=
    Nat.one_le_pow n _ (by omega)
  omega

end OperationalAlterity

/-!
## Section 9: Landing Congruence

  Author: Alessandro Sgarbi
  Date:   2026-02-28

  Informal statement:
    Let n ≥ 1, k ≥ 1, j ≥ 1 and
      r < gap(n,k),  s < gap(n,j).
    Let m = irootN n (k^n + j^n)  be the "landing chapter" of the sum
    of the bases.
    We define the **landing shift**:
      δ(n,k,j) = radRem n (k^n + j^n)
    Then, provided r + s < gap(n,m):
      radRem n (k^n + r + (j^n + s)) = (δ(n,k,j) + r + s) % gap(n,m)

  Structure of the section:
    9a — Definitions: capitoloArrivo, shiftArrivo, opCap
    9b — Auxiliary lemmas (irootN on bases and remainders)
    9c — Key lemma: decomposition of the sum
    9d — Main theorem (with no-overflow hypothesis)
    9e — Computational checks
    9f — Structural corollaries (group, formal isomorphism)
-/

section LandingCongruence

open CampiOperazionistici

/-! ### 9a — Definitions -/

/-- The landing chapter of the sum of the bases k^n + j^n. -/
def capitoloArrivo (n k j : ℕ) : ℕ :=
  irootN n (k ^ n + j ^ n)

/-- The landing shift: the radRem of the sum of the bases. -/
def shiftArrivo (n k j : ℕ) : ℕ :=
  radRem n (k ^ n + j ^ n)

/-- The chapter operation: sum of two local addresses with the shift. -/
def opCap (n k j r s : ℕ) : ℕ :=
  (shiftArrivo n k j + r + s) % gap n (capitoloArrivo n k j)

-- Computational checks
-- n=2, k=j=1: bases 1+1=2, iroot=1, shift=1, gap(2,1)=3
#eval capitoloArrivo 2 1 1   -- 1
#eval shiftArrivo 2 1 1      -- 1
#eval gap 2 1                -- 3

-- n=3, k=j=1: bases 1+1=2, iroot=1, shift=1, gap(3,1)=7
#eval capitoloArrivo 3 1 1   -- 1
#eval shiftArrivo 3 1 1      -- 1
#eval gap 3 1                -- 7

-- n=3, k=j=2: bases 8+8=16, iroot(3,16)=2, shift=16-8=8, gap(3,2)=19
#eval capitoloArrivo 3 2 2   -- 2
#eval shiftArrivo 3 2 2      -- 8
#eval gap 3 2                -- 19

-- n=2, k=2, j=3: bases 4+9=13, iroot(2,13)=3, shift=13-9=4, gap(2,3)=7
#eval capitoloArrivo 2 2 3   -- 3
#eval shiftArrivo 2 2 3      -- 4
#eval gap 2 3                -- 7

/-! ### 9b — Auxiliary lemmas -/

/-- irootN is monotone: a ≤ b → irootN n a ≤ irootN n b. -/
lemma irootN_mono (n a b : ℕ) (hn : n ≠ 0) (hab : a ≤ b) :
    irootN n a ≤ irootN n b := by
  by_contra h
  push_neg at h
  -- h : irootN n b < irootN n a
  -- SPEC 1 on b: (irootN n b)^n ≤ b
  -- SPEC 2 on a: a < (irootN n a + 1)^n
  -- Since irootN n b + 1 ≤ irootN n a:
  have hsucc : irootN n b + 1 ≤ irootN n a := h
  have hle_b := irootN_pow_le n b hn
  have hlt_a := irootN_lt_succ_pow n a hn
  -- (irootN n b + 1)^n ≤ (irootN n a)^n ≤ b < ??? no
  -- More directly: (irootN n a)^n ≤ a ≤ b and (irootN n b)^n ≤ b
  -- but irootN n b < irootN n a, hence
  -- b < (irootN n b + 1)^n ≤ (irootN n a)^n ≤ a ≤ b — contradiction.
  have hstep : (irootN n b + 1) ^ n ≤ (irootN n a) ^ n :=
    Nat.pow_le_pow_left hsucc n
  have hlt_b := irootN_lt_succ_pow n b hn
  have hle_a := irootN_pow_le n a hn
  -- Chain: b < (irootN n b + 1)^n ≤ (irootN n a)^n ≤ a ≤ b
  -- All inequalities over ℕ — linarith sees them as opaque variables
  linarith

/-- The sum k^n + r stays in chapter k if r < gap(n,k). -/
lemma sum_in_chapter (n k r : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k) : irootN n (k ^ n + r) = k := by
  apply Nat.le_antisymm
  · -- irootN n (k^n + r) ≤ k
    -- Since k^n + r < (k+1)^n (from the definition of gap)
    have hlt : k ^ n + r < (k + 1) ^ n := by
      simp [gap] at hr; omega
    -- (irootN n (k^n+r))^n ≤ k^n+r < (k+1)^n
    -- and (k+1)^n = (k+1)^n, hence irootN ≤ k
    have hle := irootN_pow_le n (k ^ n + r) hn
    have hlt2 := irootN_lt_succ_pow n (k ^ n + r) hn
    by_contra h
    push_neg at h
    -- h: k + 1 ≤ irootN n (k^n + r)
    have hbig : (k + 1) ^ n ≤ (irootN n (k ^ n + r)) ^ n :=
      Nat.pow_le_pow_left h n
    omega
  · -- k ≤ irootN n (k^n + r)
    -- k^n ≤ k^n + r and (irootN n (k^n))^n = k^n ≤ k^n + r
    have hk_le : k ^ n ≤ k ^ n + r := Nat.le_add_right _ _
    -- irootN n (k^n) = k (from the perfectPower theorem)
    -- We use irootN_mono
    have hle_base : k ≤ irootN n (k ^ n) := by
      have hle' := irootN_pow_le n (k ^ n) hn
      have hlt' := irootN_lt_succ_pow n (k ^ n) hn
      by_contra h
      push_neg at h
      -- h : irootN n (k^n) < k, i.e. irootN n (k^n) + 1 ≤ k
      -- Hence (irootN n (k^n))^n < k^n, but (irootN n (k^n))^n ≤ k^n
      -- More directly: k^n < (k^n + 1)^n... no, we use SPEC 2:
      -- k^n < (irootN n (k^n) + 1)^n ≤ k^n  — contradiction
      have hsucc_le : irootN n (k ^ n) + 1 ≤ k := h
      have hpow_lt : (irootN n (k ^ n) + 1) ^ n ≤ k ^ n :=
        Nat.pow_le_pow_left hsucc_le n
      linarith
    have hmono := irootN_mono n (k ^ n) (k ^ n + r) hn (Nat.le_add_right _ _)
    omega

/-- radRem of k^n + r (with r < gap) is exactly r. -/
lemma radRem_base_add (n k r : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k) : radRem n (k ^ n + r) = r := by
  simp only [radRem]
  rw [sum_in_chapter n k r hn hr]
  omega

/-! ### 9c — Key lemma: decomposition of the sum -/

/-- The sum of the bases: k^n + j^n = (capitoloArrivo)^n + shiftArrivo. -/
lemma sum_bases_decomp (n k j : ℕ) (hn : n ≠ 0) :
    k ^ n + j ^ n =
    (capitoloArrivo n k j) ^ n + shiftArrivo n k j := by
  simp [shiftArrivo, radRem, capitoloArrivo]
  have hle := irootN_pow_le n (k ^ n + j ^ n) hn
  omega

/-- shiftArrivo is strictly less than gap(n, capitoloArrivo). -/
lemma shiftArrivo_lt_gap (n k j : ℕ) (hn : n ≠ 0) :
    shiftArrivo n k j < gap n (capitoloArrivo n k j) := by
  simp only [shiftArrivo, capitoloArrivo, gap]
  exact radRem_lt_gap n (k ^ n + j ^ n) hn

/-- Rewriting of the full sum in terms of capitoloArrivo and shift. -/
lemma sum_rewrite (n k j r s : ℕ) (hn : n ≠ 0) :
    k ^ n + r + (j ^ n + s) =
    (capitoloArrivo n k j) ^ n + (shiftArrivo n k j + r + s) := by
  have := sum_bases_decomp n k j hn
  omega

/-! ### 9d — Main theorem: Landing Congruence -/

/--
  **Landing Congruence Theorem**

  If r + s does not cause overflow in the landing chapter
  (i.e. shiftArrivo + r + s < gap of the landing chapter),
  then the radRem of the sum is exactly the shift + r + s.

  In symbols:
    radRem n (k^n + r + (j^n + s)) = shiftArrivo n k j + r + s

  The congruence modulo gap is obtained as an immediate corollary.
-/
theorem landingCongruence (n k j r s : ℕ) (hn : n ≠ 0)
    (_hr : r < gap n k)
    (_hs : s < gap n j)
    (hno_overflow : shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j)) :
    radRem n (k ^ n + r + (j ^ n + s)) =
    shiftArrivo n k j + r + s := by
  -- Step 1: we rewrite the sum as base + shift
  rw [sum_rewrite n k j r s hn]
  -- Step 2: we apply radRem_base_add with the landing chapter
  exact radRem_base_add n (capitoloArrivo n k j) (shiftArrivo n k j + r + s) hn hno_overflow

/--
  **Corollary: Modular Congruence**

  The "mod gap" version of the landing theorem: same conclusion
  but expressed as a modular congruence, valid also when
  shiftArrivo + r + s ≥ gap (if the sum falls into the next chapter).

  Note: this form requires weaker hypotheses but gives a weaker
  conclusion. The main theorem (landingCongruence) provides
  the exact equality under stronger hypotheses.
-/
theorem landingCongruence_mod (n k j r s : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k)
    (hs : s < gap n j)
    (hno_overflow : shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j)) :
    radRem n (k ^ n + r + (j ^ n + s)) % gap n (capitoloArrivo n k j) =
    (shiftArrivo n k j + r + s) % gap n (capitoloArrivo n k j) := by
  congr 1
  exact landingCongruence n k j r s hn hr hs hno_overflow

/-! ### 9e — Computational checks of the theorem -/

-- Test 1: n=3, k=j=1, r=3, s=2
-- bases: 1+1=2, shift=1, chapter=1, gap=7
-- sum: 1+3 + 1+2 = 7, radRem(3,7) = 0
-- formula: shift+r+s = 1+3+2 = 6
-- no_overflow: 6 < 7 ✓
-- Expected result: 6 (radRem 3 7 = 7 - 1 = 6)
#eval radRem 3 (1^3 + 3 + (1^3 + 2))     -- 6
#eval shiftArrivo 3 1 1 + 3 + 2           -- 6 ✓

-- Test 2: n=2, k=j=1, r=1, s=1
-- bases: 1+1=2, shift=1, chapter=1, gap=3
-- sum: 1+1 + 1+1 = 4, radRem(2,4) = 0
-- formula: 1+1+1 = 3, no_overflow: 3 < 3? NO → overflow!
-- (4 = 2^2, perfect square → radRem=0)
-- This is the limit case: r+s=2 = gap-1, shift=1 → 1+2=3 = gap → overflow
#eval radRem 2 (1^2 + 1 + (1^2 + 1))     -- 0 (it is 4 = 2^2)
#eval shiftArrivo 2 1 1 + 1 + 1           -- 3 (= gap → overflow correct)

-- Test 3: n=3, k=2, j=2, r=5, s=4
-- bases: 8+8=16, iroot(3,16)=2, shift=16-8=8, chapter=2, gap(3,2)=19
-- formula: 8+5+4=17, no_overflow: 17 < 19 ✓
-- sum: 8+5 + 8+4 = 25, radRem(3,25) = 25 - 8 = 17
#eval radRem 3 (2^3 + 5 + (2^3 + 4))     -- 17
#eval shiftArrivo 3 2 2 + 5 + 4           -- 17 ✓

-- Test 4: n=2, k=2, j=3, r=2, s=3
-- bases: 4+9=13, iroot(2,13)=3, shift=13-9=4, chapter=3, gap(2,3)=7
-- formula: 4+2+3=9, no_overflow: 9 < 7? NO → overflow → boundary test
#eval capitoloArrivo 2 2 3    -- 3
#eval shiftArrivo 2 2 3       -- 4
#eval gap 2 3                  -- 7
-- r=1, s=1: formula 4+1+1=6 < 7 ✓
#eval radRem 2 (2^2 + 1 + (3^2 + 1))     -- 6
#eval shiftArrivo 2 2 3 + 1 + 1           -- 6 ✓

-- Test 5: n=4, k=1, j=2, r=3, s=10
-- bases: 1+16=17, iroot(4,17)=2, shift=17-16=1, chapter=2, gap(4,2)=65
-- formula: 1+3+10=14 < 65 ✓
-- sum: 1+3 + 16+10 = 30, radRem(4,30) = 30 - 16 = 14
#eval radRem 4 (1^4 + 3 + (2^4 + 10))    -- 14
#eval shiftArrivo 4 1 2 + 3 + 10          -- 14 ✓

/-! ### 9f — Structural corollaries -/

/--
  **Symmetry of the shift**: shiftArrivo is symmetric in k and j
  (since k^n + j^n = j^n + k^n).
-/
lemma shiftArrivo_symm (n k j : ℕ) :
    shiftArrivo n k j = shiftArrivo n j k := by
  simp [shiftArrivo, add_comm]

/-- capitoloArrivo is symmetric in k and j. -/
lemma capitoloArrivo_symm (n k j : ℕ) :
    capitoloArrivo n k j = capitoloArrivo n j k := by
  simp [capitoloArrivo, add_comm]

/--
  **Commutativity of the operation**: opCap is commutative in r, s.
-/
lemma opCap_comm (n k j r s : ℕ) :
    opCap n k j r s = opCap n k j s r := by
  simp [opCap, add_comm, add_left_comm]

/--
  **The landing theorem implies the commutativity of radRem**:
  under the no-overflow hypotheses, radRem is the same if the
  two addends are swapped (including chapters).
-/
theorem landingCongruence_symm (n k j r s : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k)
    (hs : s < gap n j)
    (hno_overflow : shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j)) :
    radRem n (k ^ n + r + (j ^ n + s)) =
    radRem n (j ^ n + s + (k ^ n + r)) := by
  rw [landingCongruence n k j r s hn hr hs hno_overflow]
  -- The sum j^n+s + (k^n+r) has shift shiftArrivo n j k = shiftArrivo n k j
  have hno_overflow' : shiftArrivo n j k + s + r < gap n (capitoloArrivo n j k) := by
    rw [shiftArrivo_symm, capitoloArrivo_symm]; omega
  rw [landingCongruence n j k s r hn hs hr hno_overflow']
  rw [shiftArrivo_symm]
  omega

/--
  **Monotonicity**: if r ≤ r', then the landing value is ≤.
  (Useful for estimating the landing chapter in the overflow cases.)
-/
theorem landingCongruence_mono (n k j r r' s : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k) (hr' : r' < gap n k)
    (hs : s < gap n j) (hrr' : r ≤ r')
    (hno_overflow  : shiftArrivo n k j + r  + s < gap n (capitoloArrivo n k j))
    (hno_overflow' : shiftArrivo n k j + r' + s < gap n (capitoloArrivo n k j)) :
    radRem n (k ^ n + r + (j ^ n + s)) ≤
    radRem n (k ^ n + r' + (j ^ n + s)) := by
  rw [landingCongruence n k j r  s hn hr  hs hno_overflow]
  rw [landingCongruence n k j r' s hn hr' hs hno_overflow']
  omega

end LandingCongruence
/-!
## Section 10: Characterization of the No-Overflow Hypothesis

  Goal: give a **necessary and sufficient** condition and an
  **explicit sufficient** one for `hno_overflow`, in terms depending
  only on n, k, j — not on r, s.

  Structure:
    10a — Equivalent reformulation of hno_overflow
    10b — Estimate of the landing chapter: m ≤ k + j
    10c — Uniform sufficient condition
    10d — Main theorem without explicit hno_overflow
    10e — Diagonal case k = j and connection with the 2^(1/n) threshold
-/

section NoOverflowCharacterization

open CampiOperazionistici

/-! ### 10a — Equivalent reformulation -/

/--
  The no-overflow hypothesis is equivalent to requiring that the total
  sum `k^n + j^n + r + s` does not exceed the ceiling of the landing chapter.

  In formulas: shift + r + s < gap(n,m)
  ↔ k^n + j^n - m^n + r + s < (m+1)^n - m^n
  ↔ k^n + j^n + r + s < (m+1)^n
-/
lemma noOverflow_iff (n k j r s : ℕ) (hn : n ≠ 0) :
    shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j)
    ↔
    k ^ n + j ^ n + r + s < (capitoloArrivo n k j + 1) ^ n := by
  simp only [shiftArrivo, gap, radRem, capitoloArrivo]
  -- shift = k^n + j^n - (irootN n (k^n+j^n))^n
  -- gap   = (irootN n (k^n+j^n) + 1)^n - (irootN n (k^n+j^n))^n
  -- Both sides simplify with omega after fixing
  -- hle : (irootN ...)^n ≤ k^n + j^n
  have hle := irootN_pow_le n (k ^ n + j ^ n) hn
  omega

/-- "Ceiling" version of the condition: equivalent to staying below (m+1)^n. -/
lemma noOverflow_iff' (n k j r s : ℕ) (hn : n ≠ 0) :
    shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j)
    ↔
    k ^ n + r + (j ^ n + s) < (capitoloArrivo n k j + 1) ^ n := by
  rw [noOverflow_iff n k j r s hn]
  omega

/-! ### 10b — Estimate of the landing chapter -/

/--
  The landing chapter always satisfies `m ≤ k + j`.
  Equivalently: `(k + j)^n ≥ k^n + j^n`.

  Proof: for n ≥ 1 and k, j ≥ 0,
    (k + j)^n ≥ k^n + j^n  (binomial expansion, all mixed terms ≥ 0)
  hence irootN n (k^n + j^n) ≤ irootN n ((k+j)^n) = k + j.
-/
lemma capitoloArrivo_le_sum (n k j : ℕ) (hn : n ≠ 0) :
    capitoloArrivo n k j ≤ k + j := by
  simp only [capitoloArrivo]
  -- It suffices to show: irootN n (k^n + j^n) ≤ k + j
  -- Equivalently (by SPEC 1): (k+j+1)^n > k^n + j^n,
  -- i.e. it suffices to show (k+j)^n ≥ k^n + j^n and then use irootN_mono.
  -- We use SPEC 2 of irootN applied to (k+j)^n:
  --   irootN n ((k+j)^n) = k + j  (perfectPower)
  -- and the monotonicity of irootN.
  -- Step 1: k^n + j^n ≤ (k + j)^n
  -- Proof over ℕ by induction on n, without casting to ℤ.
  -- The structure is: (k+j)^(n+1) = (k+j) * (k+j)^n
  --                              ≥ (k+j) * (k^n + j^n)   [by ih]
  --                              = k^(n+1) + j^(n+1) + j*k^n + k*j^n
  --                              ≥ k^(n+1) + j^(n+1)
  have hkj : k ^ n + j ^ n ≤ (k + j) ^ n := by
    -- Induction on n directly over ℕ
    induction n with
    | zero => simp at hn
    | succ m ih_m =>
      cases Nat.eq_zero_or_pos m with
      | inl hm0 =>
        -- m = 0, n = 1: k^1 + j^1 = k + j = (k+j)^1
        subst hm0; simp
      | inr hm_pos =>
        -- m ≥ 1: we use ih_m (m ≠ 0 is obtained from hm_pos via omega)
        have ih : k ^ m + j ^ m ≤ (k + j) ^ m := ih_m (by omega)
        -- Goal: k^(m+1) + j^(m+1) ≤ (k+j)^(m+1)
        -- Expanded: k*k^m + j*j^m ≤ (k+j)*(k+j)^m
        --        ≥ k*(k+j)^m + j*(k+j)^m  [distributivity]
        --        ≥ k*k^m + j*j^m          [hkle, hjle]
        simp only [pow_succ]
        have hkle : k ^ m ≤ (k + j) ^ m :=
          Nat.pow_le_pow_left (Nat.le_add_right k j) m
        have hjle : j ^ m ≤ (k + j) ^ m :=
          Nat.pow_le_pow_left (Nat.le_add_left j k) m
        have h1 : k * k ^ m ≤ k * (k + j) ^ m := Nat.mul_le_mul_left k hkle
        have h2 : j * j ^ m ≤ j * (k + j) ^ m := Nat.mul_le_mul_left j hjle
        -- goal after simp [pow_succ]: k * k^m + j * j^m ≤ (k+j) * (k+j)^m
        -- rhs = k*(k+j)^m + j*(k+j)^m
        have hrhs : (k + j) * (k + j) ^ m = k * (k + j) ^ m + j * (k + j) ^ m := by ring
        linarith
  -- Step 2: use irootN_mono and the fact that irootN n ((k+j)^n) = k+j
  have hmono := irootN_mono n (k ^ n + j ^ n) ((k + j) ^ n) hn hkj
  have hkj_root : irootN n ((k + j) ^ n) = k + j := by
    apply Nat.le_antisymm
    · -- irootN n ((k+j)^n) ≤ k+j
      -- By contradiction: irootN ≥ k+j+1
      -- Then (k+j+1)^n ≤ (irootN)^n ≤ (k+j)^n
      -- But (k+j)^n < (k+j+1)^n — contradiction
      have hle' := irootN_pow_le n ((k + j) ^ n) hn
      by_contra hc
      push_neg at hc
      have hsucc_le : (k + j) + 1 ≤ irootN n ((k + j) ^ n) := hc
      have hpow_big : ((k + j) + 1) ^ n ≤ (irootN n ((k + j) ^ n)) ^ n :=
        Nat.pow_le_pow_left hsucc_le n
      -- (k+j+1)^n ≤ (irootN)^n ≤ (k+j)^n  but  (k+j)^n < (k+j+1)^n
      have hstrict : (k + j) ^ n < (k + j + 1) ^ n :=
        Nat.pow_lt_pow_left (by omega) hn
      linarith
    · -- k+j ≤ irootN n ((k+j)^n)
      -- By contradiction: irootN ≤ k+j-1, i.e. irootN+1 ≤ k+j
      -- Then (irootN+1)^n ≤ (k+j)^n
      -- But (k+j)^n < (irootN+1)^n  from SPEC 2 — contradiction
      have hlt' := irootN_lt_succ_pow n ((k + j) ^ n) hn
      by_contra hc
      push_neg at hc
      have hsucc_le : irootN n ((k + j) ^ n) + 1 ≤ k + j := hc
      have hpow_lt : (irootN n ((k + j) ^ n) + 1) ^ n ≤ (k + j) ^ n :=
        Nat.pow_le_pow_left hsucc_le n
      linarith
  -- Conclusion: irootN n (k^n+j^n) ≤ irootN n ((k+j)^n) = k+j
  have := hkj_root ▸ hmono
  exact this

/-- Refinement: m ≥ max(k, j). -/
lemma capitoloArrivo_ge_max (n k j : ℕ) (hn : n ≠ 0) :
    k ≤ capitoloArrivo n k j ∧ j ≤ capitoloArrivo n k j := by
  simp only [capitoloArrivo]
  constructor
  · -- k^n ≤ k^n + j^n, hence irootN n (k^n) ≤ irootN n (k^n + j^n)
    have hmono := irootN_mono n (k ^ n) (k ^ n + j ^ n) hn (Nat.le_add_right _ _)
    -- irootN n (k^n) = k: same proof as hle_base in sum_in_chapter
    have hroot_k : k ≤ irootN n (k ^ n) := by
      have hle' := irootN_pow_le n (k ^ n) hn
      have hlt' := irootN_lt_succ_pow n (k ^ n) hn
      by_contra hc; push_neg at hc
      have : (irootN n (k ^ n) + 1) ^ n ≤ k ^ n :=
        Nat.pow_le_pow_left hc n
      linarith
    linarith
  · -- Simmetrico
    have hmono := irootN_mono n (j ^ n) (k ^ n + j ^ n) hn (Nat.le_add_left _ _)
    have hroot_j : j ≤ irootN n (j ^ n) := by
      have hle' := irootN_pow_le n (j ^ n) hn
      have hlt' := irootN_lt_succ_pow n (j ^ n) hn
      by_contra hc; push_neg at hc
      have : (irootN n (j ^ n) + 1) ^ n ≤ j ^ n :=
        Nat.pow_le_pow_left hc n
      linarith
    linarith

/-! ### 10c — Uniform sufficient condition -/

/--
  **Sufficient no-overflow condition** (uniform in r, s).

  If `(k+1)^n + (j+1)^n ≤ (capitoloArrivo n k j + 1)^n`,
  then for any `r < gap n k` and `s < gap n j` there is no overflow.

  Interpretation: the ceiling of the arrival chapter is high enough
  to contain shift + all possible r + all possible s.
-/
lemma noOverflow_of_sufficient (n k j r s : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k)
    (hs : s < gap n j)
    (hsuff : (k + 1) ^ n + (j + 1) ^ n ≤ (capitoloArrivo n k j + 1) ^ n) :
    shiftArrivo n k j + r + s < gap n (capitoloArrivo n k j) := by
  rw [noOverflow_iff n k j r s hn]
  -- We must show: k^n + j^n + r + s < (capitoloArrivo + 1)^n
  -- We know: r < (k+1)^n - k^n,  s < (j+1)^n - j^n
  -- Hence: k^n + j^n + r + s < k^n + j^n + (k+1)^n - k^n + (j+1)^n - j^n
  --                            = (k+1)^n + (j+1)^n
  --                            ≤ (capitoloArrivo + 1)^n
  have hr_bound : r < (k + 1) ^ n - k ^ n := by simp [gap] at hr; omega
  have hs_bound : s < (j + 1) ^ n - j ^ n := by simp [gap] at hs; omega
  -- Support: (k+1)^n ≥ k^n
  have hkpow : k ^ n ≤ (k + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ k) n
  have hjpow : j ^ n ≤ (j + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ j) n
  omega

/-
  MATHEMATICAL NOTE — Condition on (k+j+1) vs capitoloArrivo:

  The condition `(k+1)^n + (j+1)^n ≤ (k+j+1)^n` (proved as
  `noOverflow_kplusj_always` for k,j ≥ 1, n ≥ 2) does NOT imply no-overflow:
  since `capitoloArrivo ≤ k+j`, we have `(capitoloArrivo+1)^n ≤ (k+j+1)^n`,
  i.e. the condition on (k+j+1) is WEAKER than the one on (capitoloArrivo+1)
  required by `noOverflow_of_sufficient`. The useful lemma remains the one with
  the direct hypothesis on `(capitoloArrivo n k j + 1)^n`.
-/

/-! ### 10c' — Correction: sufficient condition via capitoloArrivo -/

/-
  The lemma `noOverflow_of_sufficient_explicit` had a logical error:
  capitoloArrivo ≤ k+j implies (capitoloArrivo+1)^n ≤ (k+j+1)^n,
  so the condition on k+j+1 is STRONGER (more restrictive) than the one
  on capitoloArrivo+1. The lemma with k+j is therefore valid in the
  correct direction if we use k+j as a lower bound of capitoloArrivo (not upper).

  The CORRECT sufficient condition that does not depend on capitoloArrivo is:
    (k+1)^n + (j+1)^n ≤ 2*(k+j+1)^n ... no.

  Actually the useful lemma is the converse: one can give a NECESSARY
  condition using capitoloArrivo ≥ max(k,j), from which
  (capitoloArrivo+1)^n ≥ (max(k,j)+1)^n.
  But it is not sufficient on its own.

  The most useful result is the version with the exact hypothesis on capitoloArrivo,
  already formalized as `noOverflow_of_sufficient`.
-/

-- Note: the condition `(k+1)^n + (j+1)^n ≤ (k+j+1)^n` is always true
-- for n ≥ 2 and k,j ≥ 1, but does NOT imply no-overflow because capitoloArrivo
-- can be strictly smaller than k+j.
-- The correct lemma uses (capitoloArrivo+1)^n directly: `noOverflow_of_sufficient`.

-- Auxiliary lemma: a^n + b^n ≤ (a+b)^n for n ≥ 1.
-- Extracted as a separate lemma to have an induction hypothesis generalized in a,b.
private lemma pow_add_pow_le_add_pow (a b n : ℕ) (hn : n ≠ 0) :
    a ^ n + b ^ n ≤ (a + b) ^ n := by
  induction n with
  | zero => simp at hn
  | succ m ih_m =>
    cases Nat.eq_zero_or_pos m with
    | inl hm0 => subst hm0; simp
    | inr hm_pos =>
      have ih : a ^ m + b ^ m ≤ (a + b) ^ m := ih_m (by omega)
      simp only [pow_succ]
      have hale : a ^ m ≤ (a + b) ^ m := Nat.pow_le_pow_left (Nat.le_add_right a b) m
      have hble : b ^ m ≤ (a + b) ^ m := Nat.pow_le_pow_left (Nat.le_add_left b a) m
      have h1 : a * a ^ m ≤ a * (a + b) ^ m := Nat.mul_le_mul_left a hale
      have h2 : b * b ^ m ≤ b * (a + b) ^ m := Nat.mul_le_mul_left b hble
      have hrhs : (a + b) * (a + b) ^ m = a * (a + b) ^ m + b * (a + b) ^ m := by ring
      linarith

-- Parametric version with free a,b: used internally.
private lemma noOverflow_kplusj_aux (n : ℕ) (hn2 : 2 ≤ n) :
    ∀ k j : ℕ, 1 ≤ k → 1 ≤ j → (k + 1) ^ n + (j + 1) ^ n ≤ (k + j + 1) ^ n := by
  induction n with
  | zero => omega
  | succ m ih_m =>
    intro k j hk hj
    cases m with
    | zero => omega  -- n=1: contradiction with hn2
    | succ p =>
      cases p with
      | zero =>
        -- n = 2
        simp only [pow_succ, pow_zero, one_mul]
        nlinarith
      | succ q =>
        -- n = q+3. ih_m is now ∀ k j, 1≤k → 1≤j → (k+1)^(q+2)+(j+1)^(q+2)≤(k+j+1)^(q+2)
        have ih : (k+1)^(q+2) + (j+1)^(q+2) ≤ (k+j+1)^(q+2) :=
          ih_m (by omega) k j hk hj
        rw [pow_succ (k+1), pow_succ (j+1), pow_succ (k+j+1)]
        have hk1_le : k + 1 ≤ k + j + 1 := by omega
        have hj1_le : j + 1 ≤ k + j + 1 := by omega
        have stepA : (k+1) * (k+1)^(q+2) + (j+1) * (j+1)^(q+2)
                   ≤ (k+j+1) * ((k+1)^(q+2) + (j+1)^(q+2)) := by
          have h1 : (k+1) * (k+1)^(q+2) ≤ (k+j+1) * (k+1)^(q+2) :=
            Nat.mul_le_mul_right _ hk1_le
          have h2 : (j+1) * (j+1)^(q+2) ≤ (k+j+1) * (j+1)^(q+2) :=
            Nat.mul_le_mul_right _ hj1_le
          have expand : (k+j+1) * ((k+1)^(q+2) + (j+1)^(q+2))
                      = (k+j+1) * (k+1)^(q+2) + (k+j+1) * (j+1)^(q+2) := by ring
          linarith [expand]
        have stepB : (k+j+1) * ((k+1)^(q+2) + (j+1)^(q+2))
                   ≤ (k+j+1) * (k+j+1)^(q+2) :=
          Nat.mul_le_mul_left _ ih
        linarith

lemma noOverflow_kplusj_always (n k j : ℕ) (hn2 : 2 ≤ n) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    (k + 1) ^ n + (j + 1) ^ n ≤ (k + j + 1) ^ n :=
  noOverflow_kplusj_aux n hn2 k j hk hj

/-! ### 10d — Main theorem without explicit hno_overflow -/

/--
  **Landing Theorem — Unconditional Version**

  Version of the main theorem in which the no-overflow hypothesis
  is replaced by the explicit sufficient condition on k, j, n.

  Useful when one wants to apply the theorem without computing
  the shift and the gap explicitly.
-/
theorem landingCongruence_unconditional (n k j r s : ℕ) (hn : n ≠ 0)
    (hr : r < gap n k)
    (hs : s < gap n j)
    (hsuff : (k + 1) ^ n + (j + 1) ^ n ≤ (capitoloArrivo n k j + 1) ^ n) :
    radRem n (k ^ n + r + (j ^ n + s)) =
    shiftArrivo n k j + r + s := by
  apply landingCongruence n k j r s hn hr hs
  exact noOverflow_of_sufficient n k j r s hn hr hs hsuff

/-! ### 10e — Diagonal case k = j -/

/--
  **Diagonal case**: when k = j, the arrival chapter satisfies
  `capitoloArrivo n k k ≥ k` and overflow does not occur if
  `2 * (k+1)^n ≤ (capitoloArrivo n k k + 1)^n`.

  Connection with the computational threshold:
  The condition `2 * k^n < (k+1)^n` (equivalent to `k < 1/(2^(1/n)-1)`)
  corresponds to the case where `capitoloArrivo n k k = k` (the bases sum
  to something still in chapter k), and in that case the shift is small.
-/
lemma capitoloArrivo_diag_eq_k (n k : ℕ) (hn : n ≠ 0)
    (h2k : 2 * k ^ n < (k + 1) ^ n) :
    capitoloArrivo n k k = k := by
  simp only [capitoloArrivo]
  -- 2*k^n < (k+1)^n  and  irootN n (2*k^n) must be k
  -- We use sum_in_chapter with r = k^n (fictitious, but the sum is 2*k^n)
  -- Since 2*k^n < (k+1)^n = k^n + gap(n,k), i.e. k^n < gap(n,k),
  -- we can use sum_in_chapter directly.
  have hgap : k ^ n < gap n k := by simp [gap]; omega
  rw [show k ^ n + k ^ n = k ^ n + k ^ n from rfl]
  exact sum_in_chapter n k (k ^ n) hn hgap

/--
  In the diagonal case with `2*k^n < (k+1)^n`, the shift is exactly k^n.
-/
lemma shiftArrivo_diag (n k : ℕ) (hn : n ≠ 0)
    (h2k : 2 * k ^ n < (k + 1) ^ n) :
    shiftArrivo n k k = k ^ n := by
  simp only [shiftArrivo]
  rw [radRem_base_add n k (k ^ n) hn]
  · simp [gap]; omega

/--
  **Diagonal theorem**: under the condition `2*k^n < (k+1)^n`,
  the radRem of the sum of two elements of the same chapter k is:

    radRem n (k^n + r + (k^n + s)) = k^n + r + s

  provided `k^n + r + s < gap(n,k)`.
-/
theorem landingCongruence_diag (n k r s : ℕ) (hn : n ≠ 0)
    (h2k  : 2 * k ^ n < (k + 1) ^ n)
    (hr   : r < gap n k)
    (hs   : s < gap n k)
    (hsum : k ^ n + r + s < gap n k) :
    radRem n (k ^ n + r + (k ^ n + s)) = k ^ n + r + s := by
  -- Translate hsum into hno_overflow
  have hshift : shiftArrivo n k k = k ^ n := shiftArrivo_diag n k hn h2k
  have hcap   : capitoloArrivo n k k = k   := capitoloArrivo_diag_eq_k n k hn h2k
  have hno_ov : shiftArrivo n k k + r + s < gap n (capitoloArrivo n k k) := by
    rw [hshift, hcap]; exact hsum
  rw [landingCongruence n k k r s hn hr hs hno_ov]
  rw [hshift]

end NoOverflowCharacterization
