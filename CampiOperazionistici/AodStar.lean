/-
  AodStar.lean
  Aod★ — The Universal Radical Quotient
  Campi Operazionistici — maximum over all degrees ≥ 2
  Author: Alessandro Sgarbi — 2026-03-04
  Paper: §20 (Universal Radical Quotient Aod★)

  References:
  - main paper (`main.pdf`)        — complete mathematical specification
  - `CampiOperazionistici.lean`    — irootN, radRem, isPerfectPower
  - `aoddepth.lean`                — pattern for depthStar
-/

import CampiOperazionistici.CampiOperazionistici
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

open CampiOperazionistici

namespace AodStar

/-!
# Aod★ — The Universal Operational Field

**Key idea.** Instead of fixing the degree `n`, `mpp(a)` is the *largest*
perfect power of *any* degree ≥ 2 that does not exceed `a`. The remainder
`r★(a) = a - mpp(a)` projects every natural number onto its "distance from the nearest PP".

## Comparison with the other structures

| Structure | Granularity | Class [0] |
|-----------|---------|-----------|
| Aod_n     | fixed degree n | n-th powers |
| Aod∞      | analytically fine (almost singletons) | strong zeros = 0 and 1 |
| **Aod★**  | coarser | **all** perfect powers |

## File structure

1. `isPPAny`       — perfect power of some degree ≥ 2
2. `mpp`           — largest lower perfect power (fuel-based, computable)
3. `radRemStar`    — universal radical remainder; Aod★ equivalence
4. T1              — otherness: r★(a) ≠ a for a ≥ 2
5. T2              — zeros: r★(a) = 0 ↔ isPPAny a
6. `depthStar`     — eval depth (fuel-based, analogue of `aodDepth`)
7. T★.depth.1      — PPs have depth★ = 1
8. Recurrence      — r★(PP+r) = r when no PP falls in the chapter
9. C★.depth.last   — depth of last stellar element (proved, `depthStar_lastElem`)
10. Conjectures    — C★.depth.asymp, C★.depth.jump (no sorry; stated, not formalised)
-/

-- ================================================================
-- § 1. Universal Perfect Powers
-- ================================================================

/-- `a` is a perfect power of some degree ≥ 2: `∃ k n, 2 ≤ n ∧ k^n = a`. -/
def isPPAny (a : ℕ) : Prop := ∃ k n : ℕ, 2 ≤ n ∧ k ^ n = a

@[simp] lemma isPPAny_zero : isPPAny 0 := ⟨0, 2, le_refl _, by norm_num⟩
@[simp] lemma isPPAny_one  : isPPAny 1 := ⟨1, 2, le_refl _, by norm_num⟩

lemma isPPAny_of_pow (k n : ℕ) (hn : 2 ≤ n) : isPPAny (k ^ n) := ⟨k, n, hn, rfl⟩

-- (computational checks after the definition of mpp)

-- ================================================================
-- § 2. Largest Lower Perfect Power
-- ================================================================

/-!
### 2.1 Fuel-based definition of `mppAux`

`mppAux a fuel` = max of `{(irootN n a)^n | 2 ≤ n ≤ fuel}` (0 if fuel < 2).
`mpp a = mppAux a (a + 2)`: the fuel `a + 2` covers all relevant degrees
(for n > a, k ≥ 2 would give k^n > a, so only k = 1 contributes, with 1).
-/

private def mppAux (a : ℕ) : ℕ → ℕ
  | 0     => 0
  | 1     => 0
  | n + 2 => max ((irootN (n + 2) a) ^ (n + 2)) (mppAux a (n + 1))

/-- `mpp a` = largest perfect power of degree ≥ 2 that is ≤ a.
    Convention: mpp 0 = 0 (no positive PP ≤ 0). -/
def mpp (a : ℕ) : ℕ := mppAux a (a + 2)

-- Computational checks
#eval mpp 0   -- 0
#eval mpp 1   -- 1  (1 = 1²)
#eval mpp 4   -- 4  (4 = 2²)
#eval mpp 8   -- 8  (8 = 2³)
#eval mpp 9   -- 9  (9 = 3²)
#eval mpp 10  -- 9  (9 = 3² > 8 = 2³)
#eval mpp 28  -- 27 (27 = 3³ > 25 = 5²)
#eval mpp 35  -- 32 (32 = 2⁵ > 27 = 3³)
#eval mpp 36  -- 36 (36 = 6²)

-- ================================================================
-- § 2b. Lemmas on mppAux
-- ================================================================

/-- mppAux is ≤ a: every candidate (irootN n a)^n is ≤ a. -/
private lemma mppAux_le_self (a : ℕ) : ∀ fuel, mppAux a fuel ≤ a := by
  intro fuel
  induction fuel with
  | zero => simp [mppAux]
  | succ m ih =>
    cases m with
    | zero => simp [mppAux]
    | succ k =>
      show max ((irootN (k + 2) a) ^ (k + 2)) (mppAux a (k + 1)) ≤ a
      exact max_le (irootN_pow_le (k + 2) a (by omega)) ih

/-- mppAux is monotone in the fuel. -/
private lemma mppAux_mono_fuel (a : ℕ) : ∀ fuel, mppAux a fuel ≤ mppAux a (fuel + 1) := by
  intro fuel
  induction fuel with
  | zero => simp [mppAux]
  | succ m =>
    cases m with
    | zero => simp only [mppAux]; exact Nat.le_max_right _ _
    | succ k =>
      show mppAux a (k + 2) ≤ max ((irootN (k + 3) a) ^ (k + 3)) (mppAux a (k + 2))
      exact Nat.le_max_right _ _

/-- Key lemma: for 2 ≤ n ≤ fuel, we have (irootN n a)^n ≤ mppAux a fuel. -/
private lemma mppAux_covers (a : ℕ) : ∀ fuel n : ℕ, 2 ≤ n → n ≤ fuel →
    (irootN n a) ^ n ≤ mppAux a fuel := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ m ih =>
    intro n hn hnm
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · -- n ≤ m: by IH and monotonicity
      exact Nat.le_trans (ih n hn (Nat.lt_succ_iff.mp hlt)) (mppAux_mono_fuel a m)
    · -- n = m + 1 (since n ≤ m+1 and n > m)
      have heq : n = m + 1 := by omega
      subst heq
      -- m + 1 ≥ 2 → m ≥ 1 → write m = k + 1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      -- goal: (irootN (k+2) a)^(k+2) ≤ mppAux a (k+2)
      simp only [mppAux]
      exact Nat.le_max_left _ _

/-- n < 2^n for every n : ℕ (used for bounds on high degrees). -/
private lemma lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm]
    have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    linarith

/-- mppAux a (a+2) ≥ 1 for a ≥ 1 (1² = 1 ≤ a is always a candidate). -/
private lemma mppAux_pos (a : ℕ) (ha : 1 ≤ a) : 1 ≤ mppAux a (a + 2) := by
  have hcov : (irootN 2 a) ^ 2 ≤ mppAux a (a + 2) :=
    mppAux_covers a (a + 2) 2 (by omega) (by omega)
  have hrt : 1 ≤ irootN 2 a := irootN_pos 2 a (by norm_num) ha
  calc 1 ≤ (irootN 2 a) ^ 2 := Nat.one_le_pow 2 _ (by omega)
       _ ≤ mppAux a (a + 2)  := hcov

-- ================================================================
-- § 2c. Public properties of mpp
-- ================================================================

theorem mpp_le_self (a : ℕ) : mpp a ≤ a := mppAux_le_self a (a + 2)

theorem mpp_pos (a : ℕ) (ha : 1 ≤ a) : 1 ≤ mpp a := mppAux_pos a ha

/-- Maximality: every perfect power ≤ a is ≤ mpp a. -/
theorem isPPAny_le_mpp {a k n : ℕ} (hn : 2 ≤ n) (hkn : k ^ n ≤ a) : k ^ n ≤ mpp a := by
  unfold mpp
  by_cases hna : n ≤ a + 2
  · -- degree n covered by the fuel a + 2
    have hk_le : k ≤ irootN n a := by
      by_contra hc; push_neg at hc
      have hlt := irootN_lt_succ_pow n a (by omega)
      have : a < k ^ n := calc a < (irootN n a + 1) ^ n := hlt
               _ ≤ k ^ n := Nat.pow_le_pow_left hc n
      exact absurd this (not_lt.mpr hkn)
    exact Nat.le_trans (Nat.pow_le_pow_left hk_le n) (mppAux_covers a (a + 2) n hn hna)
  · -- n > a + 2: k ≤ 1 (otherwise k^n ≥ 2^n > n > a)
    push_neg at hna
    have hk1 : k ≤ 1 := by
      by_contra hc; push_neg at hc
      have h2k : 2 ≤ k := hc
      have h2n : 2 ^ n ≤ k ^ n := Nat.pow_le_pow_left h2k n
      have han : a < 2 ^ n := calc a < n   := by omega
               _ < 2 ^ n := lt_two_pow_self n
      linarith
    interval_cases k
    · -- k = 0: 0^n = 0 ≤ mppAux a (a+2)
      have : (0 : ℕ) ^ n = 0 := Nat.zero_pow (by omega : 0 < n)
      omega
    · -- k = 1: k^n = 1, and a ≥ 1 (from hkn: 1 ≤ a)
      simp only [one_pow]
      have ha : 1 ≤ a := by simpa using hkn
      exact mppAux_pos a ha

/-- mpp a is itself a perfect power (or 0).
    Proved via `mppAux_is_candidate`: the maximum is attained by an explicit
    candidate (irootN m a)^m, hence it is a perfect power of degree m ≥ 2. -/
-- Auxiliary lemma: mppAux a fuel is 0 or equal to (irootN m a)^m for some 2 ≤ m ≤ fuel.
private lemma mppAux_is_candidate (a : ℕ) :
    ∀ fuel, mppAux a fuel = 0 ∨
      ∃ m : ℕ, 2 ≤ m ∧ m ≤ fuel ∧ mppAux a fuel = (irootN m a) ^ m := by
  intro fuel
  induction fuel with
  | zero => left; simp [mppAux]
  | succ f ih =>
    cases f with
    | zero => left; simp [mppAux]
    | succ g =>
      -- fuel = g + 2, mppAux a (g+2) = max ((irootN (g+2) a)^(g+2)) (mppAux a (g+1))
      simp only [mppAux]
      rcases Nat.lt_or_ge ((irootN (g + 2) a) ^ (g + 2)) (mppAux a (g + 1)) with h | h
      · -- right branch dominates: mppAux a (g+1) > (irootN (g+2) a)^(g+2)
        rw [max_eq_right (Nat.le_of_lt h)]
        rcases ih with hiz | ⟨m, hm2, hmf, hmeq⟩
        · left; exact hiz
        · right; exact ⟨m, hm2, by omega, hmeq⟩
      · -- left branch dominates: (irootN (g+2) a)^(g+2) ≥ mppAux a (g+1)
        rw [max_eq_left h]
        right
        exact ⟨g + 2, by omega, le_refl _, rfl⟩

theorem mpp_isPPAny (a : ℕ) (ha : 1 ≤ a) : isPPAny (mpp a) := by
  -- The value mppAux a (a+2) is the max of finitely many (irootN n a)^n,
  -- each of which is an n-th perfect power. The maximum is attained
  -- by one of them; every (irootN n a)^n = k^n with k = irootN n a, n ≥ 2.
  unfold mpp
  rcases mppAux_is_candidate a (a + 2) with h0 | ⟨m, hm2, _, hmeq⟩
  · -- mppAux a (a+2) = 0, contradicts mppAux_pos
    exfalso
    have hpos := mppAux_pos a ha
    omega
  · -- mppAux a (a+2) = (irootN m a)^m for some m ≥ 2
    rw [hmeq]
    exact ⟨irootN m a, m, hm2, rfl⟩

-- ================================================================
-- § 3. Universal Radical Remainder and the Aod★ Structure
-- ================================================================

/-- `radRemStar a = a - mpp a`: distance from the nearest lower PP. -/
def radRemStar (a : ℕ) : ℕ := a - mpp a

-- Table of r★(a) for the first values (cf. §1.2 of the main paper)
#eval (List.range 37).map radRemStar
-- Expected: [0,0,1,2,0,1,2,3,0,0,1,2,3,4,5,6,0,1,2,3,4,5,6,7,8,0,1,0,1,2,3,4,0,1,2,3,0]

/-- Aod★ equivalence relation: a ≡★ b ↔ r★(a) = r★(b). -/
def aodStarEquiv (a b : ℕ) : Prop := radRemStar a = radRemStar b

instance aodStarSetoid : Setoid ℕ where
  r     := aodStarEquiv
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The quotient type Aod★ = ℕ / ≡★. -/
abbrev AodStarField := Quotient aodStarSetoid

-- Notation (mirroring [Aod n])
notation:50 a " ≡★ " b => aodStarEquiv a b

-- ================================================================
-- § 4. T1 — Universal Otherness
-- ================================================================

/-- T1: r★(a) < a for every a ≥ 1 (in particular r★(a) ≠ a for a ≥ 2). -/
theorem radRemStar_lt_self {a : ℕ} (ha : 1 ≤ a) : radRemStar a < a := by
  simp only [radRemStar]
  have hpos : 1 ≤ mpp a := mpp_pos a ha
  have hle  : mpp a ≤ a := mpp_le_self a
  omega

/-- T1 (otherness formulation): r★(a) ≠ a for a ≥ 2. -/
theorem radRemStar_ne_self {a : ℕ} (ha : 2 ≤ a) : radRemStar a ≠ a :=
  Nat.ne_of_lt (radRemStar_lt_self (by omega))

-- ================================================================
-- § 5. T2 — Characterization of the Zeros
-- ================================================================

/-- T2 (←): perfect powers are zeros of Aod★. -/
theorem radRemStar_zero_of_isPPAny {a : ℕ} (h : isPPAny a) : radRemStar a = 0 := by
  simp only [radRemStar]
  obtain ⟨k, n, hn, rfl⟩ := h
  have hmpp : k ^ n ≤ mpp (k ^ n) := isPPAny_le_mpp hn (le_refl _)
  have hle  : mpp (k ^ n) ≤ k ^ n := mpp_le_self _
  omega

/-- T2 (→): if r★(a) = 0 then a is a perfect power. -/
theorem isPPAny_of_radRemStar_zero {a : ℕ} (h : radRemStar a = 0) : isPPAny a := by
  simp only [radRemStar] at h
  have hle : mpp a ≤ a := mpp_le_self a
  have heq : a = mpp a := by omega
  cases Nat.eq_zero_or_pos a with
  | inl ha0 => subst ha0; exact isPPAny_zero
  | inr ha  => rw [heq]; exact mpp_isPPAny a ha

/-- T2 (biconditional): r★(a) = 0 ↔ isPPAny a. -/
theorem radRemStar_zero_iff {a : ℕ} : radRemStar a = 0 ↔ isPPAny a :=
  ⟨isPPAny_of_radRemStar_zero, radRemStar_zero_of_isPPAny⟩

-- Examples of classes
lemma radRemStar_sq (k : ℕ) : radRemStar (k ^ 2) = 0 :=
  radRemStar_zero_of_isPPAny (isPPAny_of_pow k 2 (by omega))

lemma radRemStar_cube (k : ℕ) : radRemStar (k ^ 3) = 0 :=
  radRemStar_zero_of_isPPAny (isPPAny_of_pow k 3 (by omega))

-- ================================================================
-- § 6. Eval Depth in Aod★ (depth★)
-- ================================================================

/-!
### 6.1 Fuel-based definition of depthStar

Exact analogue of `aodDepth` in `aoddepth.lean`, with `radRemStar` in place
of `radRem n`. Termination guaranteed by `radRemStar_lt_self` (T1).
-/

private def depthStarGo : ℕ → ℕ → ℕ
  | 0,     _   => 0
  | _,     0   => 0
  | f + 1, a   => 1 + depthStarGo f (radRemStar a)

/-- `depthStar a` = length of the chain a → r★(a) → r★(r★(a)) → ⋯ → 0. -/
def depthStar (a : ℕ) : ℕ := depthStarGo a a

-- Computational chains (cf. §10.2 of the main paper)
#eval depthStar 0    -- 0
#eval depthStar 1    -- 1   (1 → 0)
#eval depthStar 2    -- 2   (2 → 1 → 0)
#eval depthStar 3    -- 3   (3 → 2 → 1 → 0)
#eval depthStar 4    -- 1   (4 = 2² → 0)
#eval depthStar 7    -- 4   (7 → 3 → 2 → 1 → 0)
#eval depthStar 8    -- 1   (8 = 2³ → 0)
#eval depthStar 9    -- 1   (9 = 3² → 0)
#eval depthStar 13   -- 2   (13 → 4 → 0)
#eval depthStar 23   -- 5   (23 → 7 → 3 → 2 → 1 → 0)
#eval depthStar 24   -- 2   (24 → 8 → 0)
#eval depthStar 27   -- 1   (27 = 3³ → 0)

-- Distribution over [1, 30]: (depth, count)
#eval (List.range 30).map (fun a => (a + 1, depthStar (a + 1)))

-- ================================================================
-- § 6b. Fuel-irrelevance lemmas for depthStar
-- ================================================================

private lemma depthStarGo_mono_fuel :
    ∀ (f a : ℕ), a ≤ f → ∀ k, depthStarGo f a = depthStarGo (f + k) a := by
  intro f
  induction f with
  | zero =>
    intro a ha k
    have : a = 0 := Nat.eq_zero_of_le_zero ha
    subst this
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ m ih =>
    intro a ha k
    cases a with
    | zero => simp [depthStarGo]
    | succ a' =>
      have hd : radRemStar (a' + 1) ≤ m := by
        have := radRemStar_lt_self (a := a' + 1) (by omega)
        omega
      have hrw : m + 1 + k = m + k + 1 := by omega
      rw [hrw]
      simp only [depthStarGo]
      congr 1
      exact ih (radRemStar (a' + 1)) hd k

private lemma depthStarGo_fuel_irrel (f a : ℕ) (h : a ≤ f) :
    depthStarGo f a = depthStarGo a a := by
  have : f = a + (f - a) := by omega
  rw [this]
  exact (depthStarGo_mono_fuel a a le_rfl (f - a)).symm

@[simp] lemma depthStar_zero : depthStar 0 = 0 := rfl

lemma depthStar_succ (a : ℕ) (ha : a ≠ 0) :
    depthStar a = 1 + depthStar (radRemStar a) := by
  cases a with
  | zero => exact absurd rfl ha
  | succ a' =>
    show depthStarGo (a' + 1) (a' + 1) =
         1 + depthStarGo (radRemStar (a' + 1)) (radRemStar (a' + 1))
    show 1 + depthStarGo a' (radRemStar (a' + 1)) =
         1 + depthStarGo (radRemStar (a' + 1)) (radRemStar (a' + 1))
    congr 1
    apply depthStarGo_fuel_irrel
    have := radRemStar_lt_self (a := a' + 1) (by omega)
    omega

-- ================================================================
-- § 7. T★.depth.1 — Perfect Powers have depth★ = 1
-- ================================================================

/-- T★.depth.1: every perfect power ≥ 1 has depth★ = 1.
    Exact analogue of `aodDepth_perfect_power` in `aoddepth.lean`. -/
theorem depthStar_isPPAny {a : ℕ} (hPP : isPPAny a) (ha : 1 ≤ a) :
    depthStar a = 1 := by
  have hne : a ≠ 0 := by omega
  rw [depthStar_succ a hne, radRemStar_zero_of_isPPAny hPP]
  simp [depthStar_zero]

/-- Corollary: depth★(k^n) = 1 for n ≥ 2, k ≥ 1. -/
theorem depthStar_pow {k n : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    depthStar (k ^ n) = 1 :=
  depthStar_isPPAny (isPPAny_of_pow k n hn) (Nat.one_le_pow n k (by omega))

-- ================================================================
-- § 8. Chapter Recurrence
-- ================================================================

/-!
### 8.1 Structure of the stellar chapters C★_k

**Stellar chapter** C★_k = [PP_k, PP_{k+1}) where PP_k = ppAt k.

It is the partition between two consecutive zeros of r★, exactly as in Aod_n
the chapter k = [k^n, (k+1)^n) is the partition between two consecutive zeros of radRem_n.
The difference is that the zeros of r★ are *all* the PPs (of any degree ≥ 2),
not just the powers of a single degree n.

**Caution** — the concept of an *Aod_2 chapter* also appears in this file:
the interval [k², (k+1)²), i.e. the partition between two consecutive zeros of radRem_2.
An Aod_2 chapter may contain zero, one, or more stellar chapters C★_k
(depending on how many PPs of degree ≥ 3 fall in the interval).
Whenever [k², (k+1)²) is written, an Aod_2 chapter is meant, NOT a stellar one.

Unlike Aod_n, within a stellar chapter C★_k the local address
r = a - PP_k cannot be a PP (by definition), but computing
r★(PP_k + r) still requires an explicit condition on the absence of intermediate PPs.

The correct recurrence in the stellar chapter is conditional:
r★(PP_k + r) = r if and only if no PP falls strictly in (PP_k, PP_k + r].
-/

/-- Lemma: if `a` is a PP and no PP falls strictly in (a, a+r],
    then mpp(a+r) = a, hence r★(a+r) = r.
    Used for the recurrence within a stellar chapter C★.
    Requires `mpp_isPPAny` for the upper bound. -/
lemma radRemStar_of_chapter {a r : ℕ} (hPP : isPPAny a)
    (hr : ∀ p : ℕ, isPPAny p → p ≤ a + r → p ≤ a) :
    radRemStar (a + r) = r := by
  simp only [radRemStar]
  have hge : a ≤ mpp (a + r) := by
    obtain ⟨k, n, hn, rfl⟩ := hPP
    exact isPPAny_le_mpp hn (by omega)
  have hle : mpp (a + r) ≤ a := by
    have hle_ar : mpp (a + r) ≤ a + r := mpp_le_self (a + r)
    have hPP_mpp : isPPAny (mpp (a + r)) := by
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · -- r = 0: mpp a = a (from hge and mpp_le_self), so isPPAny (mpp a) = hPP
        simp only [Nat.add_zero]
        have hmpp_eq : mpp a = a :=
          Nat.le_antisymm (mpp_le_self a) (by simpa using hge)
        rw [hmpp_eq]; exact hPP
      · exact mpp_isPPAny (a + r) (by omega)
    exact hr (mpp (a + r)) hPP_mpp hle_ar
  omega

/-- Recurrence of depth★ in the stellar chapter C★: if no PP falls in (a, a+r],
    then depth★(a+r) = 1 + depth★(r). -/
theorem depthStar_recurrence {a r : ℕ} (hPP : isPPAny a) (ha : 1 ≤ a)
    (hr_bound : ∀ p : ℕ, isPPAny p → p ≤ a + r → p ≤ a) :
    depthStar (a + r) = 1 + depthStar r := by
  have hne : a + r ≠ 0 := by omega
  rw [depthStar_succ (a + r) hne, radRemStar_of_chapter hPP hr_bound]

-- ================================================================
-- § 9. T3 — Uniqueness of the Width-1 Stellar Chapter (Catalan/Mihailescu)
-- ================================================================

/-!
### T3 in Aod★

The Catalan–Mihailescu Theorem (2002) states that the only pair of consecutive
perfect powers (≥ 2) is (8, 9). In the language of Aod★: the only
stellar chapter C★_k with gapStar(k) = 1 is C★_2 = {8}.

This is the qualitative version; the complete formalization requires
access to `Nat.Coprime` and variants of the theorem already in Mathlib.
-/

/-- T3 (statement): the only positive consecutive PPs are 8 and 9.
    Depends on Mihailescu; formal statement with sorry. -/
theorem catalan_in_AodStar : ∀ p q : ℕ, isPPAny p → isPPAny q → 1 ≤ p → q = p + 1 →
    (p = 8 ∧ q = 9) := by
  sorry -- follows from Nat.sq_sub_sq / Mihailescu (not yet in standard Mathlib)

-- ================================================================
-- § 10. Depth★ Status Table and Open Conjectures (no sorry here)
-- ================================================================

/-!
### Depth★ status table (cf. §10.10 of the main paper)

| Code             | Statement                                              | Status        |
|------------------|--------------------------------------------------------|--------------|
| T★.depth.1       | a ∈ PP → depth★(a) = 1                                 | **Proved** |
| T★.depth.term    | depth★ is well-defined and finite                      | **Proved** |
| C★.depth.last    | depth★(PP_{k+1}−1) = 1 + depth★(gap★(k)−1)            | **Proved** (`depthStar_lastElem`, given address validity) |
| C★.depth.jump    | sup_k |Δ_k| = +∞                                       | Open       |
| C★.depth.asymp   | depth★(a) ~ c★ · log a with c₂ < c★ < c₃               | Open (revised) |
-/

-- C★.depth.last: the last element of the stellar chapter C★_k has depth★ = 1 + depth★(gap − 1).
-- Direct corollary of depthStar_recurrence (analogue of aodDepth_lastElem).
-- The last element of C★_k is PP_{k+1} − 1 = PP_k + (gapStar(k) − 1), with
-- valid address r = gapStar(k) − 1 (no PP falls in (PP_k, PP_{k+1}−1]).

/-- Last element of the stellar chapter C★_k: PP_{k+1} − 1 = PP_k + (gapStar(k) − 1). -/
def lastElemStar (pp_k gap_k : ℕ) : ℕ := pp_k + (gap_k - 1)

/-- C★.depth.last: depth★(PP_{k+1}−1) = 1 + depth★(gapStar(k)−1).
    Corollary of depthStar_recurrence: r = gapStar(k)−1 is a valid address
    in the stellar chapter C★_k, because PP_{k+1} = PP_k + gapStar(k) does not fall
    in (PP_k, PP_k + (gapStar(k)−1)].
    Exact analogue of `aodDepth_lastElem` in `aoddepth.lean`. -/
theorem depthStar_lastElem {pp_k gap_k : ℕ} (hPP : isPPAny pp_k) (hpp : 1 ≤ pp_k)
    (hval : ∀ p : ℕ, isPPAny p → p ≤ pp_k + (gap_k - 1) → p ≤ pp_k) :
    depthStar (pp_k + (gap_k - 1)) = 1 + depthStar (gap_k - 1) :=
  depthStar_recurrence hPP (by omega) hval

-- C★.depth.asymp: computational check shows c★ ≈ 0.38 on [10,2000],
-- significantly greater than c₂ ≈ 0.147. The original conjecture c★ < c₂
-- has been retracted (cf. §8 of the main paper). Revised conjecture:
-- c₂ < c★ < c₃ ≈ 0.452, with Aod★ in an intermediate position between Aod₂ and Aod₃.

-- Computational check of C★.depth.last on the first stellar chapters:
-- PP_• = [1, 4, 8, 9, 16, 25, 27, 32, 36, 49]
-- C★_0 = [1,4):   gapStar=3, last stellar=3,  depth★(3)=3,  1+depth★(2)=3 ✓
-- C★_1 = [4,8):   gapStar=4, last stellar=7,  depth★(7)=4,  1+depth★(3)=4 ✓
-- C★_2 = [8,9):   gapStar=1, last stellar=8,  depth★(8)=1,  1+depth★(0)=1 ✓ (Catalan!)
-- C★_3 = [9,16):  gapStar=7, last stellar=15, depth★(15)=?, 1+depth★(6)=?
-- Note: C★_3 = [9,16) coincides with the Aod_2 chapter [3²,4²) because there are no
--       PPs of degree ≥ 3 in the interval (9,16).
#eval (List.range 50).map (fun a => (a, depthStar a))

-- ================================================================
-- § 11. T★.depth.mono — Monotonicity within Equivalence Classes
-- ================================================================

/-!
### T★.depth.mono

If `a` and `b` have the same universal radical remainder (`radRemStar a = radRemStar b`),
then `depthStar a ≤ depthStar b` when `a ≤ b`.

**Strategy:** the proof is surprisingly direct. For `a = 0`, trivial.
For `a ≥ 1`: `depthStar_succ` reduces both sides to `1 + depthStar (radRemStar ·)`,
and since the two remainders are equal by hypothesis, we even obtain equality.
The case `a = 0, b ≥ 1` uses `depthStar_zero` and `depthStar_isPPAny`/`depthStar_succ`.

Note: the result is actually stronger than a bound — for `a, b ≥ 1` we have equality.
The inequality alone appears only for `a = 0`: `depthStar 0 = 0 ≤ depthStar b`.
-/

/-- T★.depth.mono: elements with the same remainder r★ have non-decreasing depth★.
    Analogue of `same_depth_same_address` in `aoddepth.lean`, but for Aod★.
    Actually for a,b ≥ 1 equality holds; the inequality is strictly
    necessary only for the case a = 0 (depth★(0) = 0 ≤ depth★(b) for b ≥ 1 with r★(b)=0). -/
theorem depthStar_mono_class {a b : ℕ} (hclass : radRemStar a = radRemStar b)
    (hab : a ≤ b) : depthStar a ≤ depthStar b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · -- a = 0: depthStar 0 = 0 ≤ depthStar b
    simp [depthStar_zero]
  · -- a ≥ 1, hence b ≥ 1
    have hb_pos : 0 < b := Nat.lt_of_lt_of_le ha_pos hab
    have ha_ne : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha_pos
    have hb_ne : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb_pos
    -- For a,b ≥ 1: depth★(a) = 1 + depth★(r★(a)) = 1 + depth★(r★(b)) = depth★(b)
    rw [depthStar_succ a ha_ne, depthStar_succ b hb_ne, hclass]

/-- Corollary: for a,b ≥ 1 with the same r★, depth★ is equal (not just ≤).
    This is the precise analogue of `same_depth_same_address` in `aoddepth.lean`. -/
theorem depthStar_eq_of_same_class {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hclass : radRemStar a = radRemStar b) : depthStar a = depthStar b := by
  have ha_ne : a ≠ 0 := by omega
  have hb_ne : b ≠ 0 := by omega
  rw [depthStar_succ a ha_ne, depthStar_succ b hb_ne, hclass]

-- ================================================================
-- § 12. mpp_mono — Monotonicity of mpp (helper for §13)
-- ================================================================

/-- mpp is non-decreasing monotone: a ≤ b → mpp a ≤ mpp b.
    Proof: mpp a is a PP ≤ a ≤ b, hence by isPPAny_le_mpp it is ≤ mpp b. -/
private lemma mpp_mono {a b : ℕ} (hab : a ≤ b) : mpp a ≤ mpp b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · -- a = 0: mpp 0 = 0 ≤ mpp b
    exact Nat.zero_le _
  · -- a ≥ 1: mpp a is a PP (by mpp_isPPAny) and mpp a ≤ a ≤ b
    have hPP : isPPAny (mpp a) := mpp_isPPAny a ha_pos
    have hle : mpp a ≤ b := Nat.le_trans (mpp_le_self a) hab
    obtain ⟨k, n, hn, hmeq⟩ := hPP
    rw [← hmeq]
    exact isPPAny_le_mpp hn (hmeq ▸ hle)

-- ================================================================
-- § 13. T★.depth.succ — Successor Bound
-- ================================================================

/-!
### T★.depth.succ

`depth★(a) ≤ depth★(a-1) + 1` for every `a ≥ 2`.

Proof strategy (by strong induction on `a`):
- **`a ∈ PP`**: `depth★(a) = 1 ≤ depth★(a-1) + 1`. Trivial.
- **`a ∉ PP`**: The key lemma `mpp_eq_of_not_pp` shows that `mpp(a) = mpp(a-1)`
  when `a ∉ PP` (because `mpp(a) < a`, hence `mpp(a) ≤ a-1`, hence
  `isPPAny_le_mpp` gives `mpp(a) ≤ mpp(a-1)`, and `mpp_mono` gives the other inequality).
  Thus `r★(a) = a - mpp(a) = r★(a-1) + 1`.
  - If `a-1 ∈ PP`: `mpp(a) = a-1`, `r★(a) = 1`, `depth★(a) = 1 + depth★(1) = 2`,
    `depth★(a-1) = 1`, hence `2 ≤ 2`. ✓
  - If `a-1 ∉ PP`: `depth★(a-1) = 1 + depth★(r★(a-1))` and `r★(a) = r★(a-1) + 1 < a`.
    By IH on `r★(a) < a`: `depth★(r★(a)) ≤ depth★(r★(a)-1) + 1 = depth★(r★(a-1)) + 1`.
    Hence `depth★(a) = 1 + depth★(r★(a)) ≤ 1 + depth★(r★(a-1)) + 1 = depth★(a-1) + 1`. ✓

Note: no global monotonicity of `depth★` is needed (which is false, e.g. depth★ 7 = 4 > 1 = depth★ 8).
The proof proceeds entirely by strong induction on `a`.
-/

/-- Key lemma: if `a ∉ PP` and `a ≥ 1`, then `mpp a = mpp (a - 1)`.
    Proof: `mpp(a)` is a PP with `mpp(a) ≤ a` and `mpp(a) ≠ a` (because `a ∉ PP`),
    hence `mpp(a) ≤ a-1`, and `isPPAny_le_mpp` gives `mpp(a) ≤ mpp(a-1)`.
    The opposite inequality comes from `mpp_mono` (given `a-1 ≤ a`). -/
private lemma mpp_eq_of_not_pp {a : ℕ} (ha : 1 ≤ a) (h : ¬ isPPAny a) :
    mpp a = mpp (a - 1) := by
  apply Nat.le_antisymm
  · -- mpp(a) ≤ mpp(a-1): mpp(a) is PP and mpp(a) ≤ a-1, hence ≤ mpp(a-1)
    have hlt : mpp a < a := by
      rcases Nat.lt_or_eq_of_le (mpp_le_self a) with h' | h'
      · exact h'
      · exact absurd (h' ▸ mpp_isPPAny a ha) h
    obtain ⟨k, n, hn, hmeq⟩ := mpp_isPPAny a ha
    rw [← hmeq]
    exact isPPAny_le_mpp hn (by omega)
  · -- mpp(a-1) ≤ mpp(a): mpp_mono on a-1 ≤ a
    exact mpp_mono (by omega)

/-- If `a ∉ PP` and `a ≥ 1`, then `radRemStar a = radRemStar (a - 1) + 1`.
    Follows from `mpp_eq_of_not_pp` and the fact that `mpp(a) ≤ a - 1 < a`. -/
private lemma radRemStar_succ_of_not_pp {a : ℕ} (ha : 1 ≤ a) (h : ¬ isPPAny a) :
    radRemStar a = radRemStar (a - 1) + 1 := by
  have hmeq : mpp a = mpp (a - 1) := mpp_eq_of_not_pp ha h
  have hlt : mpp a < a := by
    rcases Nat.lt_or_eq_of_le (mpp_le_self a) with h' | h'
    · exact h'
    · exact absurd (h' ▸ mpp_isPPAny a ha) h
  simp only [radRemStar, hmeq]
  have hle1 : mpp (a - 1) ≤ a - 1 := mpp_le_self _
  omega

/-- T★.depth.succ: depth★ does not grow by more than 1 per step.
    The "asymmetric sawtooth" structure: rises by at most 1, drops to 1 at PPs.
    Proof by strong induction; does not require global monotonicity of depth★. -/
theorem depthStar_succ_le {a : ℕ} (ha : 2 ≤ a) :
    depthStar a ≤ depthStar (a - 1) + 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih => ?_
  by_cases hPP : isPPAny a
  · -- Case a ∈ PP: depth★(a) = 1
    rw [depthStar_isPPAny hPP (by omega)]
    exact Nat.le_add_left 1 _
  · -- Case a ∉ PP: r★(a) = r★(a-1) + 1
    have ha1 : 1 ≤ a := by omega
    have hrr : radRemStar a = radRemStar (a - 1) + 1 :=
      radRemStar_succ_of_not_pp ha1 hPP
    -- depth★(a) = 1 + depth★(r★(a)) = 1 + depth★(r★(a-1) + 1)
    rw [depthStar_succ a (by omega), hrr]
    by_cases hPP' : isPPAny (a - 1)
    · -- Sub-case a-1 ∈ PP: r★(a-1) = 0, hence r★(a) = 1
      -- depth★(a-1) = 1; depth★(1) = 1; goal: 1 + depth★(1) ≤ 1 + 1
      have hrr' : radRemStar (a - 1) = 0 := radRemStar_zero_of_isPPAny hPP'
      rw [hrr', zero_add]
      rw [depthStar_isPPAny hPP' (by omega),
          depthStar_isPPAny isPPAny_one (by omega)]
    · -- Sub-case a-1 ∉ PP: depth★(a-1) = 1 + depth★(r★(a-1))
      -- goal: 1 + depth★(r★(a-1)+1) ≤ 1 + depth★(r★(a-1)) + 1
      -- ↔ depth★(r★(a-1)+1) ≤ depth★(r★(a-1)) + 1
      -- Apply IH to r★(a-1)+1 = r★(a) < a
      have ha1' : 2 ≤ a - 1 := by
        rcases Nat.eq_or_lt_of_le (show 1 ≤ a - 1 by omega) with h1 | h1
        · exact absurd (h1 ▸ isPPAny_one) hPP'
        · exact h1
      have hr_lt : radRemStar a < a := radRemStar_lt_self (by omega)
      have hr_bound : radRemStar (a - 1) + 1 < a := hrr ▸ hr_lt
      have hr_a1 : 2 ≤ radRemStar (a - 1) + 1 := by
        have : radRemStar (a - 1) ≠ 0 := by rwa [Ne, radRemStar_zero_iff]
        omega
      have hIH := ih (radRemStar (a - 1) + 1) hr_bound hr_a1
      simp only [show radRemStar (a - 1) + 1 - 1 = radRemStar (a - 1) from by omega] at hIH
      rw [depthStar_succ (a - 1) (by omega)]
      linarith

-- ================================================================
-- § 14. T★.depth.PP1 — Successor of Perfect Powers
-- ================================================================

/-!
### T★.depth.PP1

For every PP `p ≥ 1` with `p ≠ 8`: `depth★(p + 1) = 2`.

**Structure of the proof:**
1. `p + 1 ∉ PP` — from the Catalan–Mihailescu Theorem (already in `catalan_in_AodStar`)
2. `mpp(p+1) = p` — because p is the largest PP ≤ p+1 (p+1 is not a PP by point 1)
3. `r★(p+1) = 1` — from mpp(p+1) = p
4. `depth★(p+1) = 1 + depth★(1) = 1 + 1 = 2`

Point 1 depends on `catalan_in_AodStar` (sorry on Mihailescu), so the entire
proof inherits this sorry. All other steps are completely proved.
-/

/-- Auxiliary lemma: if p is a PP and p+1 is not a PP, then mpp(p+1) = p. -/
private lemma mpp_succ_of_pp_not_pp {p : ℕ} (hPP : isPPAny p) (hp : 1 ≤ p)
    (h_not : ¬ isPPAny (p + 1)) : mpp (p + 1) = p := by
  apply Nat.le_antisymm
  · -- mpp(p+1) ≤ p: mpp(p+1) is a PP (by mpp_isPPAny) and ≤ p+1 but ≠ p+1 (because p+1 ∉ PP)
    have hle : mpp (p + 1) ≤ p + 1 := mpp_le_self (p + 1)
    have hPP_mpp : isPPAny (mpp (p + 1)) := mpp_isPPAny (p + 1) (by omega)
    -- If mpp(p+1) = p+1 then isPPAny(p+1), contradiction
    by_contra hc; push_neg at hc
    have heq : mpp (p + 1) = p + 1 := by omega
    rw [heq] at hPP_mpp
    exact h_not hPP_mpp
  · -- p ≤ mpp(p+1): p is a PP and p ≤ p+1
    obtain ⟨k, n, hn, rfl⟩ := hPP
    exact isPPAny_le_mpp hn (Nat.le_succ _)

/-- T★.depth.PP1: every perfect power p ≥ 1, p ≠ 8, has depth★(p+1) = 2.
    Depends on `catalan_in_AodStar` (Mihailescu's Theorem; sorry).
    Sole exception: p = 8, for which p+1 = 9 ∈ PP → depth★(9) = 1.
    This exception is a "computational marker" of Mihailescu's theorem:
    the only pair of consecutive PPs ≥ 2 is (8, 9). -/
theorem depthStar_pp_succ {p : ℕ} (hPP : isPPAny p) (hp : 1 ≤ p) (hp8 : p ≠ 8) :
    depthStar (p + 1) = 2 := by
  -- Step 1: p + 1 ∉ PP (from Catalan–Mihailescu)
  have h_not_pp : ¬ isPPAny (p + 1) := by
    intro h_pp1
    -- catalan_in_AodStar: if p and p+1 are PPs with p ≥ 1, then p = 8 ∧ p+1 = 9
    rcases catalan_in_AodStar p (p + 1) hPP h_pp1 hp rfl with ⟨rfl, _⟩
    exact hp8 rfl
  -- Step 2: mpp(p+1) = p
  have hmpp : mpp (p + 1) = p := mpp_succ_of_pp_not_pp hPP hp h_not_pp
  -- Step 3: r★(p+1) = 1
  have hrr : radRemStar (p + 1) = 1 := by simp [radRemStar, hmpp]
  -- Step 4: depth★(p+1) = 1 + depth★(1) = 1 + 1 = 2
  rw [depthStar_succ (p + 1) (by omega), hrr,
      depthStar_isPPAny isPPAny_one (by omega)]

-- Computational verification of T★.depth.PP1:
-- For every PP p in [1, 100] with p ≠ 8: depth★(p+1) should be 2
-- isPPAnyBool: computable boolean test for isPPAny
private def isPPAnyBool (a : ℕ) : Bool :=
  (List.range (a + 1)).any fun k =>
    (List.range (a + 1)).any fun n =>
      n ≥ 2 && k ^ n == a

#eval (List.range 100).filterMap (fun i =>
  let p := i + 1
  if isPPAnyBool p && p ≠ 8 then some (p, depthStar (p + 1)) else none)

-- ================================================================
-- § 9. FourDiamond D3 — Algebraic identity of the universal defect
-- ================================================================

/-- **D3 (FourDiamond): Algebraic identity of the universal defect.**
    Defining D★(a,b) := r★(a+b) - r★(a) - r★(b)  (in ℤ), we have:
      D★(a,b) = mpp(a) + mpp(b) - mpp(a+b).
    The second equality is immediate from r★(x) = x - mpp(x):
      r★(a+b) - r★(a) - r★(b)
      = (a+b - mpp(a+b)) - (a - mpp a) - (b - mpp b)
      = mpp a + mpp b - mpp(a+b).
    -- Example: a=5, b=4: mpp 5=4, mpp 4=4, mpp 9=9;
    --   r★(9)-r★(5)-r★(4) = 0-1-0 = -1 = 4+4-9 = -1. ✓ -/
theorem defectStar_identity (a b : ℕ) :
    (radRemStar (a + b) : ℤ) - radRemStar a - radRemStar b =
    (mpp a : ℤ) + mpp b - mpp (a + b) := by
  have ha  : mpp a       ≤ a     := mpp_le_self a
  have hb  : mpp b       ≤ b     := mpp_le_self b
  have hab : mpp (a + b) ≤ a + b := mpp_le_self (a + b)
  simp only [radRemStar]
  zify [ha, hb, hab]
  ring

-- ================================================================
-- § 15. Enumeration of PP_• — ppAt, ppIndex, gapStar
-- ================================================================

/-!
### Enumeration of the sequence PP_•

PP_• = [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...]

- `ppAt k`    — the k-th PP (0-indexed): ppAt 0 = 1, ppAt 1 = 4, ...
- `ppIndex a` — position of `a` in PP_•: ppIndex 1 = 0, ppIndex 4 = 1, ...
- `gapStar k` — width of the stellar chapter C★_k: ppAt(k+1) - ppAt(k)
-/

/-- Boolean check for perfect powers ≥ 1.
    Note: `isPPAnyBool` (defined in §14) does not handle a = 1 because
    `List.range 2 = [0,1]` does not include n = 2; here the case a = 1 is made explicit. -/
private def isPPBool (a : ℕ) : Bool :=
  (a == 1) ||
  (List.range (a + 1)).any fun k =>
    (List.range (a + 1)).any fun n =>
      Nat.ble 2 n && k ^ n == a

/-- Fuel-based engine: `ppAtAux target current fuel`.
    Returns the `target`-th PP (0-indexed) in the sequence PP_• starting
    from `current`, using at most `fuel` steps of successive enumeration.
    Call invariant: current ≥ 1. -/
private def ppAtAux : ℕ → ℕ → ℕ → ℕ
  | _,      _,       0      => 0        -- fuel exhausted (fallback)
  | target, current, f + 1 =>
    if isPPBool current then
      if target == 0 then current       -- found the target-th PP
      else ppAtAux (target - 1) (current + 1) f
    else ppAtAux target (current + 1) f

/-- `ppAt k` = the k-th perfect power in PP_•, 0-indexed.
    PP_• = [1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...]
    Fuel k² + 3k + 200 guarantees coverage for practical values. -/
def ppAt (k : ℕ) : ℕ := ppAtAux k 1 (k * k + 3 * k + 200)

/-- `ppIndex a` = 0-indexed position of `a` in PP_•.
    Equivalently: |{p ∈ PP_• | p < a}|, i.e. number of PPs in [1, a).
    Convention: ppIndex 0 = 0, ppIndex 1 = 0. -/
def ppIndex (a : ℕ) : ℕ :=
  (List.range a).countP (fun x => x != 0 && isPPBool x)

/-- `gapStar k` = ppAt (k+1) - ppAt k: width of the k-th chapter★ in PP_•. -/
def gapStar (k : ℕ) : ℕ := ppAt (k + 1) - ppAt k

-- Computational checks
#eval (List.range 10).map ppAt
-- Expected: [1, 4, 8, 9, 16, 25, 27, 32, 36, 49]

#eval ppIndex 1   -- 0  (1 = ppAt 0, no PP in [1, 1) = ∅)
#eval ppIndex 4   -- 1  (4 = ppAt 1, 1 PP in [1, 4): {1})
#eval ppIndex 9   -- 3  (9 = ppAt 3, 3 PPs in [1, 9): {1, 4, 8})

#eval (List.range 9).map gapStar
-- Expected: [3, 4, 1, 7, 9, 2, 5, 4, 13]
-- Reading: 1→4=3, 4→8=4, 8→9=1 (Catalan!), 9→16=7, 16→25=9,
--          25→27=2, 27→32=5, 32→36=4, 36→49=13

-- ================================================================
-- § 16. Thm 3.4 — Conservation of the Total Gap under Interferences
-- ================================================================

/-!
### Thm 3.4: gapStar_conservation

**Terminology** (critical — two distinct scales):
- *Stellar chapter* C★_i = [ppAt i, ppAt(i+1)): the natural partition of Aod★,
  between two consecutive zeros of r★. It is the main concept of this file.
- *Aod_2 chapter* [k², (k+1)²): partition between two consecutive zeros of radRem_2.
  Here used ONLY as an external reference to measure the total width 2k+1.

**Scenario**: j^n is an *interference* in the Aod_2 chapter [k², (k+1)²),
that is k² < j^n < (k+1)² with n ≥ 2 (j^n is a PP of degree ≥ 3 between two squares).
This splits the Aod_2 chapter into two consecutive stellar chapters:
  C★_{ppIndex(k²)}  = [k², j^n)        ← first stellar chapter
  C★_{ppIndex(j^n)} = [j^n, (k+1)²)   ← second stellar chapter

**Statement**: the sum of the gapStars of the two stellar chapters equals the width
of the Aod_2 chapter that contains them:

  gapStar(ppIndex(k²)) + gapStar(ppIndex(j^n)) = (k+1)² − k² = 2k+1

**Strategy — telescoping sum over the stellar chapters**:
  gapStar(ppIndex(k²)) = width of C★_{ppIndex(k²)}  = j^n − k²
  gapStar(ppIndex(j^n)) = width of C★_{ppIndex(j^n)} = (k+1)² − j^n
  Sum = (k+1)² − k² = width of the Aod_2 chapter = 2k+1.

**General form**: first proved for any three consecutive PPs (pp₁ ≤ pp₂ ≤ pp₃)
— without reference to Aod_2 — then Thm 3.4 is the corollary with pp₁ = k², pp₂ = j^n,
pp₃ = (k+1)² and the algebraic identity (k+1)² − k² = 2k+1.

**Explicit hypotheses** (satisfied in the concrete application):
- `h_rt1, h_rt2` — roundtrip: ppAt(ppIndex(p)) = p for p = k², j^n
- `h_next1`      — j^n is the PP immediately following k² in PP_• (no PP in (k², j^n))
- `h_next2`      — (k+1)² is the PP immediately following j^n in PP_• (no PP in (j^n, (k+1)²))

**Remark on Catalan**: the case k = 2, j^n = 8 = 2³ is the ONLY Aod_2 chapter
with *exactly one* interference (by Mihailescu's theorem — the only pair of
consecutive PPs is (8,9)). The other Aod_2 chapters [k², (k+1)²) have zero interferences
or more than one (e.g. k=5: [25,36) contains both 27=3³ and 32=2⁵).
-/

/-- **General form**: for three consecutive PPs pp₁ ≤ pp₂ ≤ pp₃ in the sequence PP_•,
    the sum of the gapStars equals the difference of the endpoints.
    Proof: pure ℕ algebra — telescoping sum after the rewrites. -/
theorem gapStar_conservation_general (pp₁ pp₂ pp₃ : ℕ)
    (h12 : pp₁ ≤ pp₂) (h23 : pp₂ ≤ pp₃)
    (h_rt1   : ppAt (ppIndex pp₁) = pp₁)
    (h_rt2   : ppAt (ppIndex pp₂) = pp₂)
    (h_next1 : ppAt (ppIndex pp₁ + 1) = pp₂)
    (h_next2 : ppAt (ppIndex pp₂ + 1) = pp₃) :
    gapStar (ppIndex pp₁) + gapStar (ppIndex pp₂) = pp₃ - pp₁ := by
  simp only [gapStar]
  rw [h_next1, h_rt1, h_next2, h_rt2]
  -- Goal (ℕ): pp₂ - pp₁ + (pp₃ - pp₂) = pp₃ - pp₁
  -- Follows immediately from h12 : pp₁ ≤ pp₂ and h23 : pp₂ ≤ pp₃.
  omega

/-- **Thm 3.4 — Conservation of the total gap under interferences.**

    If j^n is an interference in the Aod_2 chapter [k², (k+1)²), the two stellar chapters
    C★_{ppIndex(k²)} = [k², j^n) and C★_{ppIndex(j^n)} = [j^n, (k+1)²) have gapStars
    that sum to the width of the Aod_2 chapter:

      gapStar(ppIndex(k²)) + gapStar(ppIndex(j^n)) = 2k+1

    Corollary of `gapStar_conservation_general` (telescoping form over the stellar chapters)
    via the algebraic identity (k+1)² − k² = 2k+1 of the Aod_2 chapter. -/
theorem gapStar_conservation (k j n : ℕ) (_hn : 2 ≤ n)
    (hkj  : k ^ 2 ≤ j ^ n) (hjk  : j ^ n ≤ (k + 1) ^ 2)
    (h_rt1   : ppAt (ppIndex (k ^ 2)) = k ^ 2)
    (h_rt2   : ppAt (ppIndex (j ^ n)) = j ^ n)
    (h_next1 : ppAt (ppIndex (k ^ 2) + 1) = j ^ n)
    (h_next2 : ppAt (ppIndex (j ^ n) + 1) = (k + 1) ^ 2) :
    gapStar (ppIndex (k ^ 2)) + gapStar (ppIndex (j ^ n)) = 2 * k + 1 := by
  have hgen := gapStar_conservation_general
    (k ^ 2) (j ^ n) ((k + 1) ^ 2) hkj hjk h_rt1 h_rt2 h_next1 h_next2
  -- hgen : gapStar ... = (k+1)^2 - k^2
  -- It remains to show (k+1)^2 - k^2 = 2k+1 in ℕ
  have hring : k ^ 2 + (2 * k + 1) = (k + 1) ^ 2 := by ring
  omega

-- Computational verification: k=2, interference j^n = 2³ = 8 in the Aod_2 chapter [4, 9).
-- The two stellar chapters generated are C★_1 = [4,8) and C★_2 = [8,9).
-- gapStar(ppIndex 4) + gapStar(ppIndex 8)
-- = gapStar 1              + gapStar 2
-- = width(C★_1)            + width(C★_2)
-- = (ppAt 2 - ppAt 1)      + (ppAt 3 - ppAt 2)
-- = (8 - 4)                + (9 - 8)
-- = 4                      + 1
-- = 5 = 2·2+1 = width of the Aod_2 chapter [4,9) ✓  (Catalan case!)
#eval gapStar (ppIndex (2 ^ 2)) + gapStar (ppIndex (2 ^ 3))   -- 5

end AodStar
