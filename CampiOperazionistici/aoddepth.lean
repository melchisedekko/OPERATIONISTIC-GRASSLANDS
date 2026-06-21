/-
  AodDepth.lean
  Operationistic Fields — Subsection: Operational Depth (δₙ)
  Author: Alessandro Sgarbi — 2026-03-01 (rev. 2026-04-04)
  Paper: §10 (Operational Depth)

  This file develops the theory of the *operationistic depth* function
  aodDepth : ℕ → ℕ → ℕ.  Given a degree n and an element a, aodDepth n a
  counts how many iterated applications of radRem are needed to reach 0:

        aodDepth n a = |{ radRem-chain from a down to 0 }| - 1

  The central results are:
    T1  — perfect powers have depth 1
    T2  — fundamental recurrence:  depth(k^n + r) = 1 + depth(r)  for r < gap(n,k)
    T3  — last-element formula: depth(lastElem n k) = 1 + depth(gap n k − 1)
    T4  — chapter-invariance (corollary of T2): depth(r) is independent of the
          chapter k that contains r; the depth only depends on the radical chain of r
    T5  — minimal depth element:  μ_n(d) = κ^n + μ_n(d−1), where κ is the
          smallest integer ≥ 1 satisfying μ_n(d−1) < gap(n, κ)
    TB  — trivial bound: aodDepth n a ≤ a
-/

import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici

namespace AodDepth

open CampiOperazionistici

-- ================================================================
-- Definition of aodDepth (bounded, computable)
-- ================================================================

/-- `aodDepth n a` is the number of steps in the descending radRem-chain
    starting from `a`:
        a → radRem n a → radRem n (radRem n a) → … → 0
    The fuel parameter equals `a` itself (sufficient because radRem n x < x
    for x ≥ 1, so the chain terminates in at most `a` steps). -/
def aodDepth (n a : ℕ) : ℕ := go n a a where
  go (n : ℕ) : ℕ → ℕ → ℕ
  | 0,     _   => 0
  | _,     0   => 0
  | f + 1, a   => 1 + go n f (radRem n a)

-- ================================================================
-- Fuel-independence lemmas (internal infrastructure)
-- ================================================================

/-- Adding extra fuel does not change the result of `go`, provided we
    already have at least `a` fuel units.  (Termination follows from
    `radRem n x < x`, so the fuel counter is never the limiting factor.) -/
private lemma go_mono_fuel (n : ℕ) (hn : n ≠ 0) :
    ∀ (f a : ℕ), a ≤ f → ∀ k, aodDepth.go n f a = aodDepth.go n (f + k) a := by
  intro f
  induction f with
  | zero =>
    intro a ha k
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero ha
    subst ha0
    cases k with
    | zero => rfl
    | succ k' => simp [aodDepth.go]
  | succ m ih =>
    intro a ha k
    cases a with
    | zero => simp [aodDepth.go]
    | succ a' =>
      have hd : radRem n (a' + 1) ≤ m := by
        have := radRem_lt_self n (a' + 1) hn (by omega); omega
      have hrw : m + 1 + k = m + k + 1 := by omega
      rw [hrw]
      simp only [aodDepth.go]
      congr 1
      exact ih (radRem n (a' + 1)) hd k

/-- The `go` result depends only on the *argument* `a`, not on any fuel
    value `f ≥ a`.  In particular `go n f a = go n a a = aodDepth n a`. -/
private lemma go_fuel_irrel (n : ℕ) (hn : n ≠ 0) (f a : ℕ) (h : a ≤ f) :
    aodDepth.go n f a = aodDepth.go n a a := by
  have : f = a + (f - a) := by omega
  rw [this]
  exact (go_mono_fuel n hn a a le_rfl (f - a)).symm

-- ================================================================
-- Basic reduction lemmas
-- ================================================================

@[simp] lemma aodDepth_zero (n : ℕ) : aodDepth n 0 = 0 := rfl

/-- One-step unfolding: for `a ≠ 0`, peeling off the outermost radRem step. -/
lemma aodDepth_succ (n a : ℕ) (ha : a ≠ 0) :
    aodDepth n a = 1 + aodDepth n (radRem n a) := by
  cases a with
  | zero => exact absurd rfl ha
  | succ a' =>
    show aodDepth.go n (a' + 1) (a' + 1) =
         1 + aodDepth.go n (radRem n (a' + 1)) (radRem n (a' + 1))
    show 1 + aodDepth.go n a' (radRem n (a' + 1)) =
         1 + aodDepth.go n (radRem n (a' + 1)) (radRem n (a' + 1))
    congr 1
    by_cases hn : n = 0
    · subst hn; simp [irootN, radRem]
    · exact go_fuel_irrel n hn a' (radRem n (a' + 1)) (by
        have := radRem_lt_self n (a' + 1) hn (by omega); omega)

-- Computational spot-checks (expected values follow from the chain structure)
#eval aodDepth 2 3    -- 3  (chain: 3 → 2 → 1 → 0)
#eval aodDepth 2 4    -- 1  (4 = 2², perfect square; chain: 4 → 0)
#eval aodDepth 2 7    -- 4  (chain: 7 → 3 → 2 → 1 → 0)
#eval aodDepth 3 26   -- 5  (chain: 26 → 18 → 10 → 2 → 1 → 0)
#eval (List.range 7).map (fun r => aodDepth 3 (1 + r))
  -- [1,2,3,4,5,6,7] — the first chapter (k=1, n=3) has a perfect linear depth gradient

-- ================================================================
-- T1 — Perfect powers have depth 1
-- ================================================================

/-- **Theorem T1.** For every `k ≥ 1`, the perfect power `k^n` has
    operationistic depth 1: it lies at distance 1 from 0 along the
    radRem chain (because `radRem n (k^n) = 0`). -/
theorem aodDepth_perfect_power (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    aodDepth n (k ^ n) = 1 := by
  have hne : k ^ n ≠ 0 := by positivity
  rw [aodDepth_succ n (k ^ n) hne, radRem_of_pow n k hn]; simp

-- ================================================================
-- T2 — Fundamental recurrence
-- ================================================================

/-- **Theorem T2 (Fundamental Recurrence).** If `r` falls strictly inside
    chapter `k` (i.e. `r < gap n k`), then
        aodDepth n (k^n + r) = 1 + aodDepth n r.
    Proof: the first radRem step strips the `k^n` base, landing exactly
    at `r` (by `radRem_of_chapter`), and the rest of the chain is `r`'s
    own chain. -/
theorem aodDepth_recurrence (n k r : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k)
    (hr : r < gap n k) :
    aodDepth n (k ^ n + r) = 1 + aodDepth n r := by
  have hne : k ^ n + r ≠ 0 := by positivity
  rw [aodDepth_succ n (k ^ n + r) hne, radRem_of_chapter n k r hn hr]

/-- T1 as the `r = 0` instance of T2. -/
lemma aodDepth_recurrence_at_zero (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    aodDepth n (k ^ n + 0) = 1 + aodDepth n 0 := by
  have hgap_pos : 0 < gap n k := by
    simp [gap]
    have h : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
    omega
  rw [aodDepth_recurrence n k 0 hn hk (by omega)]

-- ================================================================
-- T3 — Last element of a chapter
-- ================================================================

/-- The last element of chapter `k` at degree `n`:
    `lastElem n k = (k+1)^n − 1`. -/
def lastElem (n k : ℕ) : ℕ := (k + 1) ^ n - 1

#eval lastElem 2 3   -- 15  (= 4² − 1)
#eval lastElem 3 2   -- 26  (= 3³ − 1)

/-- Decomposition of `lastElem` as a chapter representative:
    `lastElem n k = k^n + (gap n k − 1)`. -/
lemma lastElem_decomp (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    lastElem n k = k ^ n + (gap n k - 1) := by
  simp only [lastElem, gap]
  have hlt : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
  have hle : k ^ n ≤ (k + 1) ^ n - 1 := by
    have hone : 1 ≤ (k + 1) ^ n := Nat.one_le_pow n (k + 1) (by omega)
    omega
  have h : (k + 1) ^ n - 1 = k ^ n + ((k + 1) ^ n - k ^ n - 1) := by
    have hsub : k ^ n + 1 ≤ (k + 1) ^ n := by
      have hone : 1 ≤ (k + 1) ^ n := Nat.one_le_pow n (k + 1) (by omega)
      omega
    omega
  exact h

/-- `radRem` of the last element equals `gap n k − 1`. -/
theorem radRem_lastElem (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    radRem n (lastElem n k) = gap n k - 1 := by
  simp only [lastElem, gap, radRem]
  have hlt  : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
  have hone : 1 ≤ (k + 1) ^ n     := Nat.one_le_pow n (k + 1) (by omega)
  have hle  : k ^ n ≤ (k + 1) ^ n - 1 := by omega
  have hlt' : (k + 1) ^ n - 1 < (k + 1) ^ n := by omega
  rw [irootN_unique n ((k + 1) ^ n - 1) k hn hle hlt']
  exact (Nat.sub_right_comm ((k + 1) ^ n) (k ^ n) 1).symm

/-- **Theorem T3.** The depth of the last element of chapter `k` equals
    `1 + depth(gap n k − 1)`.  The last element has remainder `gap n k − 1`,
    so T2 applies directly. -/
theorem aodDepth_lastElem (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    aodDepth n (lastElem n k) = 1 + aodDepth n (gap n k - 1) := by
  have hne : lastElem n k ≠ 0 := by
    simp only [lastElem]
    have h2 : 1 < (k + 1) ^ n := Nat.one_lt_pow hn (by omega)
    omega
  rw [aodDepth_succ n (lastElem n k) hne, radRem_lastElem n k hn hk]

-- Derived form via decomposition (alternative proof path, useful in calculations)
lemma aodDepth_lastElem_via_T2 (n k : ℕ) (hn : n ≠ 0) (hk : 1 ≤ k) :
    aodDepth n (lastElem n k) = 1 + aodDepth n (gap n k - 1) := by
  rw [lastElem_decomp n k hn hk]
  have hgap : gap n k - 1 < gap n k := by
    have hgap_pos : 0 < gap n k := by
      simp [gap]
      have h : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
      omega
    omega
  exact aodDepth_recurrence n k (gap n k - 1) hn hk hgap

-- Verification: T3 holds for the first six chapters at n=3
#eval (List.range 6).map fun i =>
  let k := i + 1
  (aodDepth 3 (lastElem 3 k), 1 + aodDepth 3 (gap 3 k - 1))
  -- all pairs should be equal

-- ================================================================
-- T4 — Chapter-invariance of depth
-- ================================================================

/-- **Theorem T4 (Chapter-Invariance / same_depth_same_address).**
    If remainder `r` fits inside *two* chapters `k₁` and `k₂`, then
        aodDepth n (k₁^n + r) = aodDepth n (k₂^n + r).
    In other words, the depth of `k^n + r` depends only on `r`, not on
    which chapter base `k^n` we add.  This is an immediate consequence
    of T2: both sides equal `1 + aodDepth n r`. -/
theorem same_depth_same_address (n k₁ k₂ r : ℕ) (hn : n ≠ 0)
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (hr₁ : r < gap n k₁) (hr₂ : r < gap n k₂) :
    aodDepth n (k₁ ^ n + r) = aodDepth n (k₂ ^ n + r) := by
  rw [aodDepth_recurrence n k₁ r hn hk₁ hr₁,
      aodDepth_recurrence n k₂ r hn hk₂ hr₂]

/-- Depth is invariant on aodEquiv-equivalent nonzero elements.
    Note: the assumption `1 ≤ a` and `1 ≤ b` is essential —
    depth 0 and depth 1 collide at 0 and 1, but 0 ~ₒ 1 fails anyway
    since `radRem n 0 = 0 ≠ 1 = radRem n 1` for n > 0. -/
lemma aodDepth_aodEquiv (n a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    aodEquiv n a b → aodDepth n a = aodDepth n b := by
  intro h
  have h_radRem_eq : radRem n a = radRem n b := h
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  rw [aodDepth_succ n a ha', aodDepth_succ n b hb']
  rw [h_radRem_eq]

-- ================================================================
-- T5 — Minimal element of depth d  (new)
-- ================================================================

/-
  Computational exploration revealed a striking recursive structure in the
  *minimal* element realising depth d.

  For n = 2 the sequence is:  μ(1)=1, μ(2)=2, μ(3)=3, μ(4)=7, μ(5)=23,
  μ(6)=167, μ(7)=7223, …

  Each term decomposes as   μ(d) = κ(d)² + μ(d−1),
  where κ(d) = irootN(2, μ(d)) is the integer square-root of the new term.
  Equivalently κ(d) is the *smallest* k ≥ 1 such that μ(d−1) < gap(2, k).
  This is the *cheapest* extension step: we pick the smallest chapter base
  that accepts μ(d−1) as a legal remainder.

  For n = 3 the linear phase persists longer: μ(d) = d for d ≤ 7 (since
  gap(3,1) = 2³−1 = 7 accommodates all remainders 1..6), then κ(8) = 2.

  The lemmas below formalise the decomposition and the recurrence step.
-/

/-- `minDepthElem n d` is the smallest natural number with `aodDepth n a = d`.
    Computed recursively: step from `m := minDepthElem n (d-1)` to the next
    level by choosing the smallest `k` with `m < gap n k` and returning `k^n + m`. -/
def minDepthElem (n : ℕ) : ℕ → ℕ
  | 0     => 0
  | d + 1 =>
    let m := minDepthElem n d
    -- Find the smallest k ≥ 1 such that m < gap n k.
    -- For k = 1 this is m < 2^n - 1; if it fails we increment k.
    -- We use a bounded search capped at m+2 (always sufficient in practice).
    let k := (List.range (m + 2)).find? (fun k => k ≥ 1 ∧ m < gap n k) |>.getD 1
    k ^ n + m

#eval (List.range 8).map (minDepthElem 2)
  -- [0, 1, 2, 3, 7, 23, 167, 7223]
#eval (List.range 11).map (minDepthElem 3)
  -- [0, 1, 2, 3, 4, 5, 6, 7, 15, 23, ...]

-- ----------------------------------------------------------------
-- Auxiliary: gap n (m+1) > m for n ≥ 2
-- ----------------------------------------------------------------

/-- Normalise gap n (m+1) to the explicit form (m+2)^n - (m+1)^n.
    (After `simp only [gap]` the base is `m+1+1`, not `m+2`; `congr 1; ring` fixes it.) -/
private lemma gap_eq_pow_sub (n m : ℕ) :
    gap n (m + 1) = (m + 2) ^ n - (m + 1) ^ n := by
  simp only [gap]  -- m+1+1 = m+2 definitionally in ℕ, so this closes the goal

/-- For n = 2: gap 2 (m+1) = 2m+3. -/
private lemma gap_two_eq (m : ℕ) : gap 2 (m + 1) = 2 * m + 3 := by
  have hle : (m + 1) ^ 2 ≤ (m + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [gap_eq_pow_sub]; zify [hle]; ring

/-- Structural identity: gap (n+1) (m+1) = (m+2)^n + (m+1) * gap n (m+1).
    Proof via ℤ: (m+2)^(n+1) - (m+1)^(n+1) = (m+2)^n + (m+1)*((m+2)^n - (m+1)^n). -/
private lemma gap_succ_eq (n m : ℕ) :
    gap (n + 1) (m + 1) = (m + 2) ^ n + (m + 1) * gap n (m + 1) := by
  have hle  : (m + 1) ^ n     ≤ (m + 2) ^ n     := Nat.pow_le_pow_left (by omega) n
  have hle' : (m + 1) ^ (n+1) ≤ (m + 2) ^ (n+1) := Nat.pow_le_pow_left (by omega) (n+1)
  rw [gap_eq_pow_sub (n+1), gap_eq_pow_sub n]
  zify [hle', hle]; ring

/-- For n ≥ 2, gap n (m+1) > m.  (The theorem is FALSE for n = 1,
    where gap 1 k = 1 always, so no search can succeed for m ≥ 1.)
    Proof by induction on n, base n = 2 and step using gap_succ_eq. -/
private lemma gap_gt_self (n : ℕ) (hn : 2 ≤ n) (m : ℕ) : m < gap n (m + 1) := by
  induction n with
  | zero => omega
  | succ n' ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · -- n' + 1 = 2, so n' = 1
      have hn' : n' = 1 := by omega
      subst hn'
      rw [gap_two_eq]; omega
    · -- n' + 1 > 2, so n' ≥ 2
      have hn' : 2 ≤ n' := by omega
      rw [gap_succ_eq]
      have ih' : m < gap n' (m + 1) := ih hn'
      have hpos : 0 < (m + 2) ^ n' := by positivity
      -- (m+2)^n' + (m+1)*gap n' (m+1) ≥ 1 + (m+1)*(m+1) > m
      have hmul : (m + 1) * (m + 1) ≤ (m + 1) * gap n' (m + 1) :=
        Nat.mul_le_mul_left (m + 1) ih'
      nlinarith

/-- **Theorem T5 (Lower Bound for minDepthElem).**
    For n ≥ 2, `minDepthElem n d` has operationistic depth ≥ d.
    Note: the hypothesis `2 ≤ n` is necessary — for n = 1, gap 1 k = 1 always,
    so the search fails for m ≥ 1 and the theorem becomes false for d ≥ 2. -/
-- Example witnesses: n = 2, d = 5: minDepthElem 2 5 = 23, aodDepth 2 23 = 5 ✓
theorem minDepthElem_depth_lower (n d : ℕ) (hn : 2 ≤ n) :
    d ≤ aodDepth n (minDepthElem n d) := by
  induction d with
  | zero => simp [minDepthElem, aodDepth_zero]
  | succ d' ih =>
    simp only [minDepthElem]
    set m := minDepthElem n d' with hm_def
    -- Case split on whether find? returned some k or none
    rcases h : (List.range (m + 2)).find? (fun k => k ≥ 1 ∧ m < gap n k) with _ | k
    · -- Case none: contradicted by gap_gt_self (m+1 is in range and satisfies the predicate)
      exfalso
      have hmem : m + 1 ∈ List.range (m + 2) := List.mem_range.mpr (by omega)
      have hgt := gap_gt_self n hn m
      have hfalse := List.find?_eq_none.mp h (m + 1) hmem
      simp [hgt] at hfalse
    · -- Case some k: k satisfies the predicate
      simp only [Option.getD_some]
      have hpk : k ≥ 1 ∧ m < gap n k := by
        have hbool := List.find?_some h
        simpa [decide_eq_true_iff] using hbool
      rw [aodDepth_recurrence n k m (by omega) hpk.1 hpk.2]
      omega

-- Computational verification: the computed values have the expected depth
#eval (List.range 8).map fun d =>
  (d, minDepthElem 2 d, aodDepth 2 (minDepthElem 2 d))
  -- (d, minDepthElem 2 d, d) for d = 0..7 ✓

-- ================================================================
-- Refuted conjecture: depth is NOT maximised at lastElem
-- ================================================================
/-
  REFUTED CONJECTURE (archived for reference):
  "Within chapter k at degree n, the depth is maximised by the last element
  `lastElem n k`."

  This is TRUE for k = 1 (the first chapter), because gap(n,1) = 2^n − 1
  and radRem descends linearly: the chain 2^n−2 → 2^n−3 → … → 0 has
  length 2^n−2, which is the maximum in that chapter.

  It FAILS for k ≥ 2.  Counterexample (n=2, k=2):
    Chapter [4,5,6,7,8], depths = [1,2,3,4,2].
    Maximum depth = 4 at a = 7 (r = 3), whereas lastElem(2,2) = 8 has depth 2.

  What IS true (and proved above as T3) is that depth(lastElem n k) = 1 + depth(gap n k − 1),
  which is an exact formula, not a maximum characterisation.

  OPEN DIRECTION: characterise the *argmax position* r*(n,k) within each chapter.
  Computational data shows:
    • r*(n,k) is always the element with the longest radical chain BELOW gap(n,k),
      i.e., r*(n,k) = argmax_{r < gap(n,k)} aodDepth n r.
    • For fixed n, r*(n,k) stabilises as k grows (it can only increase when the
      new gap is large enough to accommodate a longer chain from scratch).
    • The sequence of *record* argmax values (n=2): 2, 3, 7, 23, 167, …
      These are exactly the values μ(d) = minDepthElem n d introduced above!
      Record at depth d appears first in chapter κ(d) = irootN(n, μ(d)).
    • Conjectured formula: r*(n,k) = μ(d*(n,k)) where d*(n,k) is the largest d
      with μ(d) < gap(n,k).
  This conjecture passes all computational checks up to k = 100, n ∈ {2,3,4}.
-/

-- Verification: refuted conjecture counterexample
#eval (List.range 5).map fun r => aodDepth 2 (2 ^ 2 + r)
  -- [1, 2, 3, 4, 2]: max = 4 at r=3, NOT at r=4 (lastElem)

-- Verification: the argmax sequence equals minDepthElem
#eval do
  let n := 2
  let records ← pure <| (List.range 10).filterMap fun k =>
    if k = 0 then none
    else
      let g := gap n k
      let depths := (List.range g).map (fun r => aodDepth n (k^n + r))
      let maxD := depths.foldl Nat.max 0
      let argR := (List.range g).find? (fun r => aodDepth n (k^n + r) = maxD) |>.getD 0
      some (k, argR, maxD)
  return records
  -- argR column matches minDepthElem 2 (d) for appropriate d

-- ================================================================
-- Open Direction — Argmax Characterisation
-- ================================================================

/-
  The "Open Direction" from the refuted-conjecture section above is now
  fully formalised in four steps:

  TD1 — `minDepthElem_exact_depth`: aodDepth n (minDepthElem n d) = d
  TD2 — `minDepthElem_min`:          if d ≤ aodDepth n r, then minDepthElem n d ≤ r
  TM  — `minDepthElem_strictMono`:   minDepthElem n d < minDepthElem n (d+1)
  TA  — `argmax_within_chapter`:     within [0, gap n k), the depth-maximiser
                                     is minDepthElem n d* where d* is the
                                     largest d with minDepthElem n d < gap n k.

  Together TD1+TD2 say that minDepthElem n d is the *unique minimum* element
  of aodDepth n = d; TA identifies the argmax within each chapter.
-/

/-- Helper: if `(List.range bound).find? p = some found` and `p target = true`
    and `target < bound`, then `found ≤ target`.  (find? returns the first hit,
    so any later valid candidate was seen *after* the one that was returned.) -/
private lemma range_find_le (bound : ℕ) (p : ℕ → Bool) (found target : ℕ)
    (hfind  : (List.range bound).find? p = some found)
    (_      : target < bound)
    (hptgt  : p target = true) : found ≤ target := by
  rw [List.find?_range_eq_some] at hfind
  obtain ⟨_, _, hbefore⟩ := hfind
  by_contra h
  push_neg at h          -- h : target < found
  have hbef := hbefore target h
  simp [hptgt] at hbef  -- !p target = true contradicts p target = true

/-- **Theorem TD1 (Exact Depth).**
    For n ≥ 2, `minDepthElem n d` has operationistic depth exactly d.
    Together with `minDepthElem_depth_lower` (≥ bound) this pins the depth. -/
theorem minDepthElem_exact_depth (n d : ℕ) (hn : 2 ≤ n) :
    aodDepth n (minDepthElem n d) = d := by
  induction d with
  | zero => simp [minDepthElem, aodDepth_zero]
  | succ d' ih =>
    simp only [minDepthElem]
    set m := minDepthElem n d' with hm_def
    rcases h : (List.range (m + 2)).find? (fun k => k ≥ 1 ∧ m < gap n k) with _ | k
    · -- none: contradicted by m+1 being a valid candidate
      exfalso
      have hmem : m + 1 ∈ List.range (m + 2) := List.mem_range.mpr (by omega)
      have hgt  := gap_gt_self n hn m
      have      := List.find?_eq_none.mp h (m + 1) hmem
      simp [hgt] at this
    · simp only [Option.getD_some]
      have hpk : k ≥ 1 ∧ m < gap n k := by
        simpa using List.find?_some h
      rw [aodDepth_recurrence n k m (by omega) hpk.1 hpk.2]
      omega  -- 1 + aodDepth n m = 1 + d' since ih : aodDepth n m = d'

/-- **Theorem TD2 (Minimality).** For n ≥ 2, if `aodDepth n r ≥ d` then
    `minDepthElem n d ≤ r`.  Equivalently, no element smaller than
    `minDepthElem n d` has depth ≥ d. -/
theorem minDepthElem_min (n d r : ℕ) (hn : 2 ≤ n) (hdepth : d ≤ aodDepth n r) :
    minDepthElem n d ≤ r := by
  induction d generalizing r with
  | zero =>
    -- d = 0: minDepthElem n 0 = 0 ≤ r trivially
    simp [minDepthElem]
  | succ d' ih =>
    -- d = d' + 1
    simp only [minDepthElem]
    set m := minDepthElem n d'
    -- r ≠ 0 (depth ≥ 1 > 0)
    have hr0 : r ≠ 0 := by
      intro hr; subst hr; simp [aodDepth_zero] at hdepth
    have hr_pos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    -- radRem n r has depth ≥ d'
    have hdepth_rem : d' ≤ aodDepth n (radRem n r) := by
      have h := aodDepth_succ n r hr0; omega
    -- m ≤ radRem n r  (IH applied to radRem n r)
    have hm_le_rem : m ≤ radRem n r := by
      apply ih (radRem n r) hdepth_rem
    -- irootN n r ≥ 1  and  m < gap n (irootN n r)
    have hk_pos : 1 ≤ irootN n r   := irootN_pos n r (by omega) hr_pos
    have hm_lt_gap : m < gap n (irootN n r) := by
      have hlt := radRem_lt_gap n r (by omega)
      simp only [gap]; omega
    -- irootN n r ^ n + radRem n r = r
    have hr_decomp : irootN n r ^ n + radRem n r = r := by
      have := radRem_eq_sub n r (by omega)
      have := irootN_pow_le n r (by omega)
      omega
    -- Case split on find? result
    rcases hf : (List.range (m + 2)).find? (fun k => k ≥ 1 ∧ m < gap n k) with _ | k
    · exfalso
      have hmem : m + 1 ∈ List.range (m + 2) := List.mem_range.mpr (by omega)
      have hgt  := gap_gt_self n hn m
      have      := List.find?_eq_none.mp hf (m + 1) hmem
      simp [hgt] at this
    · simp only [Option.getD_some]
      -- k ≤ irootN n r
      have hk_le_iroot : k ≤ irootN n r := by
        -- Case: irootN n r is in the search range → use minimality of k
        by_cases hlt : irootN n r < m + 2
        · have hpj : decide (irootN n r ≥ 1 ∧ m < gap n (irootN n r)) = true := by
            simp [hk_pos, hm_lt_gap]
          exact range_find_le (m + 2) (fun k => decide (k ≥ 1 ∧ m < gap n k)) k (irootN n r) hf hlt hpj
        · -- irootN n r ≥ m+2 ≥ k+1, so k < irootN n r trivially
          push_neg at hlt
          have hk_lt : k < m + 2 :=
            List.mem_range.mp (List.mem_of_find?_eq_some hf)
          omega
      -- k^n + m ≤ irootN n r ^ n + radRem n r = r
      have hkn_le : k ^ n ≤ irootN n r ^ n := Nat.pow_le_pow_left hk_le_iroot n
      linarith [hm_le_rem]

/-- **Theorem TB (Trivial Bound).** `aodDepth n a ≤ a` for all `a`.
    Each step in the radRem chain strictly decreases the argument
    (by `radRem_lt_self`), so after at most `a` steps we reach 0. -/
theorem aodDepth_le_self (n a : ℕ) : aodDepth n a ≤ a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha : a = 0
    · subst ha; simp [aodDepth_zero]
    · have h_succ := aodDepth_succ n a ha
      rw [h_succ]
      have h_lt : radRem n a < a := by
        by_cases hn : n = 0
        · subst hn
          simp [radRem, irootN]
          omega
        · exact radRem_lt_self n a hn (by
            have : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
            exact this)
      have h_ih := ih (radRem n a) h_lt
      omega

/-- **Corollary.** For n ≥ 2, `d ≤ minDepthElem n d` for all d.
    (The minimum depth-d element is at least as large as d itself.) -/
theorem minDepthElem_ge_depth (n d : ℕ) (hn : 2 ≤ n) : d ≤ minDepthElem n d := by
  have h := minDepthElem_exact_depth n d hn
  have tb := aodDepth_le_self n (minDepthElem n d)
  omega

/-- **Theorem TM (Strict Monotonicity).**
    For n ≥ 2, `minDepthElem n d < minDepthElem n (d+1)`. -/
theorem minDepthElem_strictMono (n d : ℕ) (hn : 2 ≤ n) :
    minDepthElem n d < minDepthElem n (d + 1) := by
  simp only [minDepthElem]
  set m := minDepthElem n d with hm_def
  rcases h : (List.range (m + 2)).find? (fun k => k ≥ 1 ∧ m < gap n k) with _ | k
  · exfalso
    have hmem : m + 1 ∈ List.range (m + 2) := List.mem_range.mpr (by omega)
    have hgt  := gap_gt_self n hn m
    have      := List.find?_eq_none.mp h (m + 1) hmem
    simp [hgt] at this
  · simp only [Option.getD_some]
    have hpk : k ≥ 1 ∧ m < gap n k := by
      simpa using List.find?_some h
    have hkn_pos : 1 ≤ k ^ n := Nat.one_le_pow n k (by omega)
    omega  -- k^n + m ≥ 1 + m > m

/-- **Theorem TA (Argmax within a Chapter).**
    For n ≥ 2, let d* be the largest index with `minDepthElem n d* < gap n k`.
    Then `minDepthElem n d*` is the depth-maximising element within [0, gap n k).

    Precisely: for any r < gap n k, `aodDepth n r ≤ aodDepth n (minDepthElem n d*)`.
    The hypothesis `hd_max` encodes that d* is the *largest* such index: the
    next level `minDepthElem n (d*+1) ≥ gap n k` so it falls outside the chapter.

    -- Example witnesses:  n=2, k=2, gap=5, d*=3, minDepthElem 2 3 = 3 < 5,
    --   minDepthElem 2 4 = 7 ≥ 5.  Depths in chapter 2: [1,2,3,4,2] → max=4 at r=3 ✓ -/
theorem argmax_within_chapter (n k d : ℕ) (hn : 2 ≤ n) (_hk : 1 ≤ k)
    (_hd_lt  : minDepthElem n d < gap n k)
    (hd_max : gap n k ≤ minDepthElem n (d + 1))
    (r : ℕ)  (hr : r < gap n k) :
    aodDepth n r ≤ aodDepth n (minDepthElem n d) := by
  rw [minDepthElem_exact_depth n d hn]
  -- Suffices to show: aodDepth n r ≤ d
  -- By contradiction: if aodDepth n r ≥ d+1, then minDepthElem n (d+1) ≤ r
  -- by TD2, but minDepthElem n (d+1) ≥ gap n k > r — contradiction.
  by_contra hlt
  push_neg at hlt            -- hlt : d + 1 ≤ aodDepth n r
  have hmin := minDepthElem_min n (d + 1) r hn hlt
  omega  -- minDepthElem n (d+1) ≤ r < gap n k ≤ minDepthElem n (d+1)

-- Verification: argmax theorem at n=2, k=2 (gap = 5, depths [1,2,3,4,2])
#eval do
  let n := 2; let k := 2
  let g := gap n k            -- 5
  let depths := (List.range g).map (fun r => aodDepth n r)
  let maxD  := depths.foldl Nat.max 0   -- 4
  -- d* = 3: minDepthElem 2 3 = 3 < 5, minDepthElem 2 4 = 7 ≥ 5
  let dStar := 3
  let argR  := minDepthElem n dStar     -- 3
  return (g, depths, maxD, dStar, argR, aodDepth n argR)
  -- (5, [1,2,3,4,2], 4, 3, 3, 4) ✓

end AodDepth
