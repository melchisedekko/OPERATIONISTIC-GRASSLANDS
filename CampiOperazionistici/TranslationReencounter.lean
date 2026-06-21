/-
  TranslationReencounter.lean — Campi Operazionistici
  Paper: §13 (Translation Reencounters & First Jump)
  First Jump Theorem and the structure of equivalence reencounters.

  Given a = k^n + t and b = h^n + t with k < h and 1 ≤ t < gap(n,k):

  **First Jump Theorem**: the pair stays equivalent in Aod n
  exactly for m ∈ {0, …, gap(n,k)-t-1}, i.e. for m < gap(n,k)-t.
  The first jump occurs at m* = gap(n,k)-t.

  **Permanent Separation (adjacent chapters)**: for h = k+1,
  the pair never reencounters after the first jump.
  For non-adjacent chapters (h > k+1), Theorem 2 of the document
  shows that reencounters occur at pairs of simultaneous n-th powers.

  Note: `first_jump_theorem` only asserts the window [0, gap-t),
  not the total absence of equivalence for m ≥ gap-t (there are reencounters).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici

namespace CampiOperazionistici

/-!
## Auxiliary lemmas on `gap` and `irootN`
-/

/-- gap(n,k) > 0 for n ≠ 0. -/
lemma gap_pos' (n k : ℕ) (hn : n ≠ 0) : 0 < gap n k := by
  unfold gap
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn)

/-- gap(n,k) is strictly increasing in k for n ≥ 2. -/
lemma gap_strictMono (n : ℕ) (hn : 2 ≤ n) (k j : ℕ) (hkj : k < j) :
    gap n k < gap n j := by
  induction hkj with
  | refl => exact growingFrontier n k hn
  | step _ ih => exact Nat.lt_trans ih (growingFrontier n _ hn)

/-- For k < h, gap(n,h) > gap(n,k) (with n ≥ 2). -/
lemma gap_lt_of_lt (n k h : ℕ) (hn : 2 ≤ n) (hkh : k < h) :
    gap n k < gap n h :=
  gap_strictMono n hn k h hkh

/-- For k < h, gap(n,h) ≥ gap(n,k) (with n ≥ 2). -/
lemma gap_le_of_lt (n k h : ℕ) (hn : 2 ≤ n) (hkh : k < h) :
    gap n k ≤ gap n h :=
  Nat.le_of_lt (gap_lt_of_lt n k h hn hkh)

/-- irootN n (k^n) = k. -/
lemma irootN_perfectPow (n k : ℕ) (hn : n ≠ 0) : irootN n (k ^ n) = k := by
  apply Nat.le_antisymm
  · by_contra hc
    push_neg at hc
    have h1 : (k + 1) ^ n ≤ (irootN n (k ^ n)) ^ n :=
      Nat.pow_le_pow_left hc n
    have h2 : (irootN n (k ^ n)) ^ n ≤ k ^ n := irootN_pow_le n (k ^ n) hn
    have h3 : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
    linarith
  · by_contra hc
    push_neg at hc
    have h1 : (irootN n (k ^ n) + 1) ^ n ≤ k ^ n :=
      Nat.pow_le_pow_left hc n
    have h2 : k ^ n < (irootN n (k ^ n) + 1) ^ n := irootN_lt_succ_pow n (k ^ n) hn
    linarith

/-- If (k+1)^n ≤ x, then irootN n x ≥ k+1. -/
lemma irootN_ge_of_pow_le (n k x : ℕ) (hn : n ≠ 0) (h : (k + 1) ^ n ≤ x) :
    irootN n x ≥ k + 1 := by
  have : irootN n ((k + 1) ^ n) ≤ irootN n x := irootN_mono n _ _ hn h
  rwa [irootN_perfectPow n (k + 1) hn] at this

/-- (k+1)^n = k^n + gap(n,k). -/
lemma succ_pow_eq_add_gap (n k : ℕ) (_hn : n ≠ 0) : (k + 1) ^ n = k ^ n + gap n k := by
  simp [gap, Nat.add_sub_cancel' (Nat.pow_le_pow_left (Nat.le_succ k) n)]

/-!
## First Jump Theorem (Theorem 1)

Let a = k^n + t and b = h^n + t with k < h and 1 ≤ t < gap(n,k).
The pair is equivalent for m < gap(n,k)-t, and not equivalent for m = gap(n,k)-t.
The equivalence window is exactly {0, …, gap(n,k)-t-1}.
-/

/-- The pair is equivalent for m < gap(n,k) - t. -/
theorem first_jump_easy (n k h t m : ℕ)
    (hn : 2 ≤ n) (hk : k < h) (ht_bound : t < gap n k)
    (hm : m < gap n k - t) :
    (k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n]) := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  have htm_k : t + m < gap n k := by omega
  have htm_h : t + m < gap n h := Nat.lt_of_lt_of_le htm_k (gap_le_of_lt n k h hn hk)
  have rk : radRem n (k ^ n + (t + m)) = t + m := radRem_base_add n k _ hnn htm_k
  have rh : radRem n (h ^ n + (t + m)) = t + m := radRem_base_add n h _ hnn htm_h
  have ek : k ^ n + t + m = k ^ n + (t + m) := by ring
  have eh : h ^ n + t + m = h ^ n + (t + m) := by ring
  rw [ek, eh, rk, rh]

/-- At the first jump m* = gap(n,k)-t the pair breaks: a+m* ≢ b+m*.

    At this precise instant, a+m* = k^n + (gap(n,k)) = (k+1)^n is a
    perfect power with radRem 0, whereas b+m* = h^n + (gap(n,k)) is still
    in chapter h (if gap(n,k) < gap(n,h)) with radRem = gap(n,k) > 0. -/
theorem first_jump_at_mstar (n k h t : ℕ)
    (hn : 2 ≤ n) (hk : k < h) (ht_bound : t < gap n k) :
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ h ^ n + t + (gap n k - t) [Aod n]) := by
  simp only [aodEquiv]
  have hnn : n ≠ 0 := by omega
  -- t + (gap - t) = gap(n,k)
  have htm : t + (gap n k - t) = gap n k := Nat.add_sub_cancel' (Nat.le_of_lt ht_bound)
  -- a + m* = k^n + gap(n,k) = (k+1)^n
  have ha : k ^ n + t + (gap n k - t) = (k + 1) ^ n := by
    rw [show k ^ n + t + (gap n k - t) = k ^ n + (t + (gap n k - t)) from by ring]
    rw [htm, succ_pow_eq_add_gap n k hnn]
  -- b + m* = h^n + gap(n,k), and gap(n,k) < gap(n,h)
  have hb : h ^ n + t + (gap n k - t) = h ^ n + gap n k := by
    rw [show h ^ n + t + (gap n k - t) = h ^ n + (t + (gap n k - t)) from by ring, htm]
  have hgap_lt : gap n k < gap n h := gap_lt_of_lt n k h hn hk
  -- radRem(a + m*) = 0  (it is a perfect power)
  have ra : radRem n ((k + 1) ^ n) = 0 := by
    have : isPerfectPower n ((k + 1) ^ n) := ⟨k + 1, rfl⟩
    rwa [perfectPower_iff_radRem_zero n _ hnn] at this
  -- radRem(b + m*) = gap(n,k) > 0
  have rb : radRem n (h ^ n + gap n k) = gap n k :=
    radRem_base_add n h (gap n k) hnn hgap_lt
  rw [ha, hb, ra, rb]
  exact (Nat.pos_iff_ne_zero.mp (gap_pos' n k hnn)).symm

/-- First Jump Theorem: the equivalence window is {m | m < gap(n,k)-t}.

    The pair is equivalent for m < gap-t, and at the first instant m = gap-t it breaks.
    For m > gap-t there may be reencounters (Theorem 2 of the document). -/
theorem first_jump_theorem (n k h t : ℕ)
    (hn : 2 ≤ n) (hk : k < h) (ht_bound : t < gap n k) :
    (∀ m < gap n k - t, k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n]) ∧
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ h ^ n + t + (gap n k - t) [Aod n]) :=
  ⟨fun m hm => first_jump_easy n k h t m hn hk ht_bound hm,
   first_jump_at_mstar n k h t hn hk ht_bound⟩

/-!
## Reencounter Structure for Non-Adjacent Chapters (Theorem 2)

For h > k+1, reencounters occur for m > m*.
The structure is: if k^n+t+m ≡ₒ h^n+t+m then k' := irootN n (k^n+t+m) > k,
h' := irootN n (h^n+t+m) > h, and (h')^n - (k')^n = h^n - k^n (in ℤ).
-/

/-- If two values are Aod-equivalent, their integer n-th roots
    have the same power difference as the starting point.
    Proof: the equivalence means radRem n a = radRem n b, i.e.
    a - (irootN n a)^n = b - (irootN n b)^n (in ℕ, with truncated subtraction).
    Passing to ℤ and using irootN_pow_le yields the exact equality. -/
lemma aodEquiv_pow_diff_eq (n a b : ℕ) (hn : n ≠ 0)
    (heq : a ≡ₒ b [Aod n]) :
    (irootN n b : ℤ) ^ n - (irootN n a : ℤ) ^ n = (b : ℤ) - (a : ℤ) := by
  simp only [aodEquiv, radRem] at heq
  have hpa := irootN_pow_le n a hn
  have hpb := irootN_pow_le n b hn
  -- heq : a - (irootN n a)^n = b - (irootN n b)^n  (in ℕ, truncated)
  -- given hpa and hpb the subtraction does not truncate, so the equality holds in ℤ
  zify [hpa, hpb] at heq
  linarith

/-- Auxiliary lemma: if a ≥ (k+1)^n then irootN n a ≥ k+1. -/
lemma irootN_ge_succ_of_ge_succ_pow (n k a : ℕ) (hn : n ≠ 0)
    (h : (k + 1) ^ n ≤ a) : k + 1 ≤ irootN n a :=
  irootN_ge_of_pow_le n k a hn h

/-- Reencounter Structure Theorem (Theorem 2, provable part).
    If k < h, 1 ≤ t < gap(n,k), m ≥ gap(n,k) - t (we are beyond m*),
    and the pair reencounters: k^n+t+m ≡ₒ h^n+t+m,
    then:
    (1) k' := irootN n (k^n+t+m) > k
    (2) h' := irootN n (h^n+t+m) > h
    (3) (h')^n - (k')^n = h^n - k^n  (in ℤ)
    Part (3) follows immediately from aodEquiv_pow_diff_eq. -/
theorem reencounter_structure (n k h t m : ℕ)
    (hn : 2 ≤ n) (_hk : k < h) (_ht_low : 1 ≤ t) (ht_bound : t < gap n k)
    (hm : gap n k - t ≤ m)
    (heq : k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n]) :
    let k' := irootN n (k ^ n + t + m)
    let h' := irootN n (h ^ n + t + m)
    k < k' ∧ h < h' ∧
    (h' : ℤ) ^ n - (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n := by
  have hnn : n ≠ 0 := by omega
  set k' := irootN n (k ^ n + t + m)
  set h' := irootN n (h ^ n + t + m)
  -- Part (3): gap preservation, from aodEquiv_pow_diff_eq
  have hgap : (h' : ℤ) ^ n - (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n := by
    have hdiff := aodEquiv_pow_diff_eq n (k ^ n + t + m) (h ^ n + t + m) hnn heq
    push_cast at hdiff ⊢
    linarith
  -- Part (1): k' > k. We have k^n + t + m ≥ k^n + gap(n,k) = (k+1)^n.
  have hkge : (k + 1) ^ n ≤ k ^ n + t + m := by
    rw [succ_pow_eq_add_gap n k hnn]
    omega
  have hk' : k + 1 ≤ k' := irootN_ge_succ_of_ge_succ_pow n k (k ^ n + t + m) hnn hkge
  -- Part (2): h' > h. We have h^n + t + m ≥ h^n + gap(n,h) ≥ h^n + gap(n,k) > h^n.
  -- We need (h+1)^n ≤ h^n + t + m, i.e., gap(n,h) ≤ t + m.
  -- Since h > k, gap(n,h) > gap(n,k), but t + m ≥ gap(n,k) only — not enough in general.
  -- Instead: use hgap + hk'. Since (h')^n = (k')^n + h^n - k^n (in ℤ),
  -- and k' ≥ k+1 > k, and h > k, we need h' > h.
  -- From hgap: (h')^n = (k')^n + h^n - k^n (in ℤ).
  -- We know k' ≥ k+1, so (k')^n ≥ (k+1)^n = k^n + gap(n,k).
  -- Hence (h')^n ≥ k^n + gap(n,k) + h^n - k^n = h^n + gap(n,k) > h^n.
  -- So (h')^n > h^n, which gives h' > h.
  have hh' : h + 1 ≤ h' := by
    -- (h')^n > h^n, so h' > h, i.e., h' ≥ h+1.
    by_contra hlt
    push_neg at hlt
    -- hlt : h' ≤ h, so (h')^n ≤ h^n  (in ℕ, hence in ℤ)
    have hpow_le : (h' : ℤ) ^ n ≤ (h : ℤ) ^ n := by
      have : h' ^ n ≤ h ^ n := Nat.pow_le_pow_left (Nat.lt_succ_iff.mp hlt) n
      exact_mod_cast this
    -- From hk': k' ≥ k+1, so (k')^n ≥ (k+1)^n > k^n
    have hkpow_gt : (k : ℤ) ^ n < (k' : ℤ) ^ n := by
      have hle : (k + 1) ^ n ≤ k' ^ n := Nat.pow_le_pow_left hk' n
      have hlt2 : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hnn
      have : (k + 1 : ℤ) ^ n ≤ (k' : ℤ) ^ n := by exact_mod_cast hle
      have : (k : ℤ) ^ n < (k + 1 : ℤ) ^ n := by exact_mod_cast hlt2
      linarith
    linarith [hgap]
  exact ⟨by omega, by omega, hgap⟩

/-!
## First Reencounter at Perfect Powers (Theorem 2, minimality part)

If m is the MINIMUM reencounter offset after m*, then s = r_n(k^n+t+m) = 0.
Proof: if s > 0 then m₀ = m - s < m is already a reencounter (with s=0 in chapter k'),
contradicting the minimality of m.
-/

/-- If m is the minimum reencounter offset beyond m*, the local coordinate is 0,
    i.e. k^n+t+m and h^n+t+m are both perfect n-th powers.

    Proof: let k' = irootN n (k^n+t+m) and s = radRem n (k^n+t+m).
    Then k^n+t+m = (k')^n + s. If s > 0, consider m₀ = m - s.
    We have m₀ ≥ gap(n,k) - t (so m₀ > m*) since (k')^n ≥ (k+1)^n = k^n+gap.
    Moreover k^n+t+m₀ = (k')^n and h^n+t+m₀ = (h')^n are equivalent (radRem = 0 = 0).
    But m₀ < m, contradicting minimality. Hence s = 0. -/
theorem first_reencounter_at_perfect_power (n k h t m : ℕ)
    (hn : 2 ≤ n) (_hk : k < h) (_ht_low : 1 ≤ t) (ht_bound : t < gap n k)
    (hm_star : gap n k - t ≤ m)
    (heq : k ^ n + t + m ≡ₒ h ^ n + t + m [Aod n])
    -- m is the minimum reencounter offset beyond m*
    (hmin : ∀ m' < m, gap n k - t ≤ m' →
              ¬ (k ^ n + t + m' ≡ₒ h ^ n + t + m' [Aod n])) :
    radRem n (k ^ n + t + m) = 0 := by
  have hnn : n ≠ 0 := by omega
  set k' := irootN n (k ^ n + t + m)
  set s  := radRem n (k ^ n + t + m)
  -- k^n + t + m = (k')^n + s  (by definition of radRem)
  have hdecomp : k ^ n + t + m = k' ^ n + s := by
    have hle := irootN_pow_le n (k ^ n + t + m) hnn
    simp only [s, k', radRem]
    omega
  -- If s = 0 we are done immediately.
  -- Otherwise derive a contradiction with hmin.
  by_contra hs_ne
  -- s ≠ 0, so s ≥ 1, meaning m₀ := m - s < m
  have hs_pos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs_ne
  -- m₀ = m - s: the offset that lands exactly on (k')^n
  set m₀ := m - s with hm₀_def
  have hm₀_lt : m₀ < m := by omega
  -- k' ≥ k + 1  (from reencounter_structure part 1)
  have hkge : (k + 1) ^ n ≤ k ^ n + t + m := by
    rw [succ_pow_eq_add_gap n k hnn]; omega
  have hk' : k + 1 ≤ k' := irootN_ge_succ_of_ge_succ_pow n k (k ^ n + t + m) hnn hkge
  -- m₀ ≥ gap(n,k) - t  (i.e., m₀ is still beyond m*)
  -- We need: m - s ≥ gap(n,k) - t, i.e., m ≥ gap(n,k) - t + s.
  -- From hdecomp: k^n + t + m = (k')^n + s, so m = (k')^n + s - k^n - t.
  -- So m₀ = m - s = (k')^n - k^n - t.
  -- Need: (k')^n - k^n - t ≥ gap(n,k) - t, i.e., (k')^n ≥ k^n + gap(n,k) = (k+1)^n.
  -- This holds since k' ≥ k+1.
  have hm₀_star : gap n k - t ≤ m₀ := by
    have hkpow : k ^ n + gap n k ≤ k' ^ n := by
      rw [← succ_pow_eq_add_gap n k hnn]
      exact Nat.pow_le_pow_left hk' n
    have hval : k ^ n + t + m = k' ^ n + s := hdecomp
    omega
  -- k^n + t + m₀ = (k')^n  (a perfect power)
  have hval_k : k ^ n + t + m₀ = k' ^ n := by omega
  -- h^n + t + m₀ = (h')^n where h' = irootN n (h^n+t+m)
  -- From gap preservation: (h')^n - (k')^n = h^n - k^n
  have hgap_pres : (irootN n (h ^ n + t + m) : ℤ) ^ n -
                   (k' : ℤ) ^ n = (h : ℤ) ^ n - (k : ℤ) ^ n := by
    have := aodEquiv_pow_diff_eq n (k ^ n + t + m) (h ^ n + t + m) hnn heq
    push_cast at this ⊢; linarith
  set h' := irootN n (h ^ n + t + m)
  -- h^n + t + m = (h')^n + s  (same s, since both have radRem = s)
  have hdecomp_h : h ^ n + t + m = h' ^ n + s := by
    have hle_h := irootN_pow_le n (h ^ n + t + m) hnn
    have heq_s : radRem n (h ^ n + t + m) = s := by
      simp only [aodEquiv, s] at heq ⊢; exact heq.symm
    simp only [s, h', radRem] at heq_s ⊢
    omega
  -- h^n + t + m₀ = (h')^n
  have hval_h : h ^ n + t + m₀ = h' ^ n := by omega
  -- Now: k^n+t+m₀ ≡ₒ h^n+t+m₀  because both have radRem = 0
  have heq₀ : k ^ n + t + m₀ ≡ₒ h ^ n + t + m₀ [Aod n] := by
    simp only [aodEquiv, radRem, hval_k, hval_h,
               irootN_perfectPow n k' hnn, irootN_perfectPow n h' hnn,
               Nat.sub_self]
  -- This contradicts hmin: m₀ < m and m₀ ≥ m* and the pair is equivalent
  exact hmin m₀ hm₀_lt hm₀_star heq₀

/-!
## Permanent Separation for Adjacent Chapters (Theorem 6)

For h = k+1, the pair never reencounters after the first jump.
Proof: one would need gap(n,k) = (h')^n - (k')^n for some k' > k,
but gap is strictly increasing, hence impossible.
-/

/-- For adjacent chapters, no pair k' < h' with k' > k
    can have the same power difference gap(n,k). -/
lemma no_reencounter_adjacent_key (n k k' h' : ℕ) (hn : 2 ≤ n)
    (hk' : k < k') (hh' : k' < h')
    (hdiff : h' ^ n - k' ^ n = gap n k) : False := by
  have hnn : n ≠ 0 := by omega
  have hpow : h' ^ n ≥ (k' + 1) ^ n := Nat.pow_le_pow_left hh' n
  have hdiff_ge : h' ^ n - k' ^ n ≥ gap n k' := by
    unfold gap; omega
  linarith [gap_lt_of_lt n k k' hn hk']

/-- Permanent Separation Theorem for adjacent chapters.
    For h = k+1, the pair does not reencounter after m* = gap(n,k)-t.
    Equivalently: there is no m > gap-t with the two radRem equal
    (for adjacent chapters, the difference gap(n,k) is unique and does not repeat). -/
theorem permanent_separation (n k t : ℕ)
    (hn : 2 ≤ n) (ht_bound : t < gap n k) :
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ (k + 1) ^ n + t + (gap n k - t) [Aod n]) :=
  first_jump_at_mstar n k (k + 1) t hn (Nat.lt_succ_self k) ht_bound

/-- Corollary: for adjacent chapters, the equivalence window
    is exactly {m | m < gap(n,k) - t}. -/
theorem adjacent_chapters_first_jump (n k t : ℕ)
    (hn : 2 ≤ n) (ht_bound : t < gap n k) :
    (∀ m < gap n k - t, k ^ n + t + m ≡ₒ (k + 1) ^ n + t + m [Aod n]) ∧
    ¬ (k ^ n + t + (gap n k - t) ≡ₒ (k + 1) ^ n + t + (gap n k - t) [Aod n]) :=
  first_jump_theorem n k (k + 1) t hn (Nat.lt_succ_self k) ht_bound

/-!
## §G — Iterated Jump Dynamics

Beyond the first jump at m* = gap(n,k)−t, the pair can reencounter (for h > k+1).
By `first_reencounter_at_perfect_power`, any minimal reencounter lands both sides on
perfect powers k'^n and h'^n. The analysis then **resets**: the pair (k'^n, h'^n) plays the
same rôle as (k^n, h^n) but with local coordinate 0 and strictly larger gap(n,k') > gap(n,k).

Three results formalise this recursive structure:
1. **Full permanent separation** (adjacent chapters): no reencounter for any m ≥ m*.
2. **Second window theorem**: once reset at (k'^n, h'^n), the pair stays equivalent for
   exactly gap(n,k') more steps — a *wider* window than the original.
3. **Windows grow**: at every reencounter the new window strictly widens.

The `ReencounterRecord` structure captures a perfect-power reencounter event and
allows building the iterated sequence of windows.
-/

/-!
### G.1  Full Permanent Separation for Adjacent Chapters

`permanent_separation` covers only the single break point m = gap(n,k)−t.
Here we extend it to **all** m ≥ gap(n,k)−t, proving that adjacent chapters separate
permanently: no reencounter ever occurs.

Key argument: any reencounter would give k' > k and h' satisfying
(h')^n − (k')^n = gap(n,k). But gap(n,k') > gap(n,k), so
(h')^n − (k')^n ≥ gap(n,k') > gap(n,k) — contradiction.
-/

/-- For adjacent chapters h = k+1, the equivalence breaks for **every** m ≥ gap(n,k)−t,
    not just at the single break point. Together with `first_jump_easy` this gives
    the exact equivalence set {m | m < gap(n,k)−t} with no exceptions beyond. -/
theorem permanent_separation_full (n k t m : ℕ)
    (hn : 2 ≤ n) (ht_bound : t < gap n k)
    (hm : gap n k - t ≤ m) :
    ¬ (k ^ n + t + m ≡ₒ (k + 1) ^ n + t + m [Aod n]) := by
  intro heq
  have hnn : n ≠ 0 := by omega
  set k' := irootN n (k ^ n + t + m)
  set h' := irootN n ((k + 1) ^ n + t + m)
  -- The integer gap is preserved: (h')^n − (k')^n = (k+1)^n − k^n = gap(n,k)
  have hdiff := aodEquiv_pow_diff_eq n (k ^ n + t + m) ((k + 1) ^ n + t + m) hnn heq
  have hgap_int : (h' : ℤ) ^ n - (k' : ℤ) ^ n = gap n k := by
    have hgapdef : (gap n k : ℤ) = (k + 1 : ℤ) ^ n - (k : ℤ) ^ n := by
      have hle : k ^ n ≤ (k + 1) ^ n := Nat.pow_le_pow_left (by omega) n
      simp only [gap]; zify [hle]
    push_cast at hdiff
    linarith [hgapdef]
  -- k' ≥ k+1: since k^n+t+m ≥ (k+1)^n
  have hkm : (k + 1) ^ n ≤ k ^ n + t + m := by rw [succ_pow_eq_add_gap n k hnn]; omega
  have hk' : k + 1 ≤ k' := irootN_ge_succ_of_ge_succ_pow n k _ hnn hkm
  -- h' > k': (h')^n > (k')^n since the difference is positive
  have hgap_pos : (0 : ℤ) < gap n k := by exact_mod_cast gap_pos' n k hnn
  have hh'_nat : k' < h' := by
    by_contra hle; push_neg at hle
    have : (h' : ℤ) ^ n ≤ (k' : ℤ) ^ n := by exact_mod_cast Nat.pow_le_pow_left hle n
    linarith
  -- h'^n − k'^n = gap(n,k) in ℕ
  have hgap_nat : h' ^ n - k' ^ n = gap n k := by
    have hle : k' ^ n ≤ h' ^ n := Nat.pow_le_pow_left (Nat.le_of_lt hh'_nat) n
    zify [hle]; exact_mod_cast hgap_int
  -- Contradiction: no_reencounter_adjacent_key shows this is impossible
  exact no_reencounter_adjacent_key n k k' h' hn (by omega) hh'_nat hgap_nat

/-!
### G.2  Second Window Theorem

After a perfect-power reencounter where k^n+t+m₁ = k'^n and h^n+t+m₁ = h'^n,
the pair (k'^n, h'^n) has local coordinate 0. Applying `first_jump_easy` with t = 0
gives: the pair is equivalent for all m' < gap(n,k'), and breaks at m' = gap(n,k').
-/

/-- **Second window theorem**: if both sides of a translated pair land on perfect powers
    at offset m₁ (so k^n+t+m₁ = k'^n and h^n+t+m₁ = h'^n with k' < h'), then
    the pair is equivalent for exactly gap(n,k') further steps.

    This is `first_jump_easy` applied to (k', h', 0) after the reset. -/
theorem second_window_after_reencounter (n k h t m₁ k' h' : ℕ)
    (hn : 2 ≤ n) (hk'h' : k' < h')
    (heq_k : k ^ n + t + m₁ = k' ^ n)
    (heq_h : h ^ n + t + m₁ = h' ^ n)
    (m' : ℕ) (hm' : m' < gap n k') :
    k ^ n + t + (m₁ + m') ≡ₒ h ^ n + t + (m₁ + m') [Aod n] := by
  have hnn : n ≠ 0 := by omega
  -- Rewrite as k'^n + 0 + m' and h'^n + 0 + m'
  rw [show k ^ n + t + (m₁ + m') = k' ^ n + 0 + m' by omega,
      show h ^ n + t + (m₁ + m') = h' ^ n + 0 + m' by omega]
  -- Apply first_jump_easy with t=0: need 0 < gap n k' (trivially) and m' < gap n k' - 0
  exact first_jump_easy n k' h' 0 m' hn hk'h' (gap_pos' n k' hnn) (by omega)

/-- **Second break**: at offset m₁ + gap(n,k') the equivalence breaks again.
    This is `first_jump_at_mstar` applied to (k', h', 0) after the reset. -/
theorem second_break_after_reencounter (n k h t m₁ k' h' : ℕ)
    (hn : 2 ≤ n) (hk'h' : k' < h')
    (heq_k : k ^ n + t + m₁ = k' ^ n)
    (heq_h : h ^ n + t + m₁ = h' ^ n) :
    ¬ (k ^ n + t + (m₁ + gap n k') ≡ₒ h ^ n + t + (m₁ + gap n k') [Aod n]) := by
  have hnn : n ≠ 0 := by omega
  rw [show k ^ n + t + (m₁ + gap n k') = k' ^ n + 0 + (gap n k' - 0) by omega,
      show h ^ n + t + (m₁ + gap n k') = h' ^ n + 0 + (gap n k' - 0) by omega]
  exact first_jump_at_mstar n k' h' 0 hn hk'h' (gap_pos' n k' hnn)

/-!
### G.3  Windows Grow Monotonically

Since k' > k at any reencounter (from `reencounter_structure`) and gap is strictly
monotone, each successive equivalence window is **strictly wider** than the previous.
-/

/-- After a reencounter at m₁ with k' = irootN n (k^n+t+m₁) > k,
    the second window gap(n,k') is strictly wider than gap(n,k). -/
theorem windows_grow_at_reencounters (n k h t m₁ : ℕ) (hn : 2 ≤ n)
    (hkh : k < h) (ht_low : 1 ≤ t) (ht_bound : t < gap n k)
    (hm_star : gap n k - t ≤ m₁)
    (heq : k ^ n + t + m₁ ≡ₒ h ^ n + t + m₁ [Aod n]) :
    gap n k < gap n (irootN n (k ^ n + t + m₁)) := by
  have hk' := (reencounter_structure n k h t m₁ hn hkh ht_low ht_bound hm_star heq).1
  exact gap_lt_of_lt n k _ hn (by omega)

/-!
### G.4  ReencounterRecord: Formalising the Iterated Structure

A `ReencounterRecord` bundles the data of one perfect-power reencounter event.
Its successor construction shows how the iterated sequence is built recursively.
-/

/-- A perfect-power reencounter for the pair (k^n+t, h^n+t):
    at offset m₁ both sides land simultaneously on perfect n-th powers k'^n and h'^n. -/
structure ReencounterRecord (n k h t : ℕ) where
  /-- Offset beyond the start at which the reencounter occurs. -/
  m₁    : ℕ
  /-- New chapter index (left). -/
  k'    : ℕ
  /-- New chapter index (right). -/
  h'    : ℕ
  /-- Left side lands on a perfect n-th power. -/
  heq_k : k ^ n + t + m₁ = k' ^ n
  /-- Right side lands on a perfect n-th power. -/
  heq_h : h ^ n + t + m₁ = h' ^ n
  /-- The chapters are still non-trivially separated. -/
  hk'h' : k' < h'

/-- Second window from a ReencounterRecord: gap(n,k') further steps stay equivalent. -/
theorem second_window_of_record {n k h t : ℕ} (hn : 2 ≤ n)
    (R : ReencounterRecord n k h t) (m' : ℕ) (hm' : m' < gap n R.k') :
    k ^ n + t + (R.m₁ + m') ≡ₒ h ^ n + t + (R.m₁ + m') [Aod n] :=
  second_window_after_reencounter n k h t R.m₁ R.k' R.h' hn R.hk'h' R.heq_k R.heq_h m' hm'

/-- Second break from a ReencounterRecord: at m₁ + gap(n,k') the equivalence breaks. -/
theorem second_break_of_record {n k h t : ℕ} (hn : 2 ≤ n)
    (R : ReencounterRecord n k h t) :
    ¬ (k ^ n + t + (R.m₁ + gap n R.k') ≡ₒ h ^ n + t + (R.m₁ + gap n R.k') [Aod n]) :=
  second_break_after_reencounter n k h t R.m₁ R.k' R.h' hn R.hk'h' R.heq_k R.heq_h

/-- **Record successor**: a reencounter for the reset pair (k'^n, h'^n, 0) lifts to
    a reencounter for the original pair.  The key invariant is preserved:
    (h'')^n − (k'')^n = (h')^n − (k')^n = h^n − k^n (gap is invariant through all reencounters).

    Proof of heq_k: k^n+t+(m₁+m₁') = (k^n+t+m₁)+m₁' = k'^n+m₁' = k'^n+0+m₁' = k''^n.
    The arithmetic is pure ℕ; omega closes it from R.heq_k and R'.heq_k. -/
def reencounter_record_successor {n k h t : ℕ} (_hn : 2 ≤ n)
    (R  : ReencounterRecord n k h t)
    (R' : ReencounterRecord n R.k' R.h' 0) :
    ReencounterRecord n k h t where
  m₁    := R.m₁ + R'.m₁
  k'    := R'.k'
  h'    := R'.h'
  heq_k := by have h1 := R.heq_k; have h2 := R'.heq_k; omega
  heq_h := by have h1 := R.heq_h; have h2 := R'.heq_h; omega
  hk'h' := R'.hk'h'

/-!
### G.5  Chapter-Index Growth Along a Record Chain

Given a `ReencounterRecord` (or a succession of them), the chapter indices k' form a
**strictly increasing** sequence, and the window gaps `gap n kᵢ` grow monotonically.

Two step-level lemmas formalise this:
1. `reencounterRecord_k'_gt`: For a record with t ≥ 1, the new chapter R.k' exceeds k.
2. `reencounterRecord_successor_k'_gt`: For a successor record with m₁' > 0, the
   successor's k' exceeds the record's k'.

Together with `gap_lt_of_lt`, these give the gap-growth analogue.
The standard fact that any strictly increasing ℕ-sequence is unbounded then gives
the full unboundedness for any initial pair — provided the existence of records,
which is not formalised here (it requires deep arithmetic).
-/

/-- For a reencounter record with local coordinate `t ≥ 1`, the new chapter index
    `R.k'` strictly exceeds the starting chapter `k`.

    Proof: `heq_k` gives `k^n + t + R.m₁ = R.k'^n`.  Since `t ≥ 1`, the LHS
    exceeds `k^n`, so `R.k'^n > k^n`, hence `R.k' > k`. -/
theorem reencounterRecord_k'_gt (n k h t : ℕ) (ht : 1 ≤ t)
    (R : ReencounterRecord n k h t) :
    k < R.k' := by
  have hval : k^n < R.k'^n := by have := R.heq_k; omega
  by_contra hle; push_neg at hle
  exact absurd (Nat.pow_le_pow_left hle n) (by omega)

/-- After a reencounter (with t ≥ 1), the window gap strictly increases:
    `gap n k < gap n R.k'`. -/
theorem reencounterRecord_gap_grows (n k h t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t)
    (R : ReencounterRecord n k h t) :
    gap n k < gap n R.k' :=
  gap_lt_of_lt n k R.k' hn (reencounterRecord_k'_gt n k h t ht R)

/-- In a two-level record chain, the second chapter index strictly exceeds the first.
    Given `R : ReencounterRecord n k h t` and `R' : ReencounterRecord n R.k' R.h' 0`
    with `R'.m₁ > 0`, we have `R.k' < R'.k'`.

    Proof: `R'.heq_k` gives `R.k'^n + R'.m₁ = R'.k'^n`.  Since `R'.m₁ > 0`,
    `R'.k'^n > R.k'^n`, hence `R'.k' > R.k'`.

    Note: for the second record the local coordinate is 0, so the `t ≥ 1` hypothesis
    from `reencounterRecord_k'_gt` does not apply.  Instead we use `R'.m₁ > 0`.
    In practice `R'.m₁ ≥ gap n R.k' > 0` whenever `R.k' < R.h'`, but the record
    does not store this lower bound, so we take `R'.m₁ > 0` as an explicit hypothesis. -/
theorem reencounterRecord_successor_k'_gt (n k h t : ℕ)
    (R : ReencounterRecord n k h t)
    (R' : ReencounterRecord n R.k' R.h' 0) (hm1 : 0 < R'.m₁) :
    R.k' < R'.k' := by
  have hval : R.k'^n < R'.k'^n := by have := R'.heq_k; omega
  by_contra hle; push_neg at hle
  exact absurd (Nat.pow_le_pow_left hle n) (by omega)

/-- In a two-level record chain (with `R'.m₁ > 0`), the window gap grows again:
    `gap n R.k' < gap n R'.k'`. -/
theorem reencounterRecord_successor_gap_grows (n k h t : ℕ) (hn : 2 ≤ n)
    (R : ReencounterRecord n k h t)
    (R' : ReencounterRecord n R.k' R.h' 0) (hm1 : 0 < R'.m₁) :
    gap n R.k' < gap n R'.k' :=
  gap_lt_of_lt n R.k' R'.k' hn
    (reencounterRecord_successor_k'_gt n k h t R R' hm1)

/-- **Strict monotonicity of the chapter-index sequence**: given a two-level chain,
    the chapter indices satisfy `k < R.k' < R'.k'` and the gaps grow twice.

    This is the key structural result for Goal 3: the sequence of chapter indices
    produced by successive reencounters is strictly increasing.  Since any strictly
    increasing sequence of natural numbers is unbounded
    (by `reencounter_chain_unbounded` below), the window gaps diverge to +∞. -/
theorem reencounter_chain_strictly_increasing (n k h t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t)
    (R : ReencounterRecord n k h t)
    (R' : ReencounterRecord n R.k' R.h' 0) (hm1 : 0 < R'.m₁) :
    k < R.k' ∧ R.k' < R'.k' ∧ gap n k < gap n R.k' ∧ gap n R.k' < gap n R'.k' :=
  ⟨reencounterRecord_k'_gt n k h t ht R,
   reencounterRecord_successor_k'_gt n k h t R R' hm1,
   reencounterRecord_gap_grows n k h t hn ht R,
   reencounterRecord_successor_gap_grows n k h t hn R R' hm1⟩

/-- **Unboundedness of strictly increasing ℕ-sequences**.
    Any strictly monotone function `f : ℕ → ℕ` satisfies `f d ≥ f 0 + d`,
    so `f` is unbounded: for every `M`, there exists `d` with `f d > M`.

    This is the standard fact connecting the step-level growth results to full
    unboundedness of the chapter-index sequence: given a strictly increasing
    sequence of records, the chapter indices grow without bound. -/
theorem reencounter_chain_unbounded (f : ℕ → ℕ) (hf : StrictMono f) (M : ℕ) :
    ∃ d, M < f d := by
  -- f n ≥ f 0 + n, proved by induction
  have hgrowth : ∀ n, f 0 + n ≤ f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => linarith [hf (Nat.lt_succ_self n)]
  exact ⟨M + 1, by linarith [hgrowth (M + 1)]⟩

end CampiOperazionistici
