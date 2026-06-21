/-
  AodInfinito.lean
  Aod∞ — The Infinite Radical Profile Structure
  Campi Operazionistici — Subsection: Radical Profile and Structures of Aod∞
  Author: Alessandro Sgarbi — 2026-03-03
  Paper: §17 (Infinite Radical Profile Structure Aod∞)
-/

import CampiOperazionistici.CampiOperazionistici
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open CampiOperazionistici

namespace AodInfinito

/-!
# Aod∞ — The Infinite Radical Profile Structure

Formalization of the **radical profile** Π∞(a) and the structures of Aod∞:
the structure that encodes the radical profiles of ℕ over all degrees Aod_n simultaneously, for n ≥ 2.

## Note on the Fundamental Theorem

In a preliminary formulation the Fundamental Theorem appeared with the divisibility
direction **inverted**. The correct formulation is:

  **Π∞(a) = { n ≥ 2 : n ∣ radExp a }**   (n divides the rad-exponent)

and NOT "radExp(a) ∣ n". Check with examples:
- a = 8  = 2³  → radExp 8  = 3, Π∞(8)  = {3}       (divisors ≥ 2 of 3)
- a = 64 = 2⁶  → radExp 64 = 6, Π∞(64) = {2, 3, 6} (divisors ≥ 2 of 6)
- a = 9  = 3²  → radExp 9  = 2, Π∞(9)  = {2}        (divisors ≥ 2 of 2)

The corollary "2 ∈ Π∞(a) ↔ radExp a is even" follows from 2 ∣ radExp a.

## Mathematical Correction on C1 and C5

Conjecture C1 (injectivity of diagEmbed) and C5 (≡∞ is the identity) are **FALSE**
in their original formulation. Concretely:
- `radRem n 0 = 0` and `radRem n 1 = 0` for every n ≥ 2 (0 and 1 are strong zeros)
- Hence `diagEmbed 0 = diagEmbed 1` (same infinite signature: all zero)
- Therefore `0 ≡∞ 1` but `0 ≠ 1`

**Correct result**: diagEmbed is injective on {a : ℕ | a ≥ 2}. The complete
proof is included in `diagEmbed_injective_on_ge_two`.

## File Structure

1. **Radical Profile** — definition of Π∞, characterization, examples
2. **Closure under Divisors** — fundamental lemma and corollaries (proved)
3. **Weak and Strong Zeros** — definitions and complete characterization (proved)
4. **Key Auxiliary Lemmas** — lt_two_pow_self, irootN_eq_one, radRem_eq_pred
5. **Rad-Exponent** — definition via sSup, lemmas (partially proved)
6. **Fundamental Theorem** — statement of C3 (proved)
7. **Radical Weight** — finite count with computational checks
8. **Diagonal Embedding and ≡∞** — diagEmbed, equivalence (proved)
9. **Corrected Conjectures C1–C5** — formalized with the mathematical corrections

## References

- `CampiOperazionistici.lean` — radRem, irootN, isPerfectPower,
  perfectPower_iff_radRem_zero (namespace CampiOperazionistici)
- main paper (`main.pdf`) — statements and discursive proofs
-/

/-! ## 1. Radical Profile -/

/-- `radicalProfile a` is the set of degrees `n ≥ 2` for which `a` is a perfect
n-th power, equivalently for which `radRem n a = 0`. -/
def radicalProfile (a : ℕ) : Set ℕ :=
  {n | 2 ≤ n ∧ radRem n a = 0}

/-- Compact notation: Π∞(a) for the radical profile of a. -/
scoped notation "Π∞(" a ")" => radicalProfile a

@[simp]
lemma mem_radicalProfile_iff {n a : ℕ} :
    n ∈ Π∞(a) ↔ 2 ≤ n ∧ radRem n a = 0 := Iff.rfl

/-- Characterization via `isPerfectPower`: n ∈ Π∞(a) ↔ a is an n-th power. -/
lemma mem_radicalProfile_iff_isPP {n a : ℕ} (hn : 2 ≤ n) :
    n ∈ Π∞(a) ↔ isPerfectPower n a := by
  simp only [mem_radicalProfile_iff, hn, true_and,
    ← perfectPower_iff_radRem_zero n a (by omega)]

/-- 0 belongs to every radical profile: 0 = 0^n for every n ≥ 1. -/
lemma zero_mem_all_profile (n : ℕ) (hn : 2 ≤ n) : n ∈ Π∞(0) := by
  rw [mem_radicalProfile_iff_isPP hn]
  exact ⟨0, Nat.zero_pow (by omega : 0 < n)⟩

/-- 1 belongs to every radical profile: 1 = 1^n for every n. -/
lemma one_mem_all_profile (n : ℕ) (hn : 2 ≤ n) : n ∈ Π∞(1) := by
  rw [mem_radicalProfile_iff_isPP hn]
  exact ⟨1, one_pow n⟩

/-- The power k^n has n in its radical profile. -/
lemma pow_mem_radicalProfile {k n : ℕ} (hn : 2 ≤ n) : n ∈ Π∞(k ^ n) := by
  rw [mem_radicalProfile_iff_isPP hn]
  exact ⟨k, rfl⟩

/-! ## 2. Closure under Divisors -/

/-- **Fundamental Closure Lemma**: if `a = k^m` and `n ∣ m` with `n ≥ 2`,
then `n ∈ Π∞(a)`. This is the heart of the Fundamental Theorem (easy direction):
if e_a ∣ m and a = k^m, then every divisor n of m belongs to Π∞(a). -/
theorem radicalProfile_dvd_closed {a k m n : ℕ} (hn : 2 ≤ n)
    (hmn : n ∣ m) (ha : k ^ m = a) : n ∈ Π∞(a) := by
  rw [mem_radicalProfile_iff_isPP hn]
  obtain ⟨q, hq⟩ := hmn
  -- a = k^m = k^(n·q) = (k^q)^n
  exact ⟨k ^ q, by subst ha; rw [hq]; ring⟩

/-- **Downward closure**: if `n ∈ Π∞(a)` and `m ∣ n` with `m ≥ 2`,
then `m ∈ Π∞(a)`. The radical profile is closed under divisors ≥ 2. -/
theorem radicalProfile_downward_closed {a n m : ℕ} (hm : 2 ≤ m)
    (hmn : m ∣ n) (hn_mem : n ∈ Π∞(a)) : m ∈ Π∞(a) := by
  -- Extract 2 ≤ n directly from membership, avoiding omega on divisibility
  have hn : 2 ≤ n := (mem_radicalProfile_iff.mp hn_mem).1
  rw [mem_radicalProfile_iff_isPP hn] at hn_mem
  obtain ⟨k, hk⟩ := hn_mem
  exact radicalProfile_dvd_closed hm hmn hk

/-- If `2 ∣ e` (e even) and `a = k^e`, then `a` is a perfect square. -/
theorem two_mem_profile_of_even_exp {a k e : ℕ} (he : 2 ∣ e) (ha : k ^ e = a) :
    2 ∈ Π∞(a) :=
  radicalProfile_dvd_closed le_rfl he ha

/-- If `3 ∣ e` and `a = k^e`, then `a` is a perfect cube. -/
theorem three_mem_profile_of_triple_exp {a k e : ℕ} (he : 3 ∣ e) (ha : k ^ e = a) :
    3 ∈ Π∞(a) :=
  radicalProfile_dvd_closed (by norm_num) he ha

/-- **Corollary**: `2 ∈ Π∞(a)` ↔ `a` is a perfect square. -/
theorem two_mem_radicalProfile_iff {a : ℕ} :
    2 ∈ Π∞(a) ↔ ∃ k, k ^ 2 = a :=
  mem_radicalProfile_iff_isPP le_rfl

/-- **Corollary**: the gcd of two degrees in the profile is still in the profile.
If n ∈ Π∞(a) and m is arbitrary, then gcd(n,m) ∈ Π∞(a) (provided gcd ≥ 2).
Note: it is not necessary that m ∈ Π∞(a); downward closure on n suffices. -/
theorem radicalProfile_gcd_closed {a n m : ℕ} (hg : 2 ≤ Nat.gcd n m)
    (hn : n ∈ Π∞(a)) : Nat.gcd n m ∈ Π∞(a) :=
  radicalProfile_downward_closed hg (Nat.gcd_dvd_left n m) hn

/-! ## 3b. Auxiliary Lemmas (anticipated for use in §3) -/

/-- For every natural number n, `n < 2^n` holds. Proof by induction. -/
private lemma lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm]
    have hp : 0 < 2 ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num))
    linarith

/-! ## 3. Weak and Strong Zeros -/

/-- `a` is a **weak zero** if it has at least one degree n ≥ 2 for which it is a perfect power. -/
def isWeakZero (a : ℕ) : Prop := (Π∞(a)).Nonempty

/-- `a` is a **strong zero** if it is a perfect power for every degree n ≥ 2. -/
def isStrongZero (a : ℕ) : Prop := ∀ n, 2 ≤ n → n ∈ Π∞(a)

theorem zero_isStrongZero : isStrongZero 0 := zero_mem_all_profile
theorem one_isStrongZero  : isStrongZero 1 := one_mem_all_profile

theorem isStrongZero_isWeakZero {a : ℕ} (h : isStrongZero a) : isWeakZero a :=
  ⟨2, h 2 le_rfl⟩

theorem zero_isWeakZero : isWeakZero 0 := isStrongZero_isWeakZero zero_isStrongZero
theorem one_isWeakZero  : isWeakZero 1 := isStrongZero_isWeakZero one_isStrongZero

/-- `k^n` is a weak zero for every k, n ≥ 2. -/
theorem pow_isWeakZero {k n : ℕ} (hn : 2 ≤ n) : isWeakZero (k ^ n) :=
  ⟨n, pow_mem_radicalProfile hn⟩

/-- **Characterization of Strong Zeros**: exactly `a ∈ {0, 1}`.
Proof: if a ≥ 2, we use n = a itself. Any k with k^a = a leads to a
contradiction: k = 0 gives 0, k = 1 gives 1, k ≥ 2 gives k^a ≥ 2^a > a. -/
theorem isStrongZero_iff (a : ℕ) : isStrongZero a ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    obtain ⟨hne0, hne1⟩ := hne
    have ha2 : 2 ≤ a := by omega
    have hmem := h a ha2
    rw [mem_radicalProfile_iff_isPP ha2] at hmem
    obtain ⟨k, hk⟩ := hmem
    -- k^a = a with a ≥ 2: impossible for any k
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · -- k = 0: 0^a = 0 ≠ a (since a ≥ 2)
        simp [Nat.zero_pow (show 0 < a by omega)] at hk
        omega
      · -- k = 1: 1^a = 1 ≠ a (since a ≥ 2)
        simp at hk; omega
    · -- k ≥ 2: k^a ≥ 2^a > a (by lt_two_pow_self proved below)
      have hlt : a < k ^ a :=
        calc a < 2 ^ a := lt_two_pow_self a
             _ ≤ k ^ a := Nat.pow_le_pow_left hk2 a
      omega
  · rintro (rfl | rfl)
    · exact zero_isStrongZero
    · exact one_isStrongZero

/-- Characterization of weak zeros: any perfect power of degree ≥ 2. -/
theorem isWeakZero_iff (a : ℕ) : isWeakZero a ↔ ∃ n ≥ 2, ∃ k, k ^ n = a := by
  constructor
  · rintro ⟨n, hn_mem⟩
    have hn : 2 ≤ n := (mem_radicalProfile_iff.mp hn_mem).1
    rw [mem_radicalProfile_iff_isPP hn] at hn_mem
    obtain ⟨k, hk⟩ := hn_mem
    exact ⟨n, hn, k, hk⟩
  · rintro ⟨n, hn, k, hk⟩
    exact ⟨n, (mem_radicalProfile_iff_isPP hn).mpr ⟨k, hk⟩⟩

/-! ## 4. Key Auxiliary Lemmas -/

/-!
These private lemmas are used in the later sections and also for the complete
proof of Conjecture C1 restricted to ℕ≥2. `lt_two_pow_self` is defined
ahead of time in section 3b so as to be available to `isStrongZero_iff`.
-/

/-- If `a < 2^n` and `a ≥ 2` and `n ≥ 2`, then `irootN n a = 1`.
Proof: any k ≥ 2 would give k^n ≥ 2^n > a, hence irootN n a ≤ 1.
And since a ≥ 2 ≥ 1 = 1^n, we have irootN n a ≥ 1. By antisymmetry, = 1. -/
private lemma irootN_eq_one {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) (hlt : a < 2 ^ n) :
    irootN n a = 1 := by
  have hn' : n ≠ 0 := by omega
  apply Nat.le_antisymm
  · -- irootN n a ≤ 1: by contradiction, if irootN n a ≥ 2, then (irootN n a)^n ≥ 2^n > a
    by_contra h
    push_neg at h
    have h2 : 2 ≤ irootN n a := by omega
    have hge : 2 ^ n ≤ (irootN n a) ^ n := Nat.pow_le_pow_left h2 n
    have hle := irootN_pow_le n a hn'
    linarith
  · -- 1 ≤ irootN n a: by contradiction, if irootN n a = 0, then a < 1 (contradiction)
    by_contra h
    push_neg at h
    have h0 : irootN n a = 0 := by omega
    have hlt_succ := irootN_lt_succ_pow n a hn'
    rw [h0, Nat.zero_add, one_pow] at hlt_succ
    omega

/-- If `a < 2^n`, `a ≥ 2`, `n ≥ 2`, then `radRem n a = a - 1`.
This is the stabilization value: for n sufficiently large,
every number ≥ 2 has radical remainder equal to itself minus 1. -/
private lemma radRem_eq_pred {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) (hlt : a < 2 ^ n) :
    radRem n a = a - 1 := by
  have h1 : irootN n a = 1 := irootN_eq_one hn ha hlt
  simp [radRem, h1]

/-! ## 5. Rad-Exponent -/

/-- The **rad-exponent** `radExp a`: the largest `e ≥ 1` such that `∃ m, m^e = a`.
Equivalently, the gcd of the exponents in the prime factorization of a.
Convention: `radExp 0 = 0` and `radExp 1 = 0`
(their profiles are all of ℕ≥2, but for consistency we use 0).
For a ≥ 2: radExp a = sSup {e | 0 < e ∧ isPerfectPower e a}. -/
noncomputable def radExp (a : ℕ) : ℕ :=
  if a ≤ 1 then 0
  else sSup {e | 0 < e ∧ ∃ m, m ^ e = a}

/-- For a ≥ 2, the set of powers is non-empty (contains 1: a = a^1). -/
lemma radExp_pos_of_ge_two {a : ℕ} (ha : 1 < a) : 0 < radExp a := by
  have hne : ¬ a ≤ 1 := by omega
  simp only [radExp, hne, if_false]
  -- Goal: 0 < sSup {e | 0 < e ∧ ∃ m, m ^ e = a}
  set S := {e | 0 < e ∧ ∃ m, m ^ e = a}
  have hmem : 1 ∈ S := ⟨Nat.one_pos, a, pow_one a⟩
  have hbdd : BddAbove S := by
    use a
    intro e ⟨he_pos, m, hm⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · simp [Nat.zero_pow he_pos] at hm; omega
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · have : m = 1 := by omega
        subst this; simp at hm; omega
      · have h2e : e < 2 ^ e := lt_two_pow_self e
        have h2m : 2 ^ e ≤ m ^ e := Nat.pow_le_pow_left hm2 e
        linarith [hm.symm ▸ h2m]
  have hle : 1 ≤ sSup S := le_csSup hbdd hmem
  linarith

/-- Lemma: if m^e = p^n with p prime and 0 < e, then e ≤ n.
Proof: p ∣ m (from primality on p ∣ m^e), hence p^e ∣ m^e = p^n, i.e. e ≤ n. -/
private lemma exp_le_of_pow_eq_prime_pow {p m e n : ℕ} (hp : p.Prime)
    (_he : 0 < e) (hn : 0 < n) (hm : m ^ e = p ^ n) : e ≤ n := by
  have hp_dvd_me : p ∣ m ^ e := hm ▸ dvd_pow_self p hn.ne'
  have hp_dvd_m  : p ∣ m    := hp.dvd_of_dvd_pow hp_dvd_me
  have hpe_dvd   : p ^ e ∣ p ^ n := hm ▸ pow_dvd_pow_of_dvd hp_dvd_m e
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpe_dvd

/-- Computation of radExp for a prime power: radExp(p^n) = n. -/
lemma radExp_prime_pow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    radExp (p ^ n) = n := by
  have hpn_gt : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
  simp only [radExp, Nat.not_le.mpr hpn_gt, if_false]
  set S := {e | 0 < e ∧ ∃ m, m ^ e = p ^ n}
  have hbdd : BddAbove S :=
    ⟨n, fun e ⟨he_pos, m, hm⟩ => exp_le_of_pow_eq_prime_pow hp he_pos hn hm⟩
  have hmem : n ∈ S := ⟨hn, p, rfl⟩
  apply Nat.le_antisymm
  · exact csSup_le ⟨n, hmem⟩ (fun e ⟨he_pos, m, hm⟩ => exp_le_of_pow_eq_prime_pow hp he_pos hn hm)
  · exact le_csSup hbdd hmem

-- (The computational checks of radWeight are found in Section 7)

/-! ## 6. Fundamental Theorem -/

/-!
### Correction to the Draft

A preliminary formulation states `Π(a) = {n ≥ 2 : e_a ∣ n}` (e_a divides n),
but the reported examples are inconsistent with this formula. The correct formula,
verifiable for every example, is:

  **Π∞(a) = { n ≥ 2 : n ∣ radExp a }**

The draft's Corollary — "2 ∈ Π(a) ↔ e_a is even" — is instead correct
and follows from this formulation: 2 ∣ radExp a ↔ radExp a is even.
-/

/-- **Fundamental Theorem — Easy Direction**:
If `n ∣ radExp a` and `n ≥ 2`, then `n ∈ Π∞(a)`.
(Requires the construction of the canonical root of a.) -/
theorem mem_radicalProfile_of_dvd_radExp {a n : ℕ} (hn : 2 ≤ n) (ha : 1 < a)
    (hdvd : n ∣ radExp a) : n ∈ Π∞(a) := by
  have hne : ¬ a ≤ 1 := by omega
  -- Unfold radExp explicitly to avoid issues with set
  have hradExp : radExp a = sSup {e | 0 < e ∧ ∃ m, m ^ e = a} := by
    simp only [radExp, hne, if_false]
  -- Bound: every e with m^e = a satisfies e ≤ a
  have hbound : ∀ e, (0 < e ∧ ∃ m, m ^ e = a) → e ≤ a := by
    intro e ⟨he_pos, m, hm⟩
    rcases Nat.eq_zero_or_pos m with rfl | _
    · simp [Nat.zero_pow he_pos] at hm; omega
    · rcases Nat.lt_or_ge m 2 with hm1 | hm2
      · -- m = 1: 1^e = 1 = a, contradiction with a ≥ 2
        have hm1eq : m = 1 := by omega
        subst hm1eq; simp at hm; omega
      · -- m ≥ 2: e < 2^e ≤ m^e = a
        have := lt_two_pow_self e
        have := hm.symm ▸ Nat.pow_le_pow_left hm2 e
        linarith
  set S := {e | 0 < e ∧ ∃ m, m ^ e = a}
  have hmem1 : 1 ∈ S := ⟨Nat.one_pos, a, pow_one a⟩
  have hbdd : BddAbove S := ⟨a, hbound⟩
  have hS_ne : S.Nonempty := ⟨1, hmem1⟩
  -- S is finite: it is contained in Finset.range (a+1) as a Set
  have hS_fin : Set.Finite S :=
    Set.Finite.subset (Set.finite_Icc 0 a)
      (fun e he => Set.mem_Icc.mpr ⟨by omega, hbound e he⟩)
  -- sSup S ∈ S (maximum attained on a non-empty finite set)
  -- sSup S ∈ S: S is finite, its sSup is the maximum and belongs to S
  have hmax_mem : sSup S ∈ S := by
    -- Convert S to its Finset and use max'
    set F := hS_fin.toFinset with hF_def
    have hF_ne : F.Nonempty := by
      rwa [Set.Finite.toFinset_nonempty hS_fin]
    have hmax_in_S : F.max' hF_ne ∈ S :=
      hS_fin.mem_toFinset.mp (hF_def ▸ F.max'_mem hF_ne)
    suffices h : sSup S = F.max' hF_ne by rwa [h]
    apply Nat.le_antisymm
    · apply csSup_le hS_ne
      intro x hx
      apply Finset.le_max'
      rwa [hF_def, hS_fin.mem_toFinset]
    · exact le_csSup hbdd hmax_in_S
  obtain ⟨_, m_max, hm_max⟩ := hmax_mem
  -- n ∣ sSup S, hence ∃ q, sSup S = n * q
  rw [hradExp] at hdvd
  -- After rw, hdvd : n ∣ sSup {e | ...} = sSup S
  have hdvd' : n ∣ sSup S := by rwa [show sSup {e | 0 < e ∧ ∃ m, m ^ e = a} = sSup S from rfl]
  obtain ⟨q, hq⟩ := hdvd'
  -- a = m_max^(sSup S) = m_max^(n*q) = (m_max^q)^n
  exact radicalProfile_dvd_closed hn ⟨q, hq⟩ hm_max

/-- **Fundamental Theorem — Complete Characterization** (Conjecture C3):
`n ∈ Π∞(a) ↔ n ∣ radExp a`, for `a > 1` and `n ≥ 2`.
The radical profile coincides exactly with the divisors ≥ 2 of the rad-exponent. -/
theorem radicalProfile_eq_dvd_radExp {a : ℕ} (ha : 1 < a) :
    ∀ n, 2 ≤ n → (n ∈ Π∞(a) ↔ n ∣ radExp a) := by
  intro n hn
  constructor
  · -- Direction: n ∈ Π∞(a) → n ∣ radExp a
    -- Strategy: let m^n = a, e₀ = sSup S = radExp a.
    -- From m^n = m₀^{e₀}: by Nat.exists_eq_pow_of_pow_eq_pow we get c with
    -- m = c^{e₀/gcd(n,e₀)}, hence a = m^n = c^{n * e₀/gcd(n,e₀)} = c^{lcm(n,e₀)}.
    -- Since lcm(n,e₀) ∈ S and e₀ is the maximum, lcm(n,e₀) = e₀, i.e. n ∣ e₀.
    intro hn_mem
    have hne : ¬ a ≤ 1 := by omega
    have hradExp : radExp a = sSup {e | 0 < e ∧ ∃ m, m ^ e = a} := by
      simp only [radExp, hne, if_false]
    -- Build S and its properties (repeating the structure of mem_radicalProfile_of_dvd_radExp)
    have hbound : ∀ e, (0 < e ∧ ∃ m, m ^ e = a) → e ≤ a := by
      intro e ⟨he_pos, m, hm⟩
      rcases Nat.eq_zero_or_pos m with rfl | _
      · simp [Nat.zero_pow he_pos] at hm; omega
      · rcases Nat.lt_or_ge m 2 with hm1 | hm2
        · have hm1eq : m = 1 := by omega
          subst hm1eq; simp at hm; omega
        · have := lt_two_pow_self e
          have := hm.symm ▸ Nat.pow_le_pow_left hm2 e
          linarith
    set S := {e | 0 < e ∧ ∃ m, m ^ e = a}
    have hmem1 : 1 ∈ S := ⟨Nat.one_pos, a, pow_one a⟩
    have hbdd : BddAbove S := ⟨a, hbound⟩
    have hS_ne : S.Nonempty := ⟨1, hmem1⟩
    have hS_fin : Set.Finite S :=
      Set.Finite.subset (Set.finite_Icc 0 a)
        (fun e he => Set.mem_Icc.mpr ⟨by omega, hbound e he⟩)
    have hmax_mem : sSup S ∈ S := by
      set F := hS_fin.toFinset with hF_def
      have hF_ne : F.Nonempty := by rwa [Set.Finite.toFinset_nonempty hS_fin]
      have hmax_in_S : F.max' hF_ne ∈ S :=
        hS_fin.mem_toFinset.mp (hF_def ▸ F.max'_mem hF_ne)
      suffices h : sSup S = F.max' hF_ne by rwa [h]
      apply Nat.le_antisymm
      · apply csSup_le hS_ne
        intro x hx; apply Finset.le_max'; rwa [hF_def, hS_fin.mem_toFinset]
      · exact le_csSup hbdd hmax_in_S
    -- Extract m and m₀ with m^n = a and m₀^{e₀} = a
    rw [mem_radicalProfile_iff_isPP hn] at hn_mem
    obtain ⟨m, hm⟩ := hn_mem
    obtain ⟨he₀_pos, m₀, hm₀⟩ := hmax_mem
    -- Apply exists_eq_pow_of_pow_eq_pow to m^n = m₀^{e₀}
    have hn_pos : 0 < n := by omega
    have heq : m ^ n = m₀ ^ sSup S := hm.trans hm₀.symm
    obtain ⟨c, hc_m, hc_m₀⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hn_pos.ne') heq
    -- a = c^{n * (sSup S / gcd(n, sSup S))}
    have hlcm_eq : n * (sSup S / Nat.gcd n (sSup S)) = Nat.lcm n (sSup S) := by
      rw [Nat.lcm, Nat.mul_div_assoc n (Nat.gcd_dvd_right n (sSup S))]
    have ha_eq_clcm : a = c ^ Nat.lcm n (sSup S) := by
      rw [← hlcm_eq]
      -- Goal: a = c ^ (n * (sSup S / gcd n (sSup S)))
      -- hm : m ^ n = a, hc_m : m = c ^ (sSup S / gcd n (sSup S))
      rw [← hm, hc_m, ← pow_mul, mul_comm]
    -- Nat.lcm n (sSup S) ∈ S
    have hlcm_pos : 0 < Nat.lcm n (sSup S) := by
      apply Nat.lcm_pos hn_pos he₀_pos
    have hlcm_mem : Nat.lcm n (sSup S) ∈ S := ⟨hlcm_pos, c, ha_eq_clcm.symm⟩
    -- Nat.lcm n (sSup S) ≤ sSup S (sSup is an upper bound of S, and lcm ∈ S)
    have hlcm_le : Nat.lcm n (sSup S) ≤ sSup S :=
      le_csSup hbdd hlcm_mem
    -- e₀ ∣ Nat.lcm n e₀
    have he₀_dvd_lcm : sSup S ∣ Nat.lcm n (sSup S) := Nat.dvd_lcm_right n (sSup S)
    -- Hence Nat.lcm n (sSup S) = sSup S
    have hlcm_eq_e₀ : Nat.lcm n (sSup S) = sSup S :=
      Nat.le_antisymm hlcm_le (Nat.le_of_dvd hlcm_pos he₀_dvd_lcm)
    -- n ∣ sSup S
    have hn_dvd : n ∣ sSup S := by
      rwa [← Nat.lcm_eq_right_iff_dvd]
    -- Conclude: n ∣ radExp a = sSup S
    rwa [hradExp, show sSup {e | 0 < e ∧ ∃ m, m ^ e = a} = sSup S from rfl]
  · -- Direction: n ∣ radExp a → n ∈ Π∞(a) (easy Fundamental Theorem)
    exact mem_radicalProfile_of_dvd_radExp hn ha

/-- **Lattice Structure of Π∞**: inclusion of profiles ↔ divisibility of rad-exponents.
`Π∞(b) ⊆ Π∞(a)` (among the degrees ≥ 2) ↔ `radExp b ∣ radExp a`.

**Correction Note**: The draft's original statement had the quantifier inverted
(`n ∈ Π∞(a) → n ∈ Π∞(b)`), which would be equivalent to `radExp a ∣ radExp b`, not `radExp b ∣ radExp a`.
The correct formulation (verified with examples: a=2^6, b=2^3 → Π∞(b)={3} ⊆ Π∞(a)={2,3,6}
and radExp b = 3 ∣ 6 = radExp a) requires `n ∈ Π∞(b) → n ∈ Π∞(a)`. -/
theorem radicalProfile_lattice {a b : ℕ} (ha : 1 < a) (hb : 1 < b) :
    (∀ n, 2 ≤ n → n ∈ Π∞(b) → n ∈ Π∞(a)) ↔ radExp b ∣ radExp a := by
  -- Reduction via the complete characterization: n ∈ Π∞(x) ↔ n ∣ radExp x (for x > 1, n ≥ 2)
  constructor
  · -- LHS → RHS: ∀ n ≥ 2, n ∣ radExp b → n ∣ radExp a; prove radExp b ∣ radExp a.
    -- Taking n = radExp b (if ≥ 2): radExp b ∣ radExp b is trivial, hence from the hypothesis
    -- radExp b ∈ Π∞(b) → radExp b ∈ Π∞(a) → radExp b ∣ radExp a. ✓
    -- If radExp b < 2: radExp b = 0 or 1.
    --   radExp b = 0: 0 ∣ radExp a ↔ radExp a = 0. But radExp a > 0 since a > 1. Contradiction?
    --     radExp b = 0 only if b ≤ 1 (by definition), but hb : 1 < b. Hence radExp b > 0.
    --   radExp b = 1: 1 ∣ radExp a is trivial. ✓
    intro h
    rcases Nat.lt_or_ge (radExp b) 2 with hlt | hge
    · -- radExp b < 2, i.e. radExp b = 0 or 1
      have hpos : 0 < radExp b := radExp_pos_of_ge_two hb
      have : radExp b = 1 := by omega
      rw [this]; exact one_dvd _
    · -- radExp b ≥ 2: radExp b ∈ Π∞(b) (easy direction)
      have hb_mem : radExp b ∈ Π∞(b) :=
        mem_radicalProfile_of_dvd_radExp hge hb dvd_rfl
      -- Apply h: radExp b ∈ Π∞(a)
      have ha_mem : radExp b ∈ Π∞(a) := h (radExp b) hge hb_mem
      -- Hard direction on a: radExp b ∣ radExp a
      exact ((radicalProfile_eq_dvd_radExp ha) (radExp b) hge).mp ha_mem
  · -- RHS → LHS: radExp b ∣ radExp a → ∀ n ≥ 2, n ∈ Π∞(b) → n ∈ Π∞(a)
    -- From n ∈ Π∞(b): n ∣ radExp b (hard direction on b).
    -- From radExp b ∣ radExp a and n ∣ radExp b: n ∣ radExp a (transitivity).
    -- From n ∣ radExp a: n ∈ Π∞(a) (easy direction on a). ✓
    intro hdvd n hn hn_mem
    have hn_dvd_b : n ∣ radExp b :=
      ((radicalProfile_eq_dvd_radExp hb) n hn).mp hn_mem
    have hn_dvd_a : n ∣ radExp a := hn_dvd_b.trans hdvd
    exact mem_radicalProfile_of_dvd_radExp hn ha hn_dvd_a

/-! ## 7. Radical Weight -/

/-- `radWeight a N` counts the degrees `n ∈ [2, N]` for which `a` is a perfect n-th power.
It is a finite and computable version of the infinite weight `w(a) = |Π∞(a)|`. -/
def radWeight (a N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun n => radRem n a = 0)).card

/-- The weight is monotone in N. -/
lemma radWeight_mono {a N M : ℕ} (hNM : N ≤ M) : radWeight a N ≤ radWeight a M :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hNM))

-- Computational checks
-- a = 7 (prime): no perfect power in [2,30]
#eval radWeight 7 30    -- expected: 0
-- a = 8 = 2^3: only n=3 in [2,30]
#eval radWeight 8 30    -- expected: 1
-- a = 9 = 3^2: only n=2 in [2,30]
#eval radWeight 9 30    -- expected: 1
-- a = 64 = 2^6: n ∈ {2,3,6} in [2,30]
#eval radWeight 64 30   -- expected: 3
-- a = 4096 = 2^12: n ∈ {2,3,4,6,12} in [2,30]
#eval radWeight 4096 30 -- expected: 5
-- a = 1: strong zero, all degrees in [2,10]
#eval radWeight 1 10    -- expected: 9

/-- For strong zeros, radWeight a N = N - 1 (all degrees in [2,N] active). -/
lemma radWeight_strongZero {a N : ℕ} (ha : isStrongZero a) (hN : 2 ≤ N) :
    radWeight a N = N - 1 := by
  simp only [radWeight]
  have hfilter : (Finset.Icc 2 N).filter (fun n => radRem n a = 0) = Finset.Icc 2 N := by
    apply Finset.filter_true_of_mem
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hmem := ha n hn.1
    simp [radicalProfile] at hmem
    exact hmem.2
  rw [hfilter]
  -- Direct proof: |Finset.Icc 2 N| = N - 1
  -- Via bijection with Finset.range (N-1): b ↦ b - 2 (inverse: i ↦ i + 2)
  -- card_bij maps from the LHS (Icc 2 N) to the RHS (range (N-1))
  have hcard : (Finset.Icc 2 N).card = N - 1 := by
    rw [show N - 1 = (Finset.range (N - 1)).card from (Finset.card_range _).symm]
    apply Finset.card_bij (fun b _ => b - 2)
    · -- b ∈ Icc 2 N → b - 2 ∈ range (N-1)
      intro b hb
      rw [Finset.mem_Icc] at hb
      rw [Finset.mem_range]
      omega
    · -- injectivity: b - 2 = c - 2 → b = c  (with b,c ≥ 2)
      intro b hb c hc h
      rw [Finset.mem_Icc] at hb hc
      omega
    · -- surjectivity: given i ∈ range (N-1), find b ∈ Icc 2 N with b - 2 = i
      intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨i + 2, ?_, by omega⟩
      rw [Finset.mem_Icc]
      omega
  exact hcard

/-! ## 8. Diagonal Embedding and Equivalence ≡∞ -/

/-- The **diagonal embedding** ι sends every natural to its vector of radical remainders:
`diagEmbed a n = radRem n a`. It is the "infinite signature" of a in the space Aod∞. -/
def diagEmbed (a : ℕ) : ℕ → ℕ := fun n => radRem n a

/-- The **definitive equivalence relation** ≡∞: `a ≡∞ b` if and only if
`radRem n a = radRem n b` for every degree `n ≥ 2`. -/
def aodInfEquiv (a b : ℕ) : Prop :=
  ∀ n, 2 ≤ n → radRem n a = radRem n b

scoped notation:50 a " ≡∞ " b => aodInfEquiv a b

theorem aodInfEquiv_refl (a : ℕ) : a ≡∞ a :=
  fun _ _ => rfl

theorem aodInfEquiv_symm {a b : ℕ} (h : a ≡∞ b) : b ≡∞ a :=
  fun n hn => (h n hn).symm

theorem aodInfEquiv_trans {a b c : ℕ} (h₁ : a ≡∞ b) (h₂ : b ≡∞ c) : a ≡∞ c :=
  fun n hn => (h₁ n hn).trans (h₂ n hn)

theorem aodInfEquiv_isEquivalence : Equivalence aodInfEquiv :=
  ⟨aodInfEquiv_refl, fun h => aodInfEquiv_symm h, fun h₁ h₂ => aodInfEquiv_trans h₁ h₂⟩

/-- The relation ≡∞ implies the equality of the radical profiles. -/
theorem aodInfEquiv_same_profile {a b : ℕ} (h : a ≡∞ b) : Π∞(a) = Π∞(b) := by
  ext n
  simp only [mem_radicalProfile_iff]
  constructor
  · rintro ⟨hn, hr⟩
    exact ⟨hn, (h n hn) ▸ hr⟩
  · rintro ⟨hn, hr⟩
    exact ⟨hn, (h n hn).symm ▸ hr⟩

/-! ## 9. Corrected Conjectures C1–C5 -/

/-!
### Fundamental Mathematical Correction: C1 and C5 Require Restriction to ≥ 2

Conjectures C1 and C5 are FALSE in the
original formulation over all of ℕ. The counterexample is `0 ≡∞ 1`:

- `radRem n 0 = 0` for every n ≥ 2 (since 0 = 0^n)
- `radRem n 1 = 0` for every n ≥ 2 (since 1 = 1^n)
- Hence `diagEmbed 0 = diagEmbed 1` (both functions are identically 0)
- But `0 ≠ 1`

The correct version is: `diagEmbed` is injective on `{a : ℕ | 2 ≤ a}`, and this
version is **provable** via the private lemmas `lt_two_pow_self` and `radRem_eq_pred`.
-/

/-- **Proved Theorem**: 0 and 1 are ≡∞-equivalent.
This shows that ≡∞ is NOT the identity over all of ℕ (C5 is false in general). -/
theorem aodInfEquiv_zero_one : (0 : ℕ) ≡∞ 1 := by
  intro n hn
  have h0 : n ∈ Π∞(0) := zero_mem_all_profile n hn
  have h1 : n ∈ Π∞(1) := one_mem_all_profile n hn
  simp [mem_radicalProfile_iff] at h0 h1
  omega

/-- **Lemma**: diagEmbed 0 = diagEmbed 1 (same infinite signature). -/
theorem diagEmbed_zero_eq_one : diagEmbed 0 = diagEmbed 1 := by
  funext n
  simp [diagEmbed, radRem, irootN]
  -- For n = 0: irootN 0 a = 1 by convention, radRem 0 a = a - 1. For a=0: 0-1=0, for a=1: 1-1=0.
  -- For n ≠ 0: 0^n = 0 and 1^n = 1, irootN n 0 = 0 and irootN n 1 = 1.
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    -- irootAux n 0 0 = 0 and irootAux n 1 1 = 1
    simp [irootAux]

/-- **Central Theorem (C1 Corrected)**: `diagEmbed` is injective on `{a | 2 ≤ a}`.
Proof: for distinct a, b ≥ 2, we choose n = a + b. Then:
- a < 2^a ≤ 2^(a+b) = 2^n (by `lt_two_pow_self`)
- b < 2^b ≤ 2^(a+b) = 2^n (likewise)
- Hence `radRem n a = a - 1` and `radRem n b = b - 1` (by `radRem_eq_pred`)
- If diagEmbed a = diagEmbed b, then a - 1 = b - 1, i.e. a = b. -/
theorem diagEmbed_injective_on_ge_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : diagEmbed a = diagEmbed b) : a = b := by
  -- Choose the degree n = a + b
  have hn : 2 ≤ a + b := by omega
  -- We prove a < 2^(a+b)
  have ha_lt : a < 2 ^ (a + b) :=
    calc a < 2 ^ a       := lt_two_pow_self a
         _ ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- We prove b < 2^(a+b)
  have hb_lt : b < 2 ^ (a + b) :=
    calc b < 2 ^ b       := lt_two_pow_self b
         _ ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- radRem (a+b) a = a - 1
  have hremA : radRem (a + b) a = a - 1 := radRem_eq_pred hn ha ha_lt
  -- radRem (a+b) b = b - 1
  have hremB : radRem (a + b) b = b - 1 := radRem_eq_pred hn hb hb_lt
  -- diagEmbed a (a+b) = diagEmbed b (a+b)
  have heq : diagEmbed a (a + b) = diagEmbed b (a + b) := congr_fun h (a + b)
  simp only [diagEmbed] at heq
  rw [hremA, hremB] at heq
  omega

/-- **Corollary**: diagEmbed is not injective over all of ℕ. -/
theorem diagEmbed_not_injective : ¬ Function.Injective diagEmbed := by
  intro h
  have := h diagEmbed_zero_eq_one
  exact absurd this (by norm_num)

/-- **Conjecture C5 (Corrected)**: ≡∞ is the identity on `{a | 2 ≤ a}`.
Direct proof: we use n = a+b ≥ 2 to extract radRem (a+b) a = a-1
and radRem (a+b) b = b-1 from h, concluding a = b without funext. -/
theorem aodInfEquiv_is_identity_ge_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a ≡∞ b) : a = b := by
  -- Choose n = a + b ≥ 2, so that a < 2^n and b < 2^n
  have hn : 2 ≤ a + b := by omega
  have ha_lt : a < 2 ^ (a + b) :=
    calc a < 2 ^ a       := lt_two_pow_self a
         _ ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb_lt : b < 2 ^ (a + b) :=
    calc b < 2 ^ b       := lt_two_pow_self b
         _ ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- radRem (a+b) a = a-1  e  radRem (a+b) b = b-1
  have hremA : radRem (a + b) a = a - 1 := radRem_eq_pred hn ha ha_lt
  have hremB : radRem (a + b) b = b - 1 := radRem_eq_pred hn hb hb_lt
  -- h : a ≡∞ b, i.e. ∀ n ≥ 2, radRem n a = radRem n b
  have heq := h (a + b) hn
  rw [hremA, hremB] at heq
  omega

/-- **C2 — Asymptotic Density of Weak-Zeros** (left with an intentional sorry).
The number of weak-zeros in [1, N] is asymptotic to √N.

Note: this is a classical result of number theory (Hardy-Wright §18.1):
the number of perfect powers in [1, N] is ~ √N, dominated by squares.
The Lean formalization of this fact adds no original scientific value
to the project; C2 serves exclusively as a calibration lemma to confirm
that `isWeakZero` captures the correct notion. Do not invest time in the proof:
it stays deliberately open as a classical result (Hardy-Wright). The sorrys once
listed here as priorities --- `crtRadicale_suriettivo` and `capAddStar_well_defined`
--- are now both proved; the only formalization `sorry` still
relevant is `catalan_in_AodStar` (awaiting the porting of Mihailescu into Mathlib4). -/
theorem weakZero_count_asymptotic :
    ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.Icc 1 N).filter (fun a => 0 < radWeight a N)).card : ℝ) /
      (Nat.sqrt N : ℝ) ∈ Set.Ioo (1 - ε) (1 + ε) := by
  sorry -- classical (Hardy-Wright §18.1); formalization not a priority

/-- **Stabilization Theorem for Non-Weak-Zeros**:
If `a ≥ 2` is not a perfect power, the sequence `n ↦ radRem n a`
eventually stabilizes at the value `a - 1`. -/
theorem nonPerfectPow_radRem_stabilizes {a : ℕ} (ha2 : 2 ≤ a) (_ha : ¬ isWeakZero a) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, radRem n a = a - 1 := by
  -- For n > log₂(a) we have irootN n a = 1 (from irootN_eq_one)
  -- hence radRem n a = a - 1^n = a - 1 (from radRem_eq_pred)
  use Nat.log 2 a + 1
  intro n hn
  have hlog : 1 ≤ Nat.log 2 a := Nat.log_pos (by norm_num) ha2
  have hlt : a < 2 ^ n :=
    (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a).trans_le
      (Nat.pow_le_pow_right (by norm_num) hn)
  have hiroot : irootN n a = 1 := irootN_eq_one (by omega) ha2 hlt
  simp [radRem, hiroot]

/-! ## 10. Appendix: Connections with the Pillai Problem -/

/-- **Remark (Connection with Pillai)**:
The condition `n ∈ Π∞(a + b)` is equivalent to requiring that `a + b` be a perfect
n-th power. This is the core of the Pillai problem: `x^p - y^q = c`.
The Aod∞ language provides a reformulation: `n ∈ Π∞(a + b) ↔ ∃ k, k^n = a + b`. -/
theorem pillai_reformulation (a b n : ℕ) (hn : 2 ≤ n) :
    n ∈ Π∞(a + b) ↔ ∃ k, k ^ n = a + b :=
  mem_radicalProfile_iff_isPP hn

/-- **Pillai — Gap between Consecutive Powers**: for every n ≥ 1, consecutive n-th
powers are strictly increasing: `k^n < (k+1)^n`.
Connection with `growingFrontier` from the base Operationistic Fields. -/
theorem pillai_gap_grows (n : ℕ) (hn : 2 ≤ n) :
    ∀ k : ℕ, k ^ n < (k + 1) ^ n := by
  intro k
  exact Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega : n ≠ 0)

end AodInfinito
