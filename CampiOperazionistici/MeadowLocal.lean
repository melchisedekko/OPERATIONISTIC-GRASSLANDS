/-
  MeadowLocal.lean
  Local Meadow Structure on CapChap(n,k): the M3-good set and the field theorem
  Operational Fields — Theory of Aod_n (not of Aod★)
  Author: Alessandro Sgarbi — 2026-03-19
  Paper: §12 (Local Meadow Structures)

  Dependencies:
  - `GroupStructure.lean` — capMul, capMulPow, capGap, toZMod, toZMod_injective,
                             toZMod_mul, toZMod_capMulPow, capMul_distrib_left

  File structure:
  § 1. M3-good set: definition and characterization
  § 2. Cardinality of G(n,k): closed-form formula (computational check)
  § 3. Local meadow: chapter structure theorems
  § 4. Corollaries

  Note: This file concerns exclusively the structure of CapChap(n,k) ≅ Fin(capGap n k).
  It does not depend on AodStar.lean and does not touch Aod★ in any way.
-/

import CampiOperazionistici.GroupStructure
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic

open CampiOperazionistici

namespace MeadowLocal

-- ================================================================
-- § 1. M3-good Set: Definition and Characterization
-- ================================================================

/-!
### The Bergstra–Tucker M3 identity

In CapChap(n,k) with Fermat inversion `capMulInv r = r^{g-2}` (via capMulPow),
the reflexive meadow identity is:

    r ⊗ r^{g-2} ⊗ r = r

Through the isomorphism `toZMod`, this translates into ZMod g as:

    a · a^{g-2} · a = a   ↔   a^g = a

**Characterization theorem:**
    r ∈ 𝒢(n,k)  ↔  (toZMod n k r)^g ≡ toZMod n k r  in ZMod g

where g = capGap n k.

**Corollary (field → universal M3):** If g is prime, a^g = a for every a
(Fermat's Little Theorem), so M3 holds on all of CapChap(n,k).
**Corollary (composite → partial M3):** If g is composite, 𝒢(n,k) is a
proper subset: the elements with gcd(θ_k(r), g) > 1 and θ_k(r)^g ≢ θ_k(r)
do not satisfy M3.
-/

/-- Boolean predicate for the M3 identity in CapChap(n,k) (works directly on ℕ). -/
def isM3GoodBool (g r : ℕ) : Bool :=
  r * (r ^ (g - 2) % g) % g * r % g == r % g

/-- M3-good set of chapter (n,k). -/
def m3GoodSet (n k : ℕ) (_hn : n ≠ 0) : List ℕ :=
  (List.range (capGap n k)).filter (isM3GoodBool (capGap n k))

-- Computational checks
#eval m3GoodSet 2 1 (by norm_num)  -- all of Fin(3), g=3 prime
#eval m3GoodSet 4 1 (by norm_num)  -- proper subset of Fin(15), g=15=3·5 composite
#eval m3GoodSet 5 1 (by norm_num)  -- all of Fin(31), g=31 prime

/-- M3-good set as a Finset over Fin(g) — primary definition on the correct type.
    Computable: `isM3GoodBool` returns Bool, `Finset.univ` over `Fin g` is finite. -/
def m3GoodFinset (n k : ℕ) (_hn : n ≠ 0) : Finset (Fin (capGap n k)) :=
  Finset.univ.filter (fun r => isM3GoodBool (capGap n k) r.val)

/-- Cardinality of the M3-good set. -/
def m3GoodCount (n k : ℕ) (hn : n ≠ 0) : ℕ :=
  (m3GoodSet n k hn).length

/-- 0 is always M3-good: 0 · _ · 0 = 0 (mod g). -/
theorem zero_isM3Good (n k : ℕ) (_hn : n ≠ 0) :
    isM3GoodBool (capGap n k) 0 = true := by
  simp [isM3GoodBool]

/-!
### 1.1 Theorem: M3(r) ↔ θ_k(r)^g = θ_k(r) in ZMod g

The proof uses `toZMod_mul` and `toZMod_capMulPow` to transport the identity
from CapChap to ZMod g, where the algebra is that of the standard CommRing.
-/

/-- Characterization: M3 holds for r ↔ (toZMod r)^g = toZMod r in ZMod g.
    Equivalence: r ⊗ r^{g-2} ⊗ r = r  ↔  a · a^{g-2} · a = a  ↔  a^g = a.
    Requires g ≥ 2 for the subtraction in ℕ. -/
theorem isM3Good_iff_pow_capGap (n k : ℕ) (hn : n ≠ 0)
    (hg : 2 ≤ capGap n k)
    (r : Fin (capGap n k)) :
    let g := capGap n k
    let a := toZMod n k r
    capMul n k hn (capMul n k hn r (capMulPow n k hn (g - 2) r)) r = r
    ↔ a ^ g = a := by
  intro g a
  have hg2 : 2 ≤ g := hg
  have key : ∀ (x : ZMod (capGap n k)),
      x * x ^ (capGap n k - 2) * x = x ^ (capGap n k) := by
    intro x
    have heq : 1 + (capGap n k - 2) + 1 = capGap n k := by omega
    have expand : x ^ (1 + (capGap n k - 2) + 1) = x * x ^ (capGap n k - 2) * x := by
      simp [pow_add, pow_one, mul_assoc]
    calc x * x ^ (capGap n k - 2) * x
        = x ^ (1 + (capGap n k - 2) + 1) := expand.symm
      _ = x ^ (capGap n k)               := by congr 1
  constructor
  · intro h
    have hmul := congr_arg (toZMod n k) h
    simp only [toZMod_mul, toZMod_capMulPow] at hmul
    exact (key (toZMod n k r)).symm.trans hmul
  · intro h
    apply toZMod_injective n k hn
    simp only [toZMod_mul, toZMod_capMulPow]
    exact (key (toZMod n k r)).trans h

/-!
### 1.2 Universal M3 if and only if the chapter is a field
-/

/-- Fermat's Little Theorem in ZMod g: a^g = a for every a when g is prime. -/
private lemma pow_card_of_prime (g : ℕ) (hg : Nat.Prime g)
    (a : ZMod g) : a ^ g = a := by
  haveI : Fact (Nat.Prime g) := ⟨hg⟩
  haveI : NeZero g := ⟨hg.pos.ne'⟩
  exact ZMod.pow_card a

/-- If g is prime, M3 holds for every r ∈ Fin(g).
    Proof: a^g = a (Fermat) → r ⊗ r^{g-2} ⊗ r = r via isM3Good_iff_pow_capGap. -/
theorem m3_universal_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k))
    (r : Fin (capGap n k)) :
    capMul n k hn (capMul n k hn r (capMulPow n k hn (capGap n k - 2) r)) r = r :=
  (isM3Good_iff_pow_capGap n k hn hprime.two_le r).mpr (pow_card_of_prime _ hprime _)

-- If g is composite with a divisor d, 1 < d < g,
-- then there exist elements r for which M3 fails.
-- Computational data: g=15 → 6 failures; g=65 → 40 failures.

/-- Bridge lemma: if g is prime, then `isM3GoodBool g r = true` for every r < g.
    Proof: in ZMod g (a field), a^g = a for every a (Fermat's Little Theorem).
    The boolean computation in ℕ coincides with the calculation in ZMod g. -/
private lemma isM3GoodBool_of_prime {g : ℕ} (hg : Nat.Prime g) (r : ℕ) (hr : r < g) :
    isM3GoodBool g r = true := by
  haveI : Fact (Nat.Prime g) := ⟨hg⟩
  haveI : NeZero g := ⟨hg.pos.ne'⟩
  simp only [isM3GoodBool, beq_iff_eq]
  have key : (r : ZMod g) * (r : ZMod g) ^ (g - 2) * (r : ZMod g) = (r : ZMod g) := by
    have hge : 2 ≤ g := hg.two_le
    have step1 : (r : ZMod g) ^ (1 + (g - 2) + 1) = (r : ZMod g) * (r : ZMod g) ^ (g - 2) * (r : ZMod g) := by
      simp only [pow_add, pow_one]
    have step2 : (r : ZMod g) ^ (1 + (g - 2) + 1) = (r : ZMod g) ^ g := by
      congr 1; omega
    rw [← step1, step2]; exact ZMod.pow_card _
  have lhs_cast : ((r * (r ^ (g - 2) % g) % g * r % g : ℕ) : ZMod g)
      = (r : ZMod g) * (r : ZMod g) ^ (g - 2) * (r : ZMod g) := by
    push_cast [ZMod.natCast_mod]; ring
  have rhs_cast : ((r % g : ℕ) : ZMod g) = (r : ZMod g) := ZMod.natCast_mod r g
  have lhs_val : ZMod.val ((r * (r ^ (g - 2) % g) % g * r % g : ℕ) : ZMod g) = r := by
    rw [lhs_cast, key]
    exact ZMod.val_natCast_of_lt hr
  have rhs_val : ZMod.val ((r % g : ℕ) : ZMod g) = r := by
    rw [rhs_cast]
    exact ZMod.val_natCast_of_lt hr
  have lhs_lt : r * (r ^ (g - 2) % g) % g * r % g < g := Nat.mod_lt _ hg.pos
  have rhs_lt : r % g < g := Nat.mod_lt _ hg.pos
  have : ZMod.val ((r * (r ^ (g - 2) % g) % g * r % g : ℕ) : ZMod g)
       = ZMod.val ((r % g : ℕ) : ZMod g) := by rw [lhs_val, rhs_val]
  rwa [ZMod.val_natCast_of_lt lhs_lt, ZMod.val_natCast_of_lt rhs_lt] at this

/-- If g is prime, M3 holds for g-1 (the maximal element). -/
theorem maxElem_isM3Good_of_prime (n k : ℕ) (hn : n ≠ 0)
    [hprime : Fact (Nat.Prime (capGap n k))] :
    isM3GoodBool (capGap n k) (capGap n k - 1) = true :=
  isM3GoodBool_of_prime hprime.out _ (Nat.sub_lt (capGap_pos n k hn) Nat.one_pos)

/-- If g is prime, all elements satisfy M3: |𝒢(n,k)| = g. -/
theorem m3GoodCount_eq_capGap_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodCount n k hn = capGap n k := by
  unfold m3GoodCount m3GoodSet
  have hall : ∀ r ∈ List.range (capGap n k), isM3GoodBool (capGap n k) r = true := by
    intro r hr
    rw [List.mem_range] at hr
    exact isM3GoodBool_of_prime hprime r hr
  rw [List.filter_eq_self.mpr hall]
  simp [List.length_range]

-- ================================================================
-- § 2. Cardinality: Closed-Form Formula for Square-Free g
-- ================================================================

/-!
### Product formula

When `g = capGap n k` is square-free, the cardinality is:

$$|\mathcal{G}(n,k)| = \prod_{p \mid g,\, p \text{ prime}} \bigl(1 + \gcd(g-1,\, p-1)\bigr)$$

**Derivation:** Via CRT, the solutions of `a^g = a` in ZMod g are counted
component by component. In each ZMod(p) with p | g:
- `a = 0`: 1 solution.
- `a ≠ 0`: `a^{g-1} = 1`, i.e. `ord(a) | (g-1)`, hence `gcd(g-1, p-1)` solutions.
Total for p: `1 + gcd(g-1, p-1)`. By CRT (g square-free): product.

**Computational check:**
| g  | fattori | formula        | |𝒢| |
|----|---------|----------------|------|
| 3  | 3       | 1+gcd(2,2)=3   | 3    |
| 15 | 3·5     | 3·3=9          | 9    |
| 65 | 5·13    | 5·5=25         | 25   |
-/

#eval
  -- Check formula on a few chapters
  [(3, [3]), (7, [7]), (15, [3,5]), (65, [5,13])].map
    fun (g, factors) =>
      let formula := factors.foldl (fun acc p =>
        acc * (1 + Nat.gcd (g - 1) (p - 1))) 1
      (g, formula)
-- Expected: (3,3), (7,7), (15,9), (65,25)

-- ================================================================
-- § 2b. Layer A — Counting solutions in ZMod p (without CRT)
-- ================================================================

/-!
### Layer A: solutions of `a^g = a` in `ZMod p` for p prime

In `ZMod p` (p prime), the solutions of `a^g = a` are:
- `a = 0`: 1 solution.
- `a ≠ 0` (unit): `a^(g-1) = 1`, i.e. `ord(a) | gcd(g-1, p-1)`.
  The group `(ZMod p)ˣ` is cyclic of order `p-1`, hence
  the solutions are `gcd(g-1, p-1)`.
Total: `1 + gcd(g-1, p-1)`.

**Required Mathlib dependencies:**
- `IsCyclic.card_pow_eq_one_le` (available)
- `sum_card_orderOf_eq_card_pow_eq_one` (available)
- Lemma: `#{u : Gˣ | u^d = 1} = gcd(d, |G|)` — to be built from `IsCyclic`
-/

/-- Key lemma: for a ≠ 0 in ZMod p (prime), a^g = a ↔ a^(g-1) = 1. -/
private lemma pow_eq_self_iff_pow_pred_eq_one {p : ℕ} (hp : Nat.Prime p)
    (g : ℕ) (hg : 1 ≤ g) (a : ZMod p) (hne : a ≠ 0) :
    a ^ g = a ↔ a ^ (g - 1) = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  constructor
  · intro h
    -- a^g = a → a^(g-1) * a = a → a^(g-1) = 1 (cancellation since a ≠ 0)
    have hstep : a ^ (g - 1) * a = a := by
      have : a ^ (g - 1) * a = a ^ g := by
        rw [← pow_succ]; congr 1; omega
      rw [this, h]
    exact mul_right_cancel₀ hne (by rw [hstep, one_mul])
  · intro h
    -- a^(g-1) = 1 → a^g = a^(g-1) * a = 1 * a = a
    have : a ^ g = a ^ (g - 1) * a := by
      rw [← pow_succ]; congr 1; omega
    rw [this, h, one_mul]

/-- Cardinality of `{u : (ZMod p)ˣ | u^d = 1} = gcd(d, p-1)`.
    The underlying fact — in a cyclic group of order `n`, `#{x | x^d = 1} = gcd(d, n)`
    — is not available in Mathlib as a single standalone lemma; it is assembled here
    from `IsCyclic.card_powMonoidHom_ker` and the cyclic structure of `(ZMod p)ˣ`.
    Fully proved (no `sorry`). -/
private lemma card_units_pow_eq_one_eq_gcd {p : ℕ} (hp : Nat.Prime p) (d : ℕ)
    [Fact (Nat.Prime p)] [NeZero p] :
    (Finset.univ.filter (fun u : (ZMod p)ˣ => u ^ d = 1)).card =
    Nat.gcd d (p - 1) := by
  -- (ZMod p)ˣ is cyclic of order p-1
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  -- #{u | u^d = 1} as a Finset = Nat.card of the ker of powMonoidHom d
  have hker_card : Nat.card (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).ker =
      (Nat.card (ZMod p)ˣ).gcd d := IsCyclic.card_powMonoidHom_ker (G := (ZMod p)ˣ) d
  -- Nat.card (ZMod p)ˣ = p - 1
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  -- The Finset.filter and the ker of powMonoidHom d have the same cardinality
  have hfilter : (Finset.univ.filter (fun u : (ZMod p)ˣ => u ^ d = 1)).card =
      Nat.card (powMonoidHom d : (ZMod p)ˣ →* (ZMod p)ˣ).ker := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨u, hu⟩ => ⟨u, MonoidHom.mem_ker.mpr (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simpa [powMonoidHom_apply])⟩
      invFun := fun ⟨u, hu⟩ => ⟨u, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have := MonoidHom.mem_ker.mp hu
          simpa [powMonoidHom_apply] using this⟩
      left_inv := fun u => by simp
      right_inv := fun u => by simp }
  rw [hfilter, hker_card, hcard]
  simp [Nat.gcd_comm]

/-- In ZMod p (p prime), the solutions of `a^g = a` are exactly `1 + gcd(g-1, p-1)`.
    Layer A of the M3 product formula.
    Depends on `card_units_pow_eq_one_eq_gcd` (proved above). -/
theorem card_pow_eq_self_zmod_prime {p : ℕ} (hp : Nat.Prime p) (g : ℕ) (hg : 1 ≤ g)
    [Fact (Nat.Prime p)] [NeZero p] :
    (Finset.univ.filter (fun a : ZMod p => a ^ g = a)).card =
    1 + Nat.gcd (g - 1) (p - 1) := by
  -- Partition: {a | a^g = a} = {0} ∪ {a ≠ 0 | a^g = a}
  have hpart : (Finset.univ (α := ZMod p)).filter (fun a => a ^ g = a) =
      insert 0 ((Finset.univ (α := ZMod p)).filter (fun a => a ≠ 0 ∧ a ^ g = a)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro ha
      by_cases h0 : a = 0
      · left; exact h0
      · right; exact ⟨h0, ha⟩
    · rintro (rfl | ⟨_, ha⟩)
      · exact zero_pow (by omega)
      · exact ha
  have h0_notin : (0 : ZMod p) ∉
      (Finset.univ (α := ZMod p)).filter (fun a => a ≠ 0 ∧ a ^ g = a) := by simp
  -- Note: `hpart` uses `Finset.univ (α := ZMod p)` but the goal uses `Finset.univ`
  -- (same thing). We use `conv` to rewrite only the left-hand side.
  have h0_notin' : (0 : ZMod p) ∉
      (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ^ g = a)) := by simp
  have hpart' : Finset.univ.filter (fun a : ZMod p => a ^ g = a) =
      insert 0 (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ^ g = a)) := hpart
  rw [hpart', Finset.card_insert_of_notMem h0_notin']
  -- Reduce {a ≠ 0 | a^g = a} to {a ≠ 0 | a^(g-1) = 1}
  have hequiv : Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ^ g = a) =
      Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ^ (g - 1) = 1) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, h⟩; exact ⟨hne, (pow_eq_self_iff_pow_pred_eq_one hp g hg a hne).mp h⟩
    · rintro ⟨hne, h⟩; exact ⟨hne, (pow_eq_self_iff_pow_pred_eq_one hp g hg a hne).mpr h⟩
  rw [hequiv]
  -- Bijection {a : ZMod p | a ≠ 0 ∧ a^(g-1) = 1} ↔ {u : (ZMod p)ˣ | u^(g-1) = 1}
  -- via: a ≠ 0 ↔ IsUnit a in ZMod p (finite field)
  have hcard_eq : (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ^ (g - 1) = 1)).card =
      (Finset.univ.filter (fun u : (ZMod p)ˣ => u ^ (g - 1) = 1)).card := by
    -- In ZMod p (a field), a ≠ 0 ↔ IsUnit a. Bijection via Units.val / IsUnit.unit.
    haveI : Fact (Nat.Prime p) := ‹_›
    -- isUnit a ↔ a ≠ 0 in a GroupWithZero (ZMod p is a field, hence a GroupWithZero)
    have isUnit_iff : ∀ a : ZMod p, IsUnit a ↔ a ≠ 0 := by
      intro a; exact isUnit_iff_ne_zero
    apply Finset.card_bij (fun a ha => (isUnit_iff a |>.mpr
        (by simp [Finset.mem_filter] at ha; exact ha.1)).unit)
    · -- membership: u^(g-1) = 1
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have hunit := (isUnit_iff a |>.mpr ha.1)
      -- Reduce the equality of units to an equality of values
      ext1
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact ha.2
    · -- injectivity
      intro a₁ ha₁ a₂ ha₂ heq
      have := congr_arg (Units.val) heq
      simpa using this
    · -- surjectivity
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine ⟨(u : ZMod p), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Units.ne_zero u, ?_⟩
        rw [← Units.val_pow_eq_pow_val, hu]; simp
      · ext1
        simp
  rw [hcard_eq]
  -- Conclude via card_units_pow_eq_one_eq_gcd (proved above, §2b)
  have := card_units_pow_eq_one_eq_gcd hp (g - 1)
  omega

/-!
### § 2c. Product formula for square-free g

**Discovery:** The two ingredients of the previous comment ("CRT for ZMod" and "counting in
ZMod p") were **both already present in the project**:
- `card_pow_eq_self_zmod_prime` (§2b, above) gives exactly `1 + gcd(g-1, p-1)` for every
  prime factor `p | g`.
- `ZMod.chineseRemainder` is already used successfully in `fiveDirections.lean` §5
  (`crtRadicale_suriettivo`, line ~650).

The missing piece was the **composition**: multiplying the counts component by component
when `g` is square-free. This requires knowing that the solutions of `a^g = a` in `ZMod g`
split, via CRT, as the product of the solutions in each `ZMod p`.

The key theorem is the **multiplicativity of the cardinality** with respect to the decomposition
`ZMod (p * q) ≅ ZMod p × ZMod q` (for `p`, `q` coprime), which allows induction on the
list of prime factors of `g`.

**Proof structure:**
1. Base case: `g` prime — already proved as `card_pow_eq_self_zmod_prime`.
2. Inductive step: if `g = p * m` with `p` prime, `p ∤ m`, then
   `|{a : ZMod g | a^g = a}| = |{a : ZMod p | a^g = a}| * |{a : ZMod m | a^g = a}|`
   via the isomorphism `ZMod.chineseRemainder (Nat.Coprime.pow_left ...)`.
-/

-- ================================================================
-- § 2c. Product Formula for Square-Free g
-- ================================================================

/-- Multiplicativity: if `Nat.Coprime m₁ m₂`, the solutions of `a^g = a` in `ZMod (m₁ * m₂)`
    decompose as a product via CRT. Multiplicative cardinality. -/
private lemma card_pow_eq_self_mul_of_coprime (m₁ m₂ g : ℕ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hcop : Nat.Coprime m₁ m₂) :
    haveI : NeZero m₁ := ⟨hm₁.ne'⟩
    haveI : NeZero m₂ := ⟨hm₂.ne'⟩
    haveI : NeZero (m₁ * m₂) := ⟨(Nat.mul_pos hm₁ hm₂).ne'⟩
    (Finset.univ.filter (fun a : ZMod (m₁ * m₂) => a ^ g = a)).card =
    (Finset.univ.filter (fun a : ZMod m₁ => a ^ g = a)).card *
    (Finset.univ.filter (fun a : ZMod m₂ => a ^ g = a)).card := by
  haveI hne1 : NeZero m₁ := ⟨hm₁.ne'⟩
  haveI hne2 : NeZero m₂ := ⟨hm₂.ne'⟩
  haveI hne12 : NeZero (m₁ * m₂) := ⟨(Nat.mul_pos hm₁ hm₂).ne'⟩
  -- The CRT isomorphism: ZMod (m₁ * m₂) ≅ ZMod m₁ × ZMod m₂
  let iso := ZMod.chineseRemainder hcop
  -- The component-wise casts
  let π₁ := ZMod.castHom (Nat.dvd_mul_right m₁ m₂) (ZMod m₁)
  let π₂ := ZMod.castHom (Nat.dvd_mul_left m₂ m₁) (ZMod m₂)
  -- Transport the filter through iso: a^g=a ↔ (iso a).1^g=(iso a).1 ∧ (iso a).2^g=(iso a).2
  have hcard : (Finset.univ.filter (fun a : ZMod (m₁ * m₂) => a ^ g = a)).card =
      (Finset.univ.filter (fun p : ZMod m₁ × ZMod m₂ => p.1 ^ g = p.1 ∧ p.2 ^ g = p.2)).card := by
    apply Finset.card_bij (fun a _ => iso a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have hiso1 : (iso a).1 = π₁ a := by
        simp [iso, π₁, ZMod.chineseRemainder]
      have hiso2 : (iso a).2 = π₂ a := by
        simp [iso, π₂, ZMod.chineseRemainder]
      constructor
      · rw [hiso1, ← map_pow π₁, ha]
      · rw [hiso2, ← map_pow π₂, ha]
    · intro a₁ _ a₂ _ heq
      exact iso.injective heq
    · intro ⟨b₁, b₂⟩ hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      -- Membership: iso.symm (b₁,b₂) ^ g = iso.symm (b₁,b₂)
      -- iso is a ring iso, hence iso.symm commutes with pow.
      -- iso (x^g) = (iso x)^g, hence iso.symm ((b₁,b₂)^g) = iso.symm (b₁^g, b₂^g)
      have hmem : iso.symm (b₁, b₂) ^ g = iso.symm (b₁, b₂) := by
        apply iso.injective
        rw [map_pow]
        simp only [RingEquiv.apply_symm_apply]
        ext
        · simp [hb.1]
        · simp [hb.2]
      refine ⟨iso.symm (b₁, b₂), by simp [Finset.mem_filter, hmem], ?_⟩
      -- goal: iso (iso.symm (b₁, b₂)) = (b₁, b₂)
      simp [iso]
  rw [hcard, ← Finset.card_product]
  -- Identity bijection between filter over product and product of filters
  apply Finset.card_bij (fun p _ => (p.1, p.2))
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h.1, h.2⟩
  · intro a _ b _ h; exact Prod.ext (congr_arg Prod.fst h) (congr_arg Prod.snd h)
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨a, b⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h.1, h.2⟩, rfl⟩

--generalized to arbitrary exponent e (fixes the induction step where IH had wrong exponent)
/-- Generalized: for g square-free and arbitrary exponent e ≥ 1, the cardinality of
    {a : ZMod g | a^e = a} is ∏_{p | g} (1 + gcd(e-1, p-1)).
    The induction is on g with e fixed, avoiding the problem in the inductive step. -/
private lemma card_pow_eq_self_zmod_squarefree_gen (g e : ℕ) (hg : 1 ≤ g) (he : 1 ≤ e)
    (hsf : Squarefree g) [hgne : NeZero g] :
    (Finset.univ.filter (fun a : ZMod g => a ^ e = a)).card =
    g.primeFactors.prod (fun p => 1 + Nat.gcd (e - 1) (p - 1)) := by
  revert hg hsf hgne
  induction g using Nat.strongRecOn' with
  | h g ih =>
  intro hg hsf hgne
  -- Base case g = 1
  by_cases hg1 : g = 1
  · subst hg1
    simp only [Nat.primeFactors_one, Finset.prod_empty]
    -- ZMod 1 is a type with a single element; the filter has card 1
    have : (Finset.univ.filter (fun a : ZMod 1 => a ^ e = a)).card = 1 := by
      have hfull : Finset.univ.filter (fun a : ZMod 1 => a ^ e = a) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intros a _
        exact Subsingleton.elim _ _
      rw [hfull]
      simp
    exact this
  -- Inductive step: p prime with p | g
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
  obtain ⟨m, hm⟩ := hpdvd
  have hm_pos : 0 < m := by
    cases m with | zero => simp at hm; omega | succ m => exact Nat.succ_pos m
  -- g square-free and g = p * m → Coprime p m
  have hcop : Nat.Coprime p m := by
    rw [Nat.Coprime]
    by_contra hbad
    have hpeq : Nat.gcd p m = p :=
      (hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left p m)).resolve_left (fun h => hbad h)
    have hpdvdm : p ∣ m := hpeq ▸ Nat.gcd_dvd_right p m
    obtain ⟨k, hk⟩ := hpdvdm
    have hpsq : p * p ∣ g := ⟨k, by rw [hm, hk]; ring⟩
    exact absurd hpsq (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
  have hm1 : 1 ≤ m := hm_pos
  have hmsf : Squarefree m := by
    intro x hx; apply hsf x; exact hx.trans ⟨p, by linarith [hm]⟩
  haveI hmne : NeZero m := ⟨hm_pos.ne'⟩
  haveI hpne : NeZero p := ⟨hp.pos.ne'⟩
  haveI hfact : Fact (Nat.Prime p) := ⟨hp⟩
  have hm_lt : m < g := by rw [hm]; nlinarith [hp.two_le]
  -- IH applied to (m, e): e is fixed, so there is no exponent mismatch
  have ihm := ih m hm_lt hm1 hmsf
  subst hm
  -- Split the count over ZMod(p*m) → ZMod p × ZMod m
  rw [card_pow_eq_self_mul_of_coprime p m e hp.pos hm_pos hcop,
      card_pow_eq_self_zmod_prime hp e he,
      ihm]
  -- Recombine the prime factors
  have hp_not_m : p ∉ m.primeFactors := by
    simp only [Nat.mem_primeFactors, not_and]
    intro _ hdvd _
    have : p ∣ Nat.gcd p m := Nat.dvd_gcd dvd_rfl hdvd
    rw [hcop] at this
    exact absurd (Nat.le_of_dvd Nat.one_pos this) (by linarith [hp.two_le])
  have hdisj : Disjoint ({p} : Finset ℕ) m.primeFactors :=
    Finset.disjoint_singleton_left.mpr hp_not_m
  rw [Nat.primeFactors_mul hp.pos.ne' hm_pos.ne', hp.primeFactors,
      Finset.prod_union hdisj, Finset.prod_singleton]

/-- Product formula for g square-free: the solutions of `a^g = a` in `ZMod g` are counted
    as a product over all prime factors of `g`. -/
theorem card_pow_eq_self_zmod_squarefree (g : ℕ) (hg : 1 ≤ g) (hsf : Squarefree g) :
    haveI : NeZero g := ⟨by omega⟩
    (Finset.univ.filter (fun a : ZMod g => a ^ g = a)).card =
    g.primeFactors.prod (fun p => 1 + Nat.gcd (g - 1) (p - 1)) := by
  haveI : NeZero g := ⟨by omega⟩
  --calls the generalized version with e := g
  exact card_pow_eq_self_zmod_squarefree_gen g g hg hg hsf

/-- Corollary: the cardinality of 𝒢(n,k) when the gap is square-free satisfies the
    product formula ∏_{p | g} (1 + gcd(g-1, p-1)).
    Link m3GoodCount → m3GoodFinset → ZMod-filter → formula. -/
theorem m3GoodCount_squarefree (n k : ℕ) (hn : n ≠ 0)
    (hg : 1 ≤ capGap n k)
    (hsf : Squarefree (capGap n k)) :
    m3GoodCount n k hn =
    (capGap n k).primeFactors.prod (fun p => 1 + Nat.gcd (capGap n k - 1) (p - 1)) := by
  -- We use the definitions directly without `set` to avoid rewriting issues.
  -- Step 1: m3GoodCount = (m3GoodFinset).card
  -- Strategy: we show that m3GoodSet n k hn is a duplicate-free list whose
  -- toFinset coincides with the image of m3GoodFinset, then we use the cardinalities.
  have hstep1 : m3GoodCount n k hn = (m3GoodFinset n k hn).card := by
    unfold m3GoodCount m3GoodSet m3GoodFinset
    -- LHS: List.filter length; RHS: Finset.filter card
    -- Strategy: convert LHS via toFinset (nodup list), then show it equals the image of RHS
    have hnodup : (List.filter (isM3GoodBool (capGap n k)) (List.range (capGap n k))).Nodup := by
      apply List.Nodup.filter
      exact List.nodup_range
    rw [← List.toFinset_card_of_nodup hnodup, ← Finset.card_image_of_injective _ Fin.val_injective]
    congr 1
    ext v
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range,
               Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hlt, hbool⟩; exact ⟨⟨v, hlt⟩, hbool, rfl⟩
    · rintro ⟨r, hbool, rfl⟩; exact ⟨r.isLt, hbool⟩
  -- Case g = 1: primeFactors = ∅, product = 1, m3GoodCount = 1
  by_cases hg1 : capGap n k = 1
  · have : m3GoodCount n k hn = 1 := by
      rw [hstep1]
      -- Fin 1 has a single element, isM3GoodBool 1 0 = true
      have hcard : (m3GoodFinset n k hn).card = 1 := by
        have heq : m3GoodFinset n k hn = Finset.univ := by
          ext r
          simp only [m3GoodFinset, Finset.mem_filter, Finset.mem_univ, true_and,
                     Finset.mem_univ]
          -- capGap n k = 1, so r : Fin 1, r.val = 0
          have hr0 : r.val = 0 := by
            have hlt := r.isLt; simp only [hg1] at hlt; omega
          simp [isM3GoodBool, hr0]
        rw [heq, Finset.card_univ, Fintype.card_fin, hg1]
      exact hcard
    rw [this, hg1, Nat.primeFactors_one, Finset.prod_empty]
  -- Case g ≥ 2
  have hg2 : 2 ≤ capGap n k := by omega
  haveI hgne : NeZero (capGap n k) := ⟨by omega⟩
  rw [hstep1]
  -- Step 2: (m3GoodFinset).card = (Finset.univ.filter (fun a : ZMod g => a^g = a)).card
  -- Key: isM3GoodBool g r.val = true ↔ (r.val : ZMod g)^g = r.val
  -- (this is the content of isM3GoodBool_iff_natCast_pow, which we prove inline)
  have hstep2 : (m3GoodFinset n k hn).card =
      (Finset.univ.filter (fun a : ZMod (capGap n k) => a ^ (capGap n k) = a)).card := by
    simp only [m3GoodFinset]
    -- Bijection: r : Fin g ↦ (r.val : ZMod g)
    apply Finset.card_bij (fun (r : Fin (capGap n k)) _ => (r.val : ZMod (capGap n k)))
    · -- membership: isM3GoodBool → a^g = a
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- Derive a^g = a from isM3GoodBool via ZMod cast
      have hlt : r.val < capGap n k := r.isLt
      have lhs_cast : ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
            * r.val % capGap n k : ℕ) : ZMod (capGap n k))
          = (r.val : ZMod (capGap n k)) * (r.val : ZMod (capGap n k)) ^ (capGap n k - 2)
            * (r.val : ZMod (capGap n k)) := by push_cast [ZMod.natCast_mod]; ring
      have expand : (r.val : ZMod (capGap n k)) ^ (capGap n k) =
          (r.val : ZMod (capGap n k)) * (r.val : ZMod (capGap n k)) ^ (capGap n k - 2)
          * (r.val : ZMod (capGap n k)) := by
        have heq : capGap n k = 1 + (capGap n k - 2) + 1 := by omega
        calc (r.val : ZMod (capGap n k)) ^ (capGap n k)
            = (r.val : ZMod (capGap n k)) ^ (1 + (capGap n k - 2) + 1) := by rw [← heq]
          _ = _ := by simp [pow_add, pow_one, mul_assoc]
      have lhs_lt : r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
          * r.val % capGap n k < capGap n k := Nat.mod_lt _ (by omega)
      simp only [isM3GoodBool, beq_iff_eq] at hr
      have hval_eq : ZMod.val ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
          * r.val % capGap n k : ℕ) : ZMod (capGap n k)) =
          ZMod.val ((r.val : ZMod (capGap n k))) := by
        rw [ZMod.val_natCast_of_lt lhs_lt, ZMod.val_natCast_of_lt hlt,
            hr, Nat.mod_eq_of_lt hlt]
      rw [expand, ← lhs_cast]
      exact ZMod.val_injective _ hval_eq
    · -- injectivity
      intro r₁ _ r₂ _ heq
      have hlt1 : r₁.val < capGap n k := r₁.isLt
      have hlt2 : r₂.val < capGap n k := r₂.isLt
      have : ZMod.val ((r₁.val : ZMod (capGap n k))) = ZMod.val ((r₂.val : ZMod (capGap n k))) :=
        congr_arg ZMod.val heq
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at this
      exact Fin.val_injective this
    · -- surjectivity
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      refine ⟨⟨ZMod.val a, ZMod.val_lt a⟩, ?_, ?_⟩
      · -- isM3GoodBool for ZMod.val a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hlt : ZMod.val a < capGap n k := ZMod.val_lt a
        have lhs_cast' : ((ZMod.val a * (ZMod.val a ^ (capGap n k - 2) % capGap n k) % capGap n k
              * ZMod.val a % capGap n k : ℕ) : ZMod (capGap n k))
            = (ZMod.val a : ZMod (capGap n k)) * (ZMod.val a : ZMod (capGap n k)) ^ (capGap n k - 2)
              * (ZMod.val a : ZMod (capGap n k)) := by push_cast [ZMod.natCast_mod]; ring
        have expand' : (ZMod.val a : ZMod (capGap n k)) ^ (capGap n k) =
            (ZMod.val a : ZMod (capGap n k)) * (ZMod.val a : ZMod (capGap n k)) ^ (capGap n k - 2)
            * (ZMod.val a : ZMod (capGap n k)) := by
          have heq : capGap n k = 1 + (capGap n k - 2) + 1 := by omega
          calc (ZMod.val a : ZMod (capGap n k)) ^ (capGap n k)
              = (ZMod.val a : ZMod (capGap n k)) ^ (1 + (capGap n k - 2) + 1) := by rw [← heq]
            _ = _ := by simp [pow_add, pow_one, mul_assoc]
        have lhs_lt' : ZMod.val a * (ZMod.val a ^ (capGap n k - 2) % capGap n k) % capGap n k
            * ZMod.val a % capGap n k < capGap n k := Nat.mod_lt _ (by omega)
        simp only [isM3GoodBool, beq_iff_eq]
        -- ha : a^g = a, natCast_val : (ZMod.val a : ZMod g) = a
        have hav : (ZMod.val a : ZMod (capGap n k)) = a := ZMod.natCast_zmod_val a
        -- ha : a^g = a; rewrite using hav : (ZMod.val a : ZMod g) = a
        rw [← hav] at ha
        -- now ha : (ZMod.val a : ZMod g)^g = (ZMod.val a : ZMod g)
        -- we use expand' and lhs_cast' (unchanged, they refer to ZMod.val a)
        rw [expand', ← lhs_cast'] at ha
        -- ha : (cast of the ℕ expression : ZMod g) = (ZMod.val a : ZMod g)
        have hval_eq : ZMod.val ((ZMod.val a * (ZMod.val a ^ (capGap n k - 2) % capGap n k) % capGap n k
            * ZMod.val a % capGap n k : ℕ) : ZMod (capGap n k)) =
            ZMod.val ((ZMod.val a : ZMod (capGap n k))) := congr_arg ZMod.val ha
        rw [ZMod.val_natCast_of_lt lhs_lt', ZMod.val_natCast_of_lt hlt] at hval_eq
        rw [Nat.mod_eq_of_lt hlt]
        exact hval_eq
      · -- (ZMod.val a : ZMod g) = a
        exact ZMod.natCast_zmod_val a
  rw [hstep2]
  -- Step 3: apply card_pow_eq_self_zmod_squarefree_gen with e := capGap n k
  exact card_pow_eq_self_zmod_squarefree_gen (capGap n k) (capGap n k) hg hg hsf

-- ================================================================
-- § 3. Local Meadow: Chapter Structure Theorem
-- ================================================================

/-!
### § 3. Local meadow on CapChap(n,k) with prime gap

The **local meadow** is the structure `(CapChap(n,k), ⊕ₙ, ⊗ₙ)` where:
- `CapChap(n,k) ≅ Fin(capGap n k)` via the offset `r ↦ k^n + r`
- `⊕ₙ = capAdd` (chapter addition)
- `⊗ₙ = capMul` (chapter multiplication)
- Fermat inversion `r⁻¹ = r^{g-2}` satisfies M3: `r ⊗ r^{g-2} ⊗ r = r`

When `capGap n k` is prime, `(CapChap(n,k), ⊕ₙ, ⊗ₙ)` is a **field** and
in particular a **total meadow** (M3 holds universally).

**Note:** This is a property of Aod_n (the structure on CapChap), not of Aod★.
-/

/-- Local meadow structure: M3 holds on all of CapChap(n,k) when the gap is prime.
    Main local structure theorem for Aod_n. -/
theorem local_meadow_of_prime_gap (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k))
    (r : Fin (capGap n k)) :
    capMul n k hn (capMul n k hn r (capMulPow n k hn (capGap n k - 2) r)) r = r :=
  m3_universal_of_prime n k hn hprime r

/-- When the gap is prime, chapter multiplication satisfies M3 for every element:
    `r ⊗ r^{g-2} ⊗ r = r` holds on all of `Fin (capGap n k)`. -/
theorem capMul_meadow_identity (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k))
    (r : Fin (capGap n k)) :
    let g := capGap n k
    let r_inv := capMulPow n k hn (g - 2) r
    capMul n k hn (capMul n k hn r r_inv) r = r :=
  local_meadow_of_prime_gap n k hn hprime r

-- ================================================================
-- § 4. Corollaries
-- ================================================================

/-- The M3-good set is always nonempty: 0 belongs to it. -/
theorem m3GoodCount_pos (n k : ℕ) (hn : n ≠ 0) : 1 ≤ m3GoodCount n k hn := by
  unfold m3GoodCount m3GoodSet
  have hmem : 0 ∈ (List.range (capGap n k)).filter (isM3GoodBool (capGap n k)) := by
    simp only [List.mem_filter, List.mem_range]
    exact ⟨capGap_pos n k hn, zero_isM3Good n k hn⟩
  exact Nat.one_le_iff_ne_zero.mpr (by simpa using List.length_pos_of_mem hmem)

/-- If g is prime, M3-good has exactly g elements (= the whole chapter). -/
theorem m3GoodCount_eq_capGap_iff_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodCount n k hn = capGap n k :=
  m3GoodCount_eq_capGap_of_prime n k hn hprime


/-- A prime gap implies that every element is M3-good.
    Formalizes the fact that CapChap(n,k) is a total meadow for prime gap. -/
theorem all_elements_m3good_of_prime (n k : ℕ) (_ : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    ∀ r : Fin (capGap n k), isM3GoodBool (capGap n k) r.val = true :=
  fun r => isM3GoodBool_of_prime hprime r.val r.isLt

/-- The local meadow is global: when the gap is prime, |𝒢(n,k)| = capGap n k. -/
theorem local_meadow_is_total (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodCount n k hn = capGap n k :=
  m3GoodCount_eq_capGap_of_prime n k hn hprime

-- ================================================================
-- § 4b. Additional Corollaries
-- ================================================================

/-- Membership in m3GoodSet: r is M3-good ↔ r < g and satisfies the boolean predicate.
    Useful as a rewrite for cascading lemmas. -/
theorem m3GoodSet_mem_iff (n k : ℕ) (hn : n ≠ 0) (r : ℕ) :
    r ∈ m3GoodSet n k hn ↔ r < capGap n k ∧ isM3GoodBool (capGap n k) r = true := by
  simp [m3GoodSet, List.mem_filter, List.mem_range]

/-- The element 0 always belongs to the M3-good set. -/
theorem zero_mem_m3GoodSet (n k : ℕ) (hn : n ≠ 0) :
    0 ∈ m3GoodSet n k hn := by
  rw [m3GoodSet_mem_iff]
  exact ⟨capGap_pos n k hn, by simp [isM3GoodBool]⟩

/-- m3GoodSet is always nonempty (contains at least 0). -/
theorem m3GoodSet_nonempty (n k : ℕ) (hn : n ≠ 0) :
    m3GoodSet n k hn ≠ [] :=
  List.ne_nil_iff_length_pos.mpr (List.length_pos_of_mem (zero_mem_m3GoodSet n k hn))

/-- The predicate `isM3GoodBool g 0` is true for any g, without hypotheses.
    Generalizes `zero_isM3Good` outside the chapter context. -/
theorem isM3GoodBool_zero_of_pos (g : ℕ) : isM3GoodBool g 0 = true := by
  simp [isM3GoodBool]

/-- When the gap is prime, m3GoodSet coincides with the entire `List.range (capGap n k)`.
    Formalizes the fact that M3 holds universally (total meadow) when g is prime. -/
theorem m3GoodSet_eq_range_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodSet n k hn = List.range (capGap n k) := by
  unfold m3GoodSet
  rw [List.filter_eq_self]
  intro r hr
  rw [List.mem_range] at hr
  exact isM3GoodBool_of_prime hprime r hr

/-- Corollary: the length of m3GoodSet equals that of `List.range g` for prime gap.
    Strengthens `m3GoodCount_eq_capGap_of_prime` by showing equality as lists. -/
theorem m3GoodCount_eq_length_range_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodCount n k hn = (List.range (capGap n k)).length := by
  unfold m3GoodCount
  rw [m3GoodSet_eq_range_of_prime n k hn hprime]

-- ================================================================
-- § 5. m3GoodFinset: consistency and cardinality
-- ================================================================

/-!
### § 5. Finset ↔ List consistency and cardinality

`m3GoodFinset` works on `Fin (capGap n k)` — the correct type for the chapter
operations — whereas `m3GoodSet` works on `List ℕ`. This section establishes
the consistency between the two representations and the cardinality theorems.

Architectural note: the bridge capMul-M3 ↔ isM3GoodBool does not exist as a
direct equivalence (toZMod r ≠ r.val in general). The correct link is:
  capMul-M3 ↔ toZMod^g = toZMod  (isM3Good_iff_pow_capGap)
  isM3GoodBool ↔ r.val^g = r.val  (isM3GoodBool_iff_natCast_pow)
The two ZMod predicates are distinct because toZMod n k r = r.val + k^n mod g.
-/

/-- Consistency between m3GoodFinset (on Fin g) and m3GoodSet (on ℕ):
    r ∈ m3GoodFinset ↔ r.val ∈ m3GoodSet. -/
theorem m3GoodFinset_mem_iff (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    r ∈ m3GoodFinset n k hn ↔ r.val ∈ m3GoodSet n k hn := by
  simp [m3GoodFinset, m3GoodSet, Finset.mem_filter, List.mem_filter,
        List.mem_range, r.isLt]

/-!
### 1.2 Boolean ↔ ZMod bridge (without primality, without toZMod)

`isM3GoodBool g r` computes in ℕ the identity `r · r^{g-2} · r ≡ r mod g`.
The following lemma shows that this computation coincides exactly with
`(r : ZMod g)^g = r` — a full equivalence, without hypotheses on k or toZMod.

Note: `toZMod n k r = r.val + k^n mod g ≠ r.val` in general, so
this bridge does **not** directly connect isM3GoodBool to capMul-M3.
The link capMul-M3 ↔ toZMod^g=toZMod is captured by `isM3Good_iff_pow_capGap`.
-/

/-- Full equivalence: `isM3GoodBool g r = true` ↔ `(r : ZMod g)^g = r`.
    Holds without primality hypotheses and without hypotheses on k or toZMod.
    Verified computationally on all capGap with n ≤ 5, k ≤ 6. -/
lemma isM3GoodBool_iff_natCast_pow (n k : ℕ) (_hn : n ≠ 0)
    (hg : 2 ≤ capGap n k) (r : Fin (capGap n k)) :
    isM3GoodBool (capGap n k) r.val = true ↔
    (r.val : ZMod (capGap n k)) ^ (capGap n k) = (r.val : ZMod (capGap n k)) := by
  haveI : NeZero (capGap n k) := ⟨by omega⟩
  have hr : r.val < capGap n k := r.isLt
  -- Expand: a^g = a * a^(g-2) * a in ZMod g
  have expand : (r.val : ZMod (capGap n k)) ^ (capGap n k) =
      (r.val : ZMod (capGap n k)) * (r.val : ZMod (capGap n k)) ^ (capGap n k - 2)
      * (r.val : ZMod (capGap n k)) := by
    have heq : capGap n k = 1 + (capGap n k - 2) + 1 := by omega
    calc (r.val : ZMod (capGap n k)) ^ (capGap n k)
        = (r.val : ZMod (capGap n k)) ^ (1 + (capGap n k - 2) + 1) := by rw [← heq]
      _ = _ := by simp [pow_add, pow_one, mul_assoc]
  -- Cast: the ℕ expression of isM3GoodBool corresponds to a * a^(g-2) * a in ZMod g
  have lhs_cast : ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
        * r.val % capGap n k : ℕ) : ZMod (capGap n k))
      = (r.val : ZMod (capGap n k)) * (r.val : ZMod (capGap n k)) ^ (capGap n k - 2)
        * (r.val : ZMod (capGap n k)) := by push_cast [ZMod.natCast_mod]; ring
  have lhs_lt : r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
      * r.val % capGap n k < capGap n k := Nat.mod_lt _ (by omega)
  simp only [isM3GoodBool, beq_iff_eq]
  constructor
  · intro h
    have hval_eq : ZMod.val ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
        * r.val % capGap n k : ℕ) : ZMod (capGap n k)) =
        ZMod.val ((r.val : ZMod (capGap n k))) := by
      rw [ZMod.val_natCast_of_lt lhs_lt, ZMod.val_natCast_of_lt hr,
          h, Nat.mod_eq_of_lt hr]
    have hzmod := ZMod.val_injective _ hval_eq
    rw [expand, ← lhs_cast, hzmod]
  · intro h
    have hzmod : ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
        * r.val % capGap n k : ℕ) : ZMod (capGap n k)) = (r.val : ZMod (capGap n k)) := by
      rw [lhs_cast, ← expand, h]
    have hval_eq : ZMod.val ((r.val * (r.val ^ (capGap n k - 2) % capGap n k) % capGap n k
        * r.val % capGap n k : ℕ) : ZMod (capGap n k)) =
        ZMod.val ((r.val : ZMod (capGap n k))) :=
      congr_arg ZMod.val hzmod
    rw [ZMod.val_natCast_of_lt lhs_lt, ZMod.val_natCast_of_lt hr] at hval_eq
    rw [Nat.mod_eq_of_lt hr]
    exact hval_eq

/-- Corollary: for prime gap, m3GoodFinset = Finset.univ. -/
theorem m3GoodFinset_eq_univ_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    m3GoodFinset n k hn = Finset.univ := by
  ext r
  simp [m3GoodFinset, Finset.mem_filter, isM3GoodBool_of_prime hprime r.val r.isLt]

/-- Cardinality of m3GoodFinset for prime gap: equal to g. -/
theorem m3GoodFinset_card_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k)) :
    (m3GoodFinset n k hn).card = capGap n k := by
  rw [m3GoodFinset_eq_univ_of_prime n k hn hprime]
  simp

-- ================================================================
-- § 6. Multiplicative Closure of 𝒢(n,k)
-- ================================================================
/-!
### §6. 𝒢(n,k) is a sub-monoid of CapChap(n,k)

The M3-good set is closed under the chapter product ⊗_k:
- The multiplicative neutral 1_k ∈ 𝒢(n,k) (without hypotheses on g)
- If r, s ∈ 𝒢(n,k) then r ⊗_k s ∈ 𝒢(n,k)

Hence (𝒢(n,k), ⊗_k) is a finite commutative sub-monoid of (CapChap(n,k), ⊗_k).

Proof of closure (in ZMod g):
  (a · b)^g = a^g · b^g = a · b.

The neutral 1_k ∈ 𝒢 follows directly from the multiplicative law:
  1 ⊗ 1^{g-2} ⊗ 1 = 1 (without going through ZMod).
-/

/-- Auxiliary lemma: capMulPow m (capMulNeutral) = capMulNeutral for every m.
    Direct proof by induction, without going through toZMod. -/
private lemma capMulPow_neutral (n k : ℕ) (hn : n ≠ 0) (m : ℕ) :
    capMulPow n k hn m (capMulNeutral n k hn) = capMulNeutral n k hn := by
  induction m with
  | zero      => rfl
  | succ m ih => rw [capMulPow, ih, capMul_neutral_left]

/-- The multiplicative neutral 1_k satisfies M3: 1 ⊗ 1^{g-2} ⊗ 1 = 1.
    Does not require g ≥ 2: the proof is purely algebraic via the neutral law. -/
theorem capMulNeutral_isM3Good (n k : ℕ) (hn : n ≠ 0) :
    capMul n k hn
      (capMul n k hn (capMulNeutral n k hn)
        (capMulPow n k hn (capGap n k - 2) (capMulNeutral n k hn)))
      (capMulNeutral n k hn) = capMulNeutral n k hn := by
  rw [capMulPow_neutral, capMul_neutral_left, capMul_neutral_left]

/-- 𝒢(n,k) is closed under ⊗_k: if r and s satisfy M3 then r ⊗_k s satisfies M3.
    Proof: in ZMod g, (a·b)^g = a^g · b^g = a · b. -/
theorem m3Good_mul_closed (n k : ℕ) (hn : n ≠ 0) (hg : 2 ≤ capGap n k)
    (r s : Fin (capGap n k))
    (hr : capMul n k hn (capMul n k hn r
            (capMulPow n k hn (capGap n k - 2) r)) r = r)
    (hs : capMul n k hn (capMul n k hn s
            (capMulPow n k hn (capGap n k - 2) s)) s = s) :
    capMul n k hn
      (capMul n k hn (capMul n k hn r s)
        (capMulPow n k hn (capGap n k - 2) (capMul n k hn r s)))
      (capMul n k hn r s) = capMul n k hn r s := by
  apply (isM3Good_iff_pow_capGap n k hn hg _).mpr
  have hr' := (isM3Good_iff_pow_capGap n k hn hg r).mp hr
  have hs' := (isM3Good_iff_pow_capGap n k hn hg s).mp hs
  simp only [toZMod_mul, mul_pow, hr', hs']

-- ================================================================
-- § 7. Frobenius Endomorphism on CapChap(n,k)
-- ================================================================
/-!
### §7. The Frobenius endomorphism F_g

The Frobenius endomorphism is the map
  F_g : CapChap(n,k) → CapChap(n,k),   F_g(r) = r^{⊗g}

where g = capGap(n,k) and r^{⊗g} = capMulPow(n,k,g,r).

In ZMod g, F_g corresponds to the endomorphism a ↦ a^g (the abstract Frobenius
on ℤ/gℤ). For g prime, Fermat's Little Theorem guarantees F_g = id,
which explains why 𝒢(n,k) = CapChap(n,k) in that case.

**Proved properties:**
- F_g is a multiplicative monoid endomorphism: F_g(r ⊗ s) = F_g(r) ⊗ F_g(s)
- 𝒢(n,k) = Fix(F_g): the M3-good elements are exactly the fixed points of F_g
- F_g fixes the multiplicative neutral 1_k

**Structural consequence:**
Fix(F_g) is a sub-monoid of CapChap(n,k): if r,s ∈ Fix(F_g) then
  F_g(r⊗s) = F_g(r)⊗F_g(s) = r⊗s,
i.e. r⊗s ∈ Fix(F_g). This recovers the multiplicative closure of §6.
-/

/-- The Frobenius endomorphism on CapChap(n,k): r ↦ r^{⊗g}. -/
def meadowFrobenius (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) : Fin (capGap n k) :=
  capMulPow n k hn (capGap n k) r

/-- F_g is a multiplicative monoid endomorphism:
    F_g(r ⊗_k s) = F_g(r) ⊗_k F_g(s).
    Proof: in ZMod g, (a·b)^g = a^g · b^g. -/
theorem meadowFrobenius_mul (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    meadowFrobenius n k hn (capMul n k hn r s) =
    capMul n k hn (meadowFrobenius n k hn r) (meadowFrobenius n k hn s) := by
  apply toZMod_injective n k hn
  simp only [meadowFrobenius, toZMod_capMulPow, toZMod_mul, mul_pow]

/-- r ∈ 𝒢(n,k) if and only if r is a fixed point of F_g:
    r ⊗ r^{g-2} ⊗ r = r  ↔  F_g(r) = r.
    Characterization: 𝒢(n,k) = Fix(F_g). -/
theorem m3Good_iff_frobenius_fixed (n k : ℕ) (hn : n ≠ 0) (hg : 2 ≤ capGap n k)
    (r : Fin (capGap n k)) :
    capMul n k hn (capMul n k hn r (capMulPow n k hn (capGap n k - 2) r)) r = r ↔
    meadowFrobenius n k hn r = r := by
  unfold meadowFrobenius
  constructor
  · intro hm3
    apply toZMod_injective n k hn
    rw [toZMod_capMulPow]
    exact (isM3Good_iff_pow_capGap n k hn hg r).mp hm3
  · intro hf
    apply (isM3Good_iff_pow_capGap n k hn hg r).mpr
    have := congr_arg (toZMod n k) hf
    rwa [toZMod_capMulPow] at this

/-- F_g fixes the multiplicative neutral 1_k. -/
theorem meadowFrobenius_neutral (n k : ℕ) (hn : n ≠ 0) :
    meadowFrobenius n k hn (capMulNeutral n k hn) = capMulNeutral n k hn := by
  unfold meadowFrobenius
  exact capMulPow_neutral n k hn (capGap n k)

-- ================================================================
-- § 8. Corollaries of the Frobenius and of multiplicative closure
-- ================================================================

/-!
### §8. Five structural corollaries

These corollaries follow directly from §6 and §7 and complete the algebraic
picture of 𝒢(n,k) as a sub-monoid and as the fixed-point set of the Frobenius.
-/

/-- The set of fixed points of F_g as a Finset over Fin(g).
    This is the "true" 𝒢(n,k) set in the chapter algebra:
    the elements r for which capMul-M3 holds, i.e. r ⊗ r^{g-2} ⊗ r = r. -/
def frobeniusFixedFinset (n k : ℕ) (hn : n ≠ 0) : Finset (Fin (capGap n k)) :=
  Finset.univ.filter (fun r => meadowFrobenius n k hn r = r)

-- ---------------------------------------------------------------
-- Corollary 1: closure of Fix(F_g) under ⊗ as a Finset
-- ---------------------------------------------------------------

/-- Fix(F_g) is closed under the chapter product ⊗_k.
    Meaning: the set of fixed points of the Frobenius is a sub-monoid
    in the Finset sense — it is the Finset version of §6 which worked
    directly with the capMul-M3 hypotheses. The proof uses meadowFrobenius_mul:
    if F_g(r)=r and F_g(s)=s then F_g(r⊗s)=F_g(r)⊗F_g(s)=r⊗s. -/
theorem frobeniusFixed_mul_closed (n k : ℕ) (hn : n ≠ 0)
    (r s : Fin (capGap n k))
    (hr : r ∈ frobeniusFixedFinset n k hn)
    (hs : s ∈ frobeniusFixedFinset n k hn) :
    capMul n k hn r s ∈ frobeniusFixedFinset n k hn := by
  simp only [frobeniusFixedFinset, Finset.mem_filter, Finset.mem_univ, true_and] at *
  rw [meadowFrobenius_mul, hr, hs]

-- ---------------------------------------------------------------
-- Corollary 2: idempotence of F_g (F_g ∘ F_g = capMulPow g²)
-- ---------------------------------------------------------------

/-- F_g applied twice is equivalent to raising to the g²-th chapter power.
    Meaning: the iteration of the Frobenius captures the orbit structure
    of the action of ℕ on ZMod g via the map n ↦ a^n. For g prime one has
    F_g = id, hence F_g ∘ F_g = id = capMulPow 1 ≠ capMulPow g², unless
    g² ≡ 1 mod (ord a) — the non-triviality lives in the composite case. -/
theorem meadowFrobenius_comp (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    meadowFrobenius n k hn (meadowFrobenius n k hn r) =
    capMulPow n k hn (capGap n k ^ 2) r := by
  apply toZMod_injective n k hn
  simp only [meadowFrobenius, toZMod_capMulPow]
  rw [← pow_mul, sq]

-- ---------------------------------------------------------------
-- Corollary 3: sub-monoid structure of Fix(F_g)
-- ---------------------------------------------------------------

/-- Fix(F_g) contains the neutral and is closed under ⊗: sub-monoid structure.
    Meaning: this is the precise algebraic statement that justifies the
    designation "finite commutative sub-monoid of (CapChap(n,k), ⊗_k)"
    used in §6 and in the LaTeX paper. The two components are:
    (i)  1_k ∈ Fix(F_g)  — the neutral is a fixed point
    (ii) r,s ∈ Fix(F_g) → r⊗s ∈ Fix(F_g)  — closure under product. -/
theorem frobeniusFixed_submonoid_structure (n k : ℕ) (hn : n ≠ 0) :
    capMulNeutral n k hn ∈ frobeniusFixedFinset n k hn ∧
    ∀ r s : Fin (capGap n k),
      r ∈ frobeniusFixedFinset n k hn →
      s ∈ frobeniusFixedFinset n k hn →
      capMul n k hn r s ∈ frobeniusFixedFinset n k hn :=
  ⟨by simp [frobeniusFixedFinset, meadowFrobenius_neutral],
   fun r s hr hs => frobeniusFixed_mul_closed n k hn r s hr hs⟩

-- ---------------------------------------------------------------
-- Corollary 4: frobeniusFixedFinset = capMul-M3 Finset
-- ---------------------------------------------------------------

/-- The Finset of fixed points of F_g coincides with that of the elements that
    satisfy the capMul-M3 identity: r ⊗ r^{g-2} ⊗ r = r.
    Meaning: this theorem closes the circle between the algebraic definition
    (M3 identity in the chapter monoid) and the geometric characterization
    (fixed points of the Frobenius endomorphism), unifying §6 and §7 into a
    single well-defined Finset object. Requires g ≥ 2. -/
theorem frobeniusFixed_eq_capM3Finset (n k : ℕ) (hn : n ≠ 0) (hg : 2 ≤ capGap n k) :
    frobeniusFixedFinset n k hn =
    Finset.univ.filter (fun r =>
      capMul n k hn (capMul n k hn r (capMulPow n k hn (capGap n k - 2) r)) r = r) := by
  ext r
  simp only [frobeniusFixedFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (m3Good_iff_frobenius_fixed n k hn hg r).symm

-- ---------------------------------------------------------------
-- Corollary 5: for prime gap F_g = id (geometric Fermat's Little Theorem)
-- ---------------------------------------------------------------

/-- For prime gap, the chapter Frobenius is the identity: F_g(r) = r for every r.
    Meaning: this is the "geometric" Fermat's Little Theorem for the
    chapter structure — in a chapter with prime gap, raising to the g-th
    chapter power does nothing. It is the structural explanation of why
    𝒢(n,k) = CapChap(n,k) when g is prime: all elements are
    fixed points of the Frobenius. -/
theorem meadowFrobenius_eq_id_of_prime (n k : ℕ) (hn : n ≠ 0)
    (hprime : Nat.Prime (capGap n k))
    (r : Fin (capGap n k)) :
    meadowFrobenius n k hn r = r :=
  (m3Good_iff_frobenius_fixed n k hn hprime.two_le r).mp
    (local_meadow_of_prime_gap n k hn hprime r)

end MeadowLocal
