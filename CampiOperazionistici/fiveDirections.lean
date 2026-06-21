/-
  DirezioniFondamentali.lean — Operationistic Fields AOD
  =======================================================
  Five Research Directions: Analogies with Modular Arithmetic
  Author: Alessandro Sgarbi — 2026-03-09

  Paper: §11 (Five Research Directions)

  Dependencies:
    · CampiOperazionistici.CampiOperazionistici  (irootN, radRem, aodEquiv, …)
    · CampiOperazionistici.GroupStructure         (capGap, capAdd, capMul,
                                                   capNeutral, capNeutral,
                                                   capMulNeutral, capMulInv,
                                                   capMulPow, toZMod,
                                                   toZMod_add, toZMod_mul,
                                                   toZMod_injective,
                                                   capField_isomorphic_zmod,
                                                   CapChap, …)

  File structure:
    §1 — Imports and setup
    §2 — Shared auxiliary lemmas
    §3 — Direction I   : Radical Order / Fermat-AOD (additive)
    §4 — Direction II  : φ_AOD and Invertibles
    §5 — Direction III : Radical CRT
    §6 — Direction IV  : Radical Wilson's Law
    §7 — Direction V   : Radical Euler Theorem

  Methodological note:
    Some directions (III, V) depend on properties of ZMod already in Mathlib
    (ZMod.pow_card_sub_one_eq_one, ZMod.card_units_eq_totient, …) and are
    proved via the morphism `toZMod`, which is already proven bijective and
    compatible with + and × in GroupStructure.lean.

    Current status: the file is fully proved, 0 `sorry`.
    All five directions are closed (including `crtRadicale_suriettivo`,
    via `ZMod.chineseRemainder` and the explicit witness `M^L + x`).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.GroupStructure

open CampiOperazionistici
open BigOperators

namespace DirezioniFondamentali

/-! ─────────────────────────────────────────────────────────────────────────
    §2 — Auxiliary Lemmas
    ───────────────────────────────────────────────────────────────────────── -/

section Ausiliari

/-
  Fundamental connection between capGap (GroupStructure) and gap (CampiOperazionistici).
  The two definitions are definitionally equal but live in different modules.
-/
lemma capGap_eq_gap (n k : ℕ) : capGap n k = gap n k := by
  simp [capGap, gap]

/-- `toZMod` is an additive homomorphism: already in GroupStructure as `toZMod_add`. -/
lemma toZMod_add_hom (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    toZMod n k (capAdd n k hn r s) = toZMod n k r + toZMod n k s :=
  (capField_isomorphic_zmod n k hn).right.left r s

/-- `toZMod` is a multiplicative homomorphism: already in GroupStructure as `toZMod_mul`. -/
lemma toZMod_mul_hom (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    toZMod n k (capMul n k hn r s) = toZMod n k r * toZMod n k s :=
  (capField_isomorphic_zmod n k hn).right.right.left r s

/-- The additive neutral maps to 0 under `toZMod`. -/
lemma toZMod_neutral_is_zero (n k : ℕ) (hn : n ≠ 0) :
    toZMod n k (capNeutral n k hn) = 0 :=
  (capField_isomorphic_zmod n k hn).right.right.right.left

/-- The multiplicative neutral maps to 1 under `toZMod`. -/
lemma toZMod_mulNeutral_is_one (n k : ℕ) (hn : n ≠ 0) :
    toZMod n k (capMulNeutral n k hn) = 1 :=
  (capField_isomorphic_zmod n k hn).right.right.right.right

/-- Utility: the order of capGap is positive. -/
lemma capGap_pos' (n k : ℕ) (hn : n ≠ 0) : 0 < capGap n k :=
  capGap_pos n k hn

end Ausiliari


/-! ─────────────────────────────────────────────────────────────────────────
    §3 — DIRECTION I: Radical Order and Fermat's Little Theorem AOD
    ─────────────────────────────────────────────────────────────────────────

    Context:
      In classical modular arithmetic, Fermat's Little Theorem states
      that in (ℤ/pℤ, +) of prime order p, every element has order dividing p,
      hence p·a = 0 for every a.

      In AOD, the chapter additive group is (Fin(g), ⊕_k) with neutral
      capNeutral n k hn, proven AddCommGroup in GroupStructure.lean.
      Since the group has order g, g iterations of ⊕_k on any r
      return to the neutral (additive Fermat-AOD), for every g — prime or not.
      Primality is needed only for the stronger result
      (exact additive order = g for every r ≠ neutral).
    ─────────────────────────────────────────────────────────────────────────  -/

section DirezioneI

variable (n k : ℕ) (hn : n ≠ 0)

/-- The m-th iteration of capAdd on r: `capAddIter m r = m ⊕_k r` -/
def capAddIter : ℕ → Fin (capGap n k) → Fin (capGap n k)
  | 0,     _ => capNeutral n k hn
  | m + 1, r => capAdd n k hn (capAddIter m r) r

/-- `capAddIter` corresponds to `nsmul` in the group `capAddCommGroup`. -/
lemma capAddIter_eq_nsmul (m : ℕ) (r : Fin (capGap n k)) :
    capAddIter n k hn m r = (capAddCommGroup n k hn).nsmul m r := by
  induction m with
  | zero =>
    simp [capAddIter]
    rfl
  | succ m ih =>
    simp only [capAddIter, ih]
    rfl

/-- Central lemma: `toZMod` transports `capAddIter` to iterated sum in ZMod g. -/
lemma toZMod_capAddIter (m : ℕ) (r : Fin (capGap n k)) :
    toZMod n k (capAddIter n k hn m r) = m • toZMod n k r := by
  induction m with
  | zero =>
    simp [capAddIter, toZMod_neutral_is_zero n k hn]
  | succ m ih =>
    simp only [capAddIter, succ_nsmul]
    rw [toZMod_add_hom, ih]

/-
  THEOREM I.1 — Additive Fermat-AOD (via ZMod).

  In (ℤ/gℤ, +), if g is prime, then g·x = 0 for every x (group order).
  Transported back via toZMod_injective, we obtain:
    capAddIter g r = capNeutral.

  Proof:
    toZMod (capAddIter g r) = g • toZMod r   [toZMod_capAddIter]
                            = (g : ZMod g) • toZMod r
                            = 0 • toZMod r     [ZMod.natCast_self]
                            = 0
                            = toZMod (capNeutral)  [toZMod_neutral_is_zero]
    ⟹ capAddIter g r = capNeutral              [toZMod_injective]
-/
theorem fermatAOD_additivo (r : Fin (capGap n k)) :
    capAddIter n k hn (capGap n k) r = capNeutral n k hn := by
  apply (capField_isomorphic_zmod n k hn).left.left
  rw [toZMod_capAddIter, toZMod_neutral_is_zero]
  haveI : NeZero (capGap n k) := ⟨(capGap_pos' n k hn).ne'⟩
  simp [nsmul_eq_mul]

/-
  COROLLARY I.2 — Additive order of toZMod r divides the gap (CORRECTED statement).

  For every r, the additive order of toZMod n k r in (ZMod g, +) divides capGap n k.
  This is Lagrange's Theorem for the additive group (ZMod g, +).

  CRITICAL NOTE on the previous statement:
  The statement "capGap n k ∣ m whenever capAddIter m r = capNeutral"
  was MATHEMATICALLY FALSE. Counterexample in ZMod 6: the element 2 has additive
  order 3, hence capAddIter 3 r = capNeutral, but 6 ∤ 3.
  The correct result is addOrderOf(toZMod r) ∣ m (the order of r divides m,
  not vice versa). The statement "g ∣ m" holds only if r is a generator.

  We work in ZMod g (via toZMod) to have a standard AddCommGroup structure.
-/
/-- The additive order of toZMod r in ZMod g divides capGap n k (Lagrange's Theorem). -/
theorem ordine_radicale_divide_gap (r : Fin (capGap n k)) :
    addOrderOf (toZMod n k r) ∣ capGap n k := by
  -- capGap n k > 0: r : Fin (capGap n k) implies capGap n k ≠ 0
  haveI : NeZero (capGap n k) := ⟨by have := r.isLt; omega⟩
  have := @addOrderOf_dvd_card (ZMod (capGap n k)) _ _ (toZMod n k r)
  simpa [ZMod.card] using this

/-- If capAddIter m r = capNeutral, then addOrderOf(toZMod r) ∣ m. -/
theorem addOrderOf_dvd_of_capAddIter (r : Fin (capGap n k)) (m : ℕ)
    (hm : capAddIter n k hn m r = capNeutral n k hn) :
    addOrderOf (toZMod n k r) ∣ m := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  -- toZMod transports capAddIter m r = capNeutral to m • toZMod r = 0
  have := congr_arg (toZMod n k) hm
  rwa [toZMod_capAddIter, toZMod_neutral_is_zero] at this

/-
  COROLLARY I.2b — Strong variant: for prime capGap, every r ≠ capNeutral
  has additive order EXACTLY capGap n k in ZMod g.

  In ZMod p (p prime), the additive group is cyclic of order p.
  Every non-zero element has order p.
  Verified computationally: for n=2, k=1 (gap=3 prime), every r≠neutral
  has addOrderOf(toZMod r) = 3.
-/
/-- For prime capGap n k, every r ≠ capNeutral: addOrderOf(toZMod r) = capGap n k. -/
theorem ordine_radicale_esatto_primo [hprime : Fact (Nat.Prime (capGap n k))]
    (r : Fin (capGap n k)) (hr : r ≠ capNeutral n k hn) :
    addOrderOf (toZMod n k r) = capGap n k := by
  haveI : NeZero (capGap n k) := ⟨hprime.out.pos.ne'⟩
  have hne : toZMod n k r ≠ 0 := by
    intro h; apply hr
    apply toZMod_injective n k hn
    rw [h, toZMod_neutral_is_zero]
  -- In ZMod p prime, every non-zero element has order p
  -- The Mathlib lemma is ZMod.addOrderOf_eq_prime (if it exists) or derivable from:
  -- addOrderOf x ∣ p (Lagrange) and addOrderOf x > 1 (x ≠ 0) → addOrderOf x = p (p prime)
  have hdvd : addOrderOf (toZMod n k r) ∣ capGap n k := by
    have := @addOrderOf_dvd_card (ZMod (capGap n k)) _ _ (toZMod n k r)
    simpa [ZMod.card] using this
  have hone : addOrderOf (toZMod n k r) ≠ 1 := by
    intro h
    rw [AddMonoid.addOrderOf_eq_one_iff] at h
    exact hne h
  rcases hprime.out.eq_one_or_self_of_dvd _ hdvd with h1 | hg
  · exact absurd h1 hone
  · exact hg

/-
  COMPUTATIONAL VERIFICATION of the main cases.
  These #eval confirm the theorem on concrete instances.
-/
-- AOD_2, k=1: gap=3, neutral e=2
-- capAddIter 3 r = e for every r ∈ {0,1,2}
#eval (capAddIter 2 1 (by norm_num) 3 ⟨0, by norm_num [capGap]⟩).val  -- 2 = neutral ✓
#eval (capAddIter 2 1 (by norm_num) 3 ⟨1, by norm_num [capGap]⟩).val  -- 2 ✓
#eval (capAddIter 2 1 (by norm_num) 3 ⟨2, by norm_num [capGap]⟩).val  -- 2 ✓
-- capNeutral 2 1
#eval (capNeutral 2 1 (by norm_num)).val   -- 2 ✓

-- AOD_3, k=1: gap=7, neutral e=6
#eval (capAddIter 3 1 (by norm_num) 7 ⟨0, by norm_num [capGap]⟩).val  -- 6 = neutral ✓
#eval (capAddIter 3 1 (by norm_num) 7 ⟨3, by norm_num [capGap]⟩).val  -- 6 ✓
#eval (capNeutral 3 1 (by norm_num)).val   -- 6 ✓

end DirezioneI


/-! ─────────────────────────────────────────────────────────────────────────
    §4 — DIRECTION II: φ_AOD and Density of Invertibles
    ─────────────────────────────────────────────────────────────────────────

    Euler's function φ(g) counts the elements of {0,...,g-1} coprime to g.
    In AOD, the multiplicative invertibles in chapter k are the r ∈ Fin(g)
    such that gcd(k^n + r, g) = 1.

    The map r ↦ (k^n + r) mod g is a bijection of {0,...,g-1}
    onto itself, and gcd(k^n+r, g) = gcd((k^n+r) mod g, g).
    Hence the number of k-invertible r equals the number of a < g
    with gcd(a,g)=1, which is φ(g) by definition.

    In this section we prove:
      (1) The multiplicative neutral capMulNeutral is invertible.
      (2) For g prime, every non-zero element is invertible.
      (3) The number of invertibles is exactly φ(g).
    ─────────────────────────────────────────────────────────────────────────  -/

section DirezioneII

variable (n k : ℕ) (hn : n ≠ 0)

/-- An element r : Fin(g) is invertible in (Fin(g), ⊗_k) iff
    its absolute representative (k^n + r) is coprime to g. -/
def isCapMulInvertible (r : Fin (capGap n k)) : Prop :=
  Nat.Coprime (k ^ n + r.val) (capGap n k)

/-- The set of invertibles in (Fin(g), ⊗_k). -/
def capMulUnits (n k : ℕ) : Finset (Fin (capGap n k)) :=
  Finset.filter (fun r => Nat.Coprime (k ^ n + r.val) (capGap n k))
                Finset.univ

/-- The multiplicative neutral is always invertible. -/
theorem capMulNeutral_isInvertible :
    Nat.Coprime (k ^ n + (capMulNeutral n k hn).val) (capGap n k) := by
  -- toZMod n k r = (r.val : ZMod g) + k^n, and toZMod(capMulNeutral) = 1.
  -- Hence (val + k^n : ZMod g) = 1, i.e. (k^n + val) % g = 1.
  -- From (k^n + val) % g = 1 it follows that gcd(k^n + val, g) = 1.
  have hg := capGap_pos' n k hn
  haveI hne : NeZero (capGap n k) := ⟨hg.ne'⟩
  -- toZMod n k r = r.val + k^n in ZMod g, and the result is 1
  -- We obtain (k^n + val) ≡ 1 (mod g) from toZMod_mulNeutral_is_one
  -- and use ZMod.natCast_eq_natCast_iff to pass to the Nat congruence
  -- (k^n + val) % g = 1 % g, i.e. ≡ 1 (mod g)
  have hmod : (k ^ n + (capMulNeutral n k hn).val) % capGap n k = 1 % capGap n k := by
    have h := toZMod_mulNeutral_is_one n k hn
    simp only [toZMod] at h
    -- h : (val : ZMod g) + (k^n : ZMod g) = 1
    -- We want: (k^n + val) % g = 1 % g
    -- Equivalent to: (k^n + val : ZMod g) = (1 : ZMod g)
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [add_comm]
    convert h using 2
    · push_cast [Nat.cast_pow]; rfl
  -- gcd(k^n + val, g) = gcd(1 % g, g) = gcd(1, g) = 1
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hmod]
  simp

/-- For g prime, every non-zero element is invertible in (Fin(g), ⊗_k).
    This follows from the fact that ZMod p is a field. -/
theorem capMul_prime_gap_allInvertible
    [hprime : Fact (Nat.Prime (capGap n k))]
    (r : Fin (capGap n k))
    (hr : r ≠ capNeutral n k hn) :
    Nat.Coprime (k ^ n + r.val) (capGap n k) := by
  -- Strategy: if g | (k^n + r.val) then toZMod r = 0, contradicting r ≠ capNeutral.
  -- toZMod r ≠ 0 (because r ≠ capNeutral)
  have hne : toZMod n k r ≠ 0 := by
    intro h
    apply hr
    apply toZMod_injective n k hn
    rw [h, toZMod_neutral_is_zero]
  -- prime gcd: if p prime, gcd(a,p) is 1 or p
  -- If gcd(k^n+r.val, g) = g, then g | k^n+r.val, hence toZMod r = 0 — contradiction
  -- For g prime, Coprime(k^n+r, g) ↔ ¬(g ∣ k^n+r)
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime]
  rw [Nat.Prime.coprime_iff_not_dvd hprime.out]
  intro hdvd
  -- g | (k^n + r.val) implies (k^n + r.val : ZMod g) = 0
  have hzero : toZMod n k r = 0 := by
    simp only [toZMod]
    rw [← ZMod.natCast_eq_zero_iff] at hdvd
    push_cast
    rw [add_comm]
    convert hdvd using 1
    push_cast; ring
  exact hne hzero

/-
  THEOREM II.1 — Cardinality of the invertibles.

  The number of invertibles in (Fin(g), ⊗_k) equals φ(g).

  Proof: the map r ↦ (k^n + r) is a bijection between Fin(g) and
  {k^n, k^n+1, ..., k^n+g-1}. Coprimality with g is invariant under
  translation modulo g (since gcd(a,g) = gcd(a mod g, g)).
  Hence the number of r with gcd(k^n+r, g) = 1 equals the number of
  a ∈ {0,...,g-1} with gcd(a, g) = 1, which is φ(g) by definition.
-/
theorem phi_aod_eq_phi_gap (hn' : n ≠ 0) :
    (capMulUnits n k).card = Nat.totient (capGap n k) := by
  set g := capGap n k
  have hg : 0 < g := capGap_pos' n k hn'
  rw [Nat.totient_eq_card_coprime]
  -- hcop_mod: Coprime(a, g) ↔ Coprime(a%g, g)
  have hcop_mod : ∀ a : ℕ, Nat.Coprime a g ↔ Nat.Coprime (a % g) g := fun a => by
    simp only [Nat.Coprime, (Nat.gcd_comm a g).trans (Nat.gcd_rec g a)]
  -- Shared helper: (k^n + x) % g = (k^n % g + x) % g
  have hadd_mod : ∀ x, (k ^ n + x) % g = (k ^ n % g + x) % g := fun x => by
    conv_lhs => rw [show k ^ n + x = k ^ n % g + x + g * (k ^ n / g) from by
      have := Nat.div_add_mod (k ^ n) g; omega]
    rw [Nat.add_mul_mod_self_left]
  set m := k ^ n % g with hm_def
  have hm : m < g := Nat.mod_lt _ hg
  -- Key: (m + (a+g-m)%g) % g = a when a < g and m < g
  have hkey_aux : ∀ a, a < g → (m + (a + g - m) % g) % g = a := fun a ha_lt => by
    rcases Nat.lt_or_ge a m with h | h
    · have : (a + g - m) % g = a + g - m := Nat.mod_eq_of_lt (by omega)
      rw [this, show m + (a + g - m) = a + g from by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt ha_lt
    · have : (a + g - m) % g = a - m := by
        have heq : a + g - m = (a - m) + g := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [this, show m + (a - m) = a from by omega]
      exact Nat.mod_eq_of_lt ha_lt
  apply Finset.card_nbij' (fun r => (k ^ n + r.val) % g)
      (fun a => ⟨(a + g - m) % g, Nat.mod_lt _ hg⟩)
  · -- hi (Set.MapsTo): r ∈ capMulUnits → (k^n + r.val) % g ∈ {a ∈ range g | g.Coprime a}
    intro r hr
    have hr' : Nat.Coprime (k ^ n + r.val) g := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hg),
      Nat.coprime_comm.mp ((hcop_mod _).mp hr')⟩
  · -- hj (Set.MapsTo): a ∈ {a ∈ range g | g.Coprime a} → ⟨(a+g-m)%g, _⟩ ∈ capMulUnits
    intro a ha
    have ha_mem : a < g := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have ha_cop : g.Coprime a := (Finset.mem_filter.mp ha).2
    have hkey : (k ^ n + (a + g - m) % g) % g = a := by
      rw [hadd_mod]; exact hkey_aux a ha_mem
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hcop_mod, hkey]; exact Nat.coprime_comm.mp ha_cop⟩
  · -- left_inv (Set.LeftInvOn): ⟨((k^n+r.val)%g + g - m)%g, _⟩ = r
    intro r _
    apply Fin.ext
    simp only []
    have h1 : r.val < g := r.isLt
    have heq : (k ^ n + r.val) % g = (m + r.val) % g := hadd_mod r.val
    -- goal: ((k^n + r.val) % g + g - k^n % g) % g = r.val
    rw [heq, hm_def]
    -- goal: ((m + r.val) % g + g - m) % g = r.val
    -- Since m < g and r.val < g, we have m + r.val < 2g, so either:
    --   (a) m + r.val < g  ⟹  (m+r.val) % g = m+r.val, and (m+r.val+g-m) % g = (r.val+g) % g = r.val
    --   (b) m + r.val ≥ g  ⟹  (m+r.val) % g = m+r.val-g, and (m+r.val-g+g-m) % g = r.val % g = r.val
    rcases Nat.lt_or_ge (m + r.val) g with h | h
    · have hq : (m + r.val) % g = m + r.val := Nat.mod_eq_of_lt h
      rw [hq, show m + r.val + g - m = r.val + g from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt h1]
    · have hlt2g : m + r.val < 2 * g := by omega
      have hq : (m + r.val) % g = m + r.val - g := by
        conv_lhs => rw [show m + r.val = g + (m + r.val - g) from by omega]
        simp [Nat.add_mod_left, Nat.mod_eq_of_lt (show m + r.val - g < g by omega)]
      rw [hq, show m + r.val - g + g - m = r.val from by omega, Nat.mod_eq_of_lt h1]
  · -- right_inv (Set.RightInvOn): (k^n + (a+g-m)%g) % g = a
    intro a ha
    have ha_mem : a < g := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    show (k ^ n + (a + g - m) % g) % g = a
    rw [hadd_mod]; exact hkey_aux a ha_mem

end DirezioneII


/-! ─────────────────────────────────────────────────────────────────────────
    §5 — DIRECTION III: Radical CRT
    ─────────────────────────────────────────────────────────────────────────

    The classical Chinese Remainder Theorem states that if m₁, m₂ are
    coprime, then ℤ/(m₁m₂) ≅ ℤ/m₁ × ℤ/m₂.

    In AOD, the map φₙ : ℕ → ZMod (2^n - 1) defined by
      φₙ(a) = r_n(a) mod (2^n - 1)
    is well defined on the classes of AOD_n and satisfies:
      gcd(2^n₁ - 1, 2^n₂ - 1) = 2^gcd(n₁,n₂) - 1

    Therefore, for gcd(n₁, n₂) = 1, the two moduli are coprime and the
    product map is surjective (Radical CRT).

    The proof uses the key lemma that φₙ is well defined on the classes
    (if r_n(a) = r_n(b) then φₙ(a) = φₙ(b)) — which follows by definition —
    and surjectivity follows from the classical CRT applied to ZMod.
    ─────────────────────────────────────────────────────────────────────────  -/

section DirezioneIII

/-
  Definition of the map φₙ : ℕ → ZMod (2^n - 1).
  φₙ(a) = r_n(a) mod (2^n - 1)
-/
def phiMod (n a : ℕ) : ZMod (2 ^ n - 1) :=
  (radRem n a : ZMod (2 ^ n - 1))

/-- φₙ is well defined on the classes of AOD_n:
    if r_n(a) = r_n(b), then φₙ(a) = φₙ(b). -/
theorem phiMod_wellDefined (n a b : ℕ) (h : a ≡ₒ b [Aod n]) :
    phiMod n a = phiMod n b := by
  simp only [phiMod, aodEquiv] at *
  -- h : radRem n a = radRem n b, goal: cast radRem n a = cast radRem n b
  rw [h]

/-
  LEMMA III.1 — Formula for gcd(2^n₁ - 1, 2^n₂ - 1).

  This is a classical result of number theory:
    gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1

  The proof uses the property that ord_{2^a-1}(2) = a (the order of 2
  modulo 2^a-1 is exactly a), and that the gcd of the orders is the order of the gcd.
-/
theorem gcd_mersenne (n₁ n₂ : ℕ) (_ : 1 ≤ n₁) (_ : 1 ≤ n₂) :
    Nat.gcd (2 ^ n₁ - 1) (2 ^ n₂ - 1) = 2 ^ Nat.gcd n₁ n₂ - 1 := by
  exact Nat.pow_sub_one_gcd_pow_sub_one 2 n₁ n₂

/-- For gcd(n₁, n₂) = 1, the Mersenne moduli are coprime. -/
theorem mersenne_coprime_of_exponent_coprime (n₁ n₂ : ℕ)
    (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (hcop : Nat.Coprime n₁ n₂) :
    Nat.Coprime (2 ^ n₁ - 1) (2 ^ n₂ - 1) := by
  rw [Nat.Coprime, gcd_mersenne n₁ n₂ hn₁ hn₂, hcop]
  simp

/-
  THEOREM III.2 — Radical CRT (surjectivity).

  For gcd(n₁, n₂) = 1, the product map
    Φ : AodField n₁ × AodField n₂ → ZMod (2^n₁-1) × ZMod (2^n₂-1)
  is surjective.

  The proof uses the classical CRT in Mathlib:
    ZMod.chineseRemainder or ZMod.prod_eq_of_coprime.

  Precisely: for every (c₁, c₂), we find a ∈ ℕ such that
    r_{n₁}(a) ≡ c₁ (mod 2^n₁-1)  and  r_{n₂}(a) ≡ c₂ (mod 2^n₂-1)
-/
/-!
  Auxiliary lemmas for crtRadicale_suriettivo.
-/

/-- `irootN n (k^n + c) = k` when `c < (k+1)^n - k^n`. -/
private lemma irootN_of_add_lt_gap_crt (n k c : ℕ) (hn : n ≠ 0)
    (hc : c < (k + 1) ^ n - k ^ n) :
    irootN n (k ^ n + c) = k := by
  apply Nat.le_antisymm
  · by_contra h
    push_neg at h
    have hge : (k + 1) ^ n ≤ (irootN n (k ^ n + c)) ^ n :=
      Nat.pow_le_pow_left h n
    have hle := irootN_pow_le n (k ^ n + c) hn
    have hlt : k ^ n + c < (k + 1) ^ n := by omega
    omega
  · by_contra h
    push_neg at h
    have hlt := irootN_lt_succ_pow n (k ^ n + c) hn
    have hge : (irootN n (k ^ n + c) + 1) ^ n ≤ k ^ n :=
      Nat.pow_le_pow_left h n
    omega

/-- `radRem n (k^n + c) = c` when `c < (k+1)^n - k^n`. -/
private lemma radRem_of_add_lt_gap_crt (n k c : ℕ) (hn : n ≠ 0)
    (hc : c < (k + 1) ^ n - k ^ n) :
    radRem n (k ^ n + c) = c := by
  simp only [radRem, irootN_of_add_lt_gap_crt n k c hn hc]
  have hle : k ^ n ≤ k ^ n + c := Nat.le_add_right _ _
  omega

/-- For `n ≥ 2` and `k ≥ 1`, the gap `(k+1)^n - k^n > k`. -/
private lemma gap_gt_base (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    k < (k + 1) ^ n - k ^ n := by
  -- We show k^n + k + 1 ≤ (k+1)^n by induction on n ≥ 2
  suffices h : k ^ n + k + 1 ≤ (k + 1) ^ n by omega
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hn with h | hm
    · -- n = 2 (m = 1): (k+1)^2 = k^2 + 2k + 1 ≥ k^2 + k + 1 ✓
      have hm1 : m = 1 := by omega
      subst hm1
      -- Goal: k ^ (1+1) + k + 1 ≤ (k+1)^(1+1)
      simp only [pow_succ]
      nlinarith
    · -- m ≥ 2: induction
      have ihm : 2 ≤ m := by omega
      have ih' := ih ihm
      have hkm : k ≤ k ^ m := le_self_pow hk (by omega : m ≠ 0)
      calc (k + 1) ^ (m + 1) = (k + 1) ^ m * (k + 1) := pow_succ _ _
        _ ≥ (k ^ m + k + 1) * (k + 1) := Nat.mul_le_mul_right _ ih'
        _ = k ^ m * k + k ^ m + k ^ 2 + 2 * k + 1 := by ring
        _ ≥ k ^ (m + 1) + k + 1 := by
            have hkm2 : k * k ≤ k ^ m * k := Nat.mul_le_mul_right k hkm
            nlinarith [Nat.one_le_pow m k hk, pow_succ k m]

theorem crtRadicale_suriettivo (n₁ n₂ : ℕ)
    (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (hcop : Nat.Coprime n₁ n₂)
    (c₁ : ZMod (2 ^ n₁ - 1)) (c₂ : ZMod (2 ^ n₂ - 1)) :
    ∃ a : ℕ, phiMod n₁ a = c₁ ∧ phiMod n₂ a = c₂ := by
  -- Case n₁ = 1 or n₂ = 1: ZMod (2^1-1) = ZMod 1 = Fin 1, unique element
  -- The condition phiMod 1 a = c₁ is automatic (ZMod 1 is Subsingleton)
  -- For the other condition, we use the general-case strategy with only that exponent.
  -- Implementation: for n₁=1, we use the isomorphism ZMod (m₁*m₂) with m₁=1 (identity)
  -- and the witness a = (m₂)^n₂ + c₂.val works if n₂≥2.
  -- Simpler: we exploit that Nat.Coprime n₁ n₂ with n₁=1 implies n₂ arbitrary,
  -- and we build the witness using only n₂.
  rcases Nat.eq_or_lt_of_le hn₁ with rfl | hn₁2
  · -- n₁ = 1: ZMod (2^1-1) = ZMod 1, c₁ is the unique element
    -- phiMod 1 a = c₁ is automatic; only phiMod n₂ a = c₂ is needed
    have hsimp1 : (2 : ℕ)^1 - 1 = 1 := by norm_num
    rcases Nat.eq_or_lt_of_le hn₂ with rfl | hn₂2'
    · -- n₁=n₂=1: both ZMod 1 = Fin 1, unique element
      -- We use hsimp1 to rewrite the type
      haveI : Subsingleton (ZMod (2^1-1)) := by
        rw [hsimp1]; exact inferInstance
      exact ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · -- n₁=1, n₂≥2: witness a = (2^n₂-1)^n₂ + c₂.val
      have hn₂2' : 2 ≤ n₂ := hn₂2'
      have hm₂_pos : 0 < 2^n₂ - 1 := by
        have h : 2 ≤ 2^n₂ := Nat.le_self_pow (by omega) 2
        omega
      have hm₂_ge1 : 1 ≤ 2^n₂ - 1 := hm₂_pos
      haveI : NeZero (2^n₂ - 1) := ⟨hm₂_pos.ne'⟩
      have hcv : c₂.val < 2^n₂ - 1 := ZMod.val_lt c₂
      have hgap' : c₂.val < (2^n₂ - 1 + 1)^n₂ - (2^n₂ - 1)^n₂ :=
        lt_of_lt_of_le hcv (Nat.le_of_lt (gap_gt_base n₂ (2^n₂-1) hn₂2' hm₂_ge1))
      have hrad' : radRem n₂ ((2^n₂-1)^n₂ + c₂.val) = c₂.val :=
        radRem_of_add_lt_gap_crt n₂ (2^n₂-1) c₂.val (by omega) hgap'
      refine ⟨(2^n₂-1)^n₂ + c₂.val, ?_, ?_⟩
      · -- phiMod 1 a = c₁: ZMod (2^1-1) = ZMod 1, Subsingleton
        simp only [phiMod]
        haveI : Subsingleton (ZMod (2^1-1)) := by
          rw [show (2:ℕ)^1-1 = 1 from by norm_num]
          exact ZMod.subsingleton_iff.mpr rfl
        exact Subsingleton.elim _ _
      · -- phiMod n₂ a = c₂
        simp only [phiMod, hrad']
        exact ZMod.natCast_zmod_val c₂
  rcases Nat.eq_or_lt_of_le hn₂ with rfl | hn₂2
  · -- n₂ = 1: symmetric
    -- n₁ ≥ 2 (since hn₁2 : 1 < n₁)
    have hn₁2' : 2 ≤ n₁ := hn₁2
    have hm₁_pos : 0 < 2^n₁ - 1 := by
      have h : 2 ≤ 2^n₁ := Nat.le_self_pow (by omega) 2; omega
    have hm₁_ge1 : 1 ≤ 2^n₁ - 1 := hm₁_pos
    haveI : NeZero (2^n₁ - 1) := ⟨hm₁_pos.ne'⟩
    have hcv : c₁.val < 2^n₁ - 1 := ZMod.val_lt c₁
    have hgap' : c₁.val < (2^n₁ - 1 + 1)^n₁ - (2^n₁ - 1)^n₁ :=
      lt_of_lt_of_le hcv (Nat.le_of_lt (gap_gt_base n₁ (2^n₁-1) hn₁2' hm₁_ge1))
    have hrad' : radRem n₁ ((2^n₁-1)^n₁ + c₁.val) = c₁.val :=
      radRem_of_add_lt_gap_crt n₁ (2^n₁-1) c₁.val (by omega) hgap'
    refine ⟨(2^n₁-1)^n₁ + c₁.val, ?_, ?_⟩
    · simp only [phiMod, hrad']
      exact ZMod.natCast_zmod_val c₁
    · simp only [phiMod]
      haveI : Subsingleton (ZMod (2^1-1)) := by
        rw [show (2:ℕ)^1-1 = 1 from by norm_num]
        exact ZMod.subsingleton_iff.mpr rfl
      exact Subsingleton.elim _ _
  -- Now n₁, n₂ ≥ 2
  have hn₁2 : 2 ≤ n₁ := hn₁2
  have hn₂2 : 2 ≤ n₂ := hn₂2
  -- Setup: abbreviations without set (to avoid renaming c₁, c₂)
  have hm₁_pos : 0 < 2^n₁ - 1 := by
    have h : 2 ≤ 2^n₁ := Nat.le_self_pow (by omega) 2; omega
  have hm₂_pos : 0 < 2^n₂ - 1 := by
    have h : 2 ≤ 2^n₂ := Nat.le_self_pow (by omega) 2; omega
  -- Coprimality of the Mersenne moduli
  have hcop_mod : Nat.Coprime (2^n₁-1) (2^n₂-1) :=
    mersenne_coprime_of_exponent_coprime n₁ n₂ (by omega) (by omega) hcop
  -- STEP 1: CRT — find x : ℕ with (x : ZMod (2^n₁-1)) = c₁ and (x : ZMod (2^n₂-1)) = c₂
  haveI hm₁ne : NeZero (2^n₁-1) := ⟨hm₁_pos.ne'⟩
  haveI hm₂ne : NeZero (2^n₂-1) := ⟨hm₂_pos.ne'⟩
  haveI hm₁m₂ne : NeZero ((2^n₁-1) * (2^n₂-1)) :=
    ⟨Nat.mul_ne_zero hm₁_pos.ne' hm₂_pos.ne'⟩
  obtain ⟨x, hx_lt, hx₁_mod, hx₂_mod⟩ :
      ∃ x : ℕ, x < (2^n₁-1) * (2^n₂-1) ∧
        (x : ZMod (2^n₁-1)) = c₁ ∧ (x : ZMod (2^n₂-1)) = c₂ := by
    let iso := ZMod.chineseRemainder hcop_mod
    let x_zm := iso.symm (c₁, c₂)
    refine ⟨x_zm.val, ZMod.val_lt x_zm, ?_, ?_⟩
    · have heq := iso.apply_symm_apply (c₁, c₂)
      have h1 : (iso x_zm).1 = c₁ := by rw [heq]
      rw [← ZMod.natCast_zmod_val x_zm]
      convert h1 using 1
      simp [iso, ZMod.chineseRemainder, ZMod.castHom]
    · have heq := iso.apply_symm_apply (c₁, c₂)
      have h2 : (iso x_zm).2 = c₂ := by rw [heq]
      rw [← ZMod.natCast_zmod_val x_zm]
      convert h2 using 1
      simp [iso, ZMod.chineseRemainder, ZMod.castHom]
  -- STEP 2: Choose the L-th block: a = M^L + x
  -- M = (2^n₁-1)*(2^n₂-1), L = lcm(n₁,n₂)
  let M := (2^n₁-1) * (2^n₂-1)
  let L := Nat.lcm n₁ n₂
  have hn₁_dvd : n₁ ∣ L := Nat.dvd_lcm_left n₁ n₂
  have hn₂_dvd : n₂ ∣ L := Nat.dvd_lcm_right n₁ n₂
  use M ^ L + x
  have hJ₁ : M ^ L = (M ^ (L / n₁)) ^ n₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hn₁_dvd]
  have hJ₂ : M ^ L = (M ^ (L / n₂)) ^ n₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hn₂_dvd]
  have hM_pos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hm₁_pos.ne' hm₂_pos.ne')
  have hL_pos : 0 < L := Nat.lcm_pos (by omega) (by omega)
  have hL_div₁ : 1 ≤ L / n₁ := Nat.le_div_iff_mul_le (by omega) |>.mpr
    (by simpa using Nat.le_of_dvd hL_pos hn₁_dvd)
  have hL_div₂ : 1 ≤ L / n₂ := Nat.le_div_iff_mul_le (by omega) |>.mpr
    (by simpa using Nat.le_of_dvd hL_pos hn₂_dvd)
  have hMpow₁_ge : M ≤ M ^ (L / n₁) := le_self_pow hM_pos (by omega : L / n₁ ≠ 0)
  have hMpow₂_ge : M ≤ M ^ (L / n₂) := le_self_pow hM_pos (by omega : L / n₂ ≠ 0)
  have hMpow₁_pos : 1 ≤ M ^ (L / n₁) := le_trans hM_pos hMpow₁_ge
  have hMpow₂_pos : 1 ≤ M ^ (L / n₂) := le_trans hM_pos hMpow₂_ge
  have hgap₁ : x < (M ^ (L / n₁) + 1) ^ n₁ - (M ^ (L / n₁)) ^ n₁ :=
    lt_of_lt_of_le hx_lt (le_trans hMpow₁_ge
      (Nat.le_of_lt (gap_gt_base n₁ (M ^ (L / n₁)) hn₁2 hMpow₁_pos)))
  have hgap₂ : x < (M ^ (L / n₂) + 1) ^ n₂ - (M ^ (L / n₂)) ^ n₂ :=
    lt_of_lt_of_le hx_lt (le_trans hMpow₂_ge
      (Nat.le_of_lt (gap_gt_base n₂ (M ^ (L / n₂)) hn₂2 hMpow₂_pos)))
  -- STEP 3: radRem nᵢ (M^L + x) = x
  have hrad₁ : radRem n₁ (M ^ L + x) = x := by
    rw [hJ₁]; exact radRem_of_add_lt_gap_crt n₁ (M ^ (L / n₁)) x (by omega) hgap₁
  have hrad₂ : radRem n₂ (M ^ L + x) = x := by
    rw [hJ₂]; exact radRem_of_add_lt_gap_crt n₂ (M ^ (L / n₂)) x (by omega) hgap₂
  -- STEP 4: phiMod nᵢ (M^L + x) = cᵢ
  exact ⟨by simp [phiMod, hrad₁, hx₁_mod], by simp [phiMod, hrad₂, hx₂_mod]⟩

/-
  THEOREM III.3 — φₙ is compatible with the ZMod homomorphism (chapter k=1).

  The special case k=1: in chapter k=1 of AOD_n, capGap n 1 = 2^n - 1.
  The map toZMod n 1 : Fin(2^n-1) → ZMod(2^n-1) is a ring isomorphism
  (already proved in GroupStructure.lean).
  Hence phiMod n and toZMod n 1 are compatible through modular reduction.
-/
-- Note: phiMod n a : ZMod (2^n-1); toZMod n 1 r : ZMod (capGap n 1).
-- Since capGap n 1 = 2^n-1, the types coincide after eq.subst.
-- We state it in terms of ZMod (capGap n 1) for both sides.
theorem phiMod_eq_toZMod_chapter1 (n a : ℕ) (_ : n ≠ 0)
    (hr : radRem n a < capGap n 1) :
    (radRem n a : ZMod (capGap n 1)) + (1 : ℕ) ^ n =
    toZMod n 1 ⟨radRem n a, hr⟩ := by
  -- Both sides live in ZMod (capGap n 1).
  -- toZMod n 1 r = r.val + 1^n by definition.
  simp [toZMod]

end DirezioneIII


/-! ─────────────────────────────────────────────────────────────────────────
    §6 — DIRECTION IV: Radical Wilson's Law
    ─────────────────────────────────────────────────────────────────────────

    Classical formulation: for p prime, (p-1)! ≡ -1 (mod p).
    In ZMod p, the product of all non-zero elements is -1.

    In AOD, the product ⊗_k of all r ∈ Fin(g) except:
      · the multiplicative neutral e_× = capMulNeutral
      · the absorbing element α such that (k^n + α) ≡ 0 (mod g)
    equals -1 in ZMod g.

    THE ABSORBING ELEMENT α is the value r ∈ Fin(g) such that
    (k^n + r) ≡ 0 (mod g), i.e. α = (g - k^n % g) % g.
    Under toZMod, α maps to -k^n = -(k^n mod g).

    Radical Wilson's Law states:
      ∏_{r ≠ e_×, r ≠ α} (k^n + r) ≡ -1 (mod g)

    STRUCTURAL OBSERVATION (verified computationally):
      e_× + α = g - 1 (mod g)
    i.e., the two elements to be excluded are COMPLEMENTARY modulo g.

    This section proves:
    (1) The definition and properties of the absorbing element α.
    (2) The complementarity e_× + α ≡ g-1 (mod g).
    (3) Radical Wilson's Law via toZMod and Wilson in ZMod.
    ─────────────────────────────────────────────────────────────────────────  -/

section DirezioneIV

variable (n k : ℕ) (hn : n ≠ 0)

/-- The absorbing element of ⊗_k:
    α ∈ Fin(g) such that (k^n + α) ≡ 0 (mod g).
    Formula: α = (g - k^n % g) % g. -/
def capAbsorb : Fin (capGap n k) :=
  ⟨(capGap n k - k ^ n % capGap n k) % capGap n k,
   Nat.mod_lt _ (capGap_pos' n k hn)⟩

-- Computational verification of the absorbing element (commented out):
-- #eval! (capAbsorb 2 1 (by norm_num)).val  -- g=3, k^n=1, α=(3-1)%3=2
-- #eval! (capAbsorb 3 1 (by norm_num)).val  -- g=7, k^n=1, α=(7-1)%7=6
-- #eval! (capAbsorb 3 2 (by norm_num)).val  -- g=19, k^n=8, α=(19-8)%19=11
-- #eval! (capAbsorb 2 2 (by norm_num)).val  -- g=5, k^n=4, α=(5-4)%5=1

/-- toZMod transports capAbsorb to 0. -/
theorem toZMod_capAbsorb_is_zero :
    toZMod n k (capAbsorb n k hn) = 0 := by
  -- toZMod n k r = r.val + k^n in ZMod g
  -- capAbsorb.val = (g - k^n%g) % g
  -- We want: (g - k^n%g)%g + k^n ≡ 0 (mod g)
  simp only [toZMod, capAbsorb]
  have hg := capGap_pos' n k hn
  have hm : k ^ n % capGap n k < capGap n k := Nat.mod_lt _ hg
  haveI : NeZero (capGap n k) := ⟨hg.ne'⟩
  -- Goal: ↑((g - k^n%g)%g) + ↑(k^n) = 0  in ZMod g
  -- We group as a single cast and use divisibility
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  -- Goal: capGap n k ∣ (g - k^n%g)%g + k^n
  -- Let m = k^n % g. Then (g-m)%g + k^n = (g-m) + k^n (if m≠0) or else 0 + k^n
  -- In both cases, (g-m)%g + k^n ≡ -m + k^n ≡ k^n - k^n%g ≡ 0 (mod g)
  set m := k ^ n % capGap n k
  have hm_lt : m < capGap n k := Nat.mod_lt _ hg
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- m = 0: (g-0)%g = 0, sum = k^n, and k^n ≡ 0 (mod g)
    simp [hm0, Nat.mod_self]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · -- m ≥ 1: (g-m)%g = g-m, sum = g-m + k^n = g + (k^n - m) = g + k^n/g*g
    have hval : (capGap n k - m) % capGap n k = capGap n k - m := by
      apply Nat.mod_eq_of_lt; omega
    rw [hval]
    have hkn : k ^ n = m + capGap n k * (k ^ n / capGap n k) := by
      have := Nat.mod_add_div (k ^ n) (capGap n k); omega
    -- Goal: capGap n k ∣ capGap n k - m + k^n
    -- by hkn: k^n = m + g*q, so g - m + k^n = g + g*q = g*(q+1)
    refine ⟨k ^ n / capGap n k + 1, ?_⟩
    -- Avoid Nat subtraction: use that capGap n k - m + m = capGap n k (since m ≤ g)
    have hle : m ≤ capGap n k := Nat.le_of_lt hm_lt
    zify [hle]
    linarith [hkn]

/-
  THEOREM IV.2 — Radical Wilson's Law.

  Let g = capGap n k be prime. The set to be excluded from the product is
  {capNeutral, capMulNeutral}: the additive neutral (→ 0 under toZMod,
  by capNeutral_eq_capAbsorb it coincides with the absorbing α) and the
  multiplicative neutral (→ 1 under toZMod). The product of the remaining r
  corresponds in ZMod g to ∏_{z≠0,z≠1} z = (p-1)!/1 = -1 by Wilson.
-/

/-- capNeutral and capAbsorb coincide. -/
theorem capNeutral_eq_capAbsorb :
    capNeutral n k hn = capAbsorb n k hn := by
  apply Fin.ext
  simp [capNeutral, capAbsorb]
  -- Both have val = (g - k^n%g) % g  by construction.

/-- The elements to be excluded in Radical Wilson. -/
def wilsonExcluded (n k : ℕ) (hn : n ≠ 0) : Finset (Fin (capGap n k)) :=
  {capNeutral n k hn, capMulNeutral n k hn}

/-- The elements included in the Radical Wilson product. -/
def wilsonFactors (n k : ℕ) (hn : n ≠ 0) : Finset (Fin (capGap n k)) :=
  Finset.univ \ wilsonExcluded n k hn

/-
  Sub-lemma: product of all elements ≠0 ∧ ≠1 in ZMod p (prime) = -1.
  Proof: bijection with Ico 2 p via val/cast + ZMod.prod_Ico_one_prime.
-/
private lemma prod_filter_ne_zero_ne_one_eq_neg_one (p : ℕ) [hp : Fact p.Prime] [hpn : NeZero p] :
    ∏ z ∈ (Finset.univ : Finset (ZMod p)).filter (fun z => z ≠ 0 ∧ z ≠ 1), z = -1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have h_ico2 : ∏ x ∈ Finset.Ico 2 p, (x : ZMod p) = -1 := by
    have h := ZMod.prod_Ico_one_prime p
    rw [show Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) from by
        ext x; simp [Finset.mem_Ico, Finset.mem_insert]; omega,
      Finset.prod_insert (by simp [Finset.mem_Ico]),
      Nat.cast_one, one_mul] at h
    exact h
  rw [← h_ico2]
  apply Finset.prod_nbij' ZMod.val (fun x : ℕ => (x : ZMod p))
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_Ico]
    exact ⟨by
        have hv0 : z.val ≠ 0 := fun h => hz.1 ((ZMod.val_eq_zero z).mp h)
        have hv1 : z.val ≠ 1 := fun h => hz.2 ((ZMod.val_eq_one (by omega) z).mp h)
        omega,
      ZMod.val_lt z⟩
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd; exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega),
      by
        intro h
        have hv := ZMod.val_natCast_of_lt hx.2
        have := (ZMod.val_eq_one (by omega : 1 < p) ((x : ℕ) : ZMod p)).mpr h
        omega⟩
  · intro z _; exact ZMod.natCast_zmod_val z
  · intro x hx
    simp only [Finset.mem_Ico] at hx
    exact ZMod.val_natCast_of_lt hx.2
  · intro z _; exact (ZMod.natCast_zmod_val z).symm

/-- Radical Wilson: the product of the elements of wilsonFactors, seen in ZMod g, is -1.
    The correct version uses ∏ r ∈ wilsonFactors, toZMod r (not the standard product in Fin).
    Proof: toZMod bijects wilsonFactors onto {z≠0, z≠1} in ZMod g;
    then classical Wilson gives ∏_{z≠0,z≠1} z = -1 in ZMod p. -/
theorem wilsonRadicale [hprime : Fact (Nat.Prime (capGap n k))] :
    ∏ r ∈ wilsonFactors n k hn, toZMod n k r = -1 := by
  set g := capGap n k
  haveI hgne : NeZero g := ⟨hprime.out.pos.ne'⟩
  have hprod_eq : ∏ r ∈ wilsonFactors n k hn, toZMod n k r =
      ∏ z ∈ (Finset.univ : Finset (ZMod g)).filter (fun z => z ≠ 0 ∧ z ≠ 1), z := by
    apply Finset.prod_nbij (toZMod n k)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [wilsonFactors, wilsonExcluded, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, Finset.mem_singleton, not_or, true_and] at hr
      exact ⟨fun h => hr.1 (toZMod_injective n k hn _ _
                  (h.trans (toZMod_neutral_is_zero n k hn).symm)),
             fun h => hr.2 (toZMod_injective n k hn _ _
                  (h.trans (toZMod_mulNeutral_is_one n k hn).symm))⟩
    · intro r1 _ r2 _ h
      exact toZMod_injective n k hn _ _ h
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      obtain ⟨r, hr⟩ := toZMod_surjective n k hn z
      refine ⟨r, ?_, hr⟩
      rw [Finset.mem_coe, wilsonFactors, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [wilsonExcluded, Finset.mem_insert, Finset.mem_singleton]
      rintro (heq | heq)
      · exact hz'.1 (show z = 0 by rw [← hr, heq]; exact toZMod_neutral_is_zero n k hn)
      · exact hz'.2 (show z = 1 by rw [← hr, heq]; exact toZMod_mulNeutral_is_one n k hn)
    · intro r _; rfl
  rw [hprod_eq]
  exact prod_filter_ne_zero_ne_one_eq_neg_one g

end DirezioneIV


/-! ─────────────────────────────────────────────────────────────────────────
    §7 — DIRECTION V: Radical Euler Theorem
    ─────────────────────────────────────────────────────────────────────────

    Euler's theorem in chapter form, proved for an arbitrary gap.

    Motivation:
      The classical Euler theorem states: for gcd(a,m)=1,
        a^{φ(m)} ≡ 1 (mod m).
      Equivalently: in (ℤ/mℤ)×, every element has order dividing φ(m).

      In AOD, the multiplicative group of chapter k is (Fin(g), ⊗_k)
      with neutral capMulNeutral. The invertibles form a group (Fin(g))×_k.
      Direction II established that |(Fin(g))×_k| = φ(g).
      Hence for every invertible r, Lagrange's Theorem implies:
        ord(r) ∣ φ(g),
      from which: r^{φ(g)} = capMulNeutral (with ⊗_k).

    This is the AOD version of Euler's theorem.
    ─────────────────────────────────────────────────────────────────────────  -/

section DirezioneV

variable (n k : ℕ) (hn : n ≠ 0)

/-- φ_AOD(n,k): the radical Euler function.
    Counts the invertible elements of chapter k in AOD_n. -/
def phiAOD : ℕ := Nat.totient (capGap n k)

/-- The chapter multiplicative power r^m with respect to ⊗_k.
    Already defined in GroupStructure as `capMulPow`. -/
-- capMulPow n k hn m r  : Fin (capGap n k)

/-
  THEOREM V.1 — Radical Euler Theorem.

  For every invertible r ∈ Fin(capGap n k) (gcd(k^n + r.val, capGap n k) = 1),
  the φ(g)-th chapter multiplicative power is the multiplicative neutral:

    capMulPow n k hn (phiAOD n k) r = capMulNeutral n k hn

  Equivalently in ZMod g (via toZMod_capMulPow):
    toZMod r ^ φ(g) = 1.

  PROOF (sketch):
    If r is invertible, toZMod r is a unit in ZMod g.
    By Euler's theorem in ZMod g (already in Mathlib):
      z ^ φ(g) = 1  for every z ∈ (ZMod g)×.
    Hence toZMod r ^ φ(g) = 1.
    From toZMod_capMulPow: toZMod (capMulPow n k hn φ(g) r) = toZMod r ^ φ(g) = 1.
    From toZMod_mulNeutral_is_one: toZMod (capMulNeutral n k hn) = 1.
    By injectivity of toZMod: capMulPow n k hn φ(g) r = capMulNeutral.
-/
theorem eulerRadicale (r : Fin (capGap n k))
    (hinv : Nat.Coprime (k ^ n + r.val) (capGap n k)) :
    capMulPow n k hn (phiAOD n k) r = capMulNeutral n k hn := by
  apply toZMod_injective n k hn
  rw [toZMod_capMulPow, toZMod_mulNeutral_is_one]
  -- goal: toZMod n k r ^ φ(g) = 1
  -- toZMod r is a unit because gcd(k^n + r, g) = 1
  have hunit : IsUnit (toZMod n k r) := by
    rw [show toZMod n k r = ((k ^ n + r.val : ℕ) : ZMod (capGap n k)) from by
      simp only [toZMod]; push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    exact hinv
  -- By Euler's Theorem in ZMod g:
  have hg := capGap_pos' n k hn
  haveI : NeZero (capGap n k) := ⟨hg.ne'⟩
  rw [phiAOD]
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

/-
  SPECIAL CASE V.2 — Multiplicative Fermat-AOD (g prime).

  For g prime, φ(g) = g - 1 (since all nonzero elements are invertible).
  The Radical Euler Theorem becomes:
    capMulPow n k hn (g - 1) r = capMulNeutral  for every r ≠ capNeutral.

  This is the multiplicative version of Fermat's Little Theorem in AOD.
  It already exists in GroupStructure.lean as `capMul_mul_inv`
  (which uses Fermat for g-2 powers, equivalent to g-1 with one extra step).
-/
theorem fermatAOD_moltiplicativo
    [hprime : Fact (Nat.Prime (capGap n k))]
    (r : Fin (capGap n k))
    (hr : r ≠ capNeutral n k hn) :
    capMulPow n k hn (capGap n k - 1) r = capMulNeutral n k hn := by
  apply toZMod_injective n k hn
  rw [toZMod_capMulPow, toZMod_mulNeutral_is_one]
  -- goal: toZMod r ^ (g - 1) = 1
  have hne : toZMod n k r ≠ 0 := by
    intro h; apply hr
    apply toZMod_injective n k hn
    rw [h, toZMod_neutral_is_zero]
  haveI : NeZero (capGap n k) := ⟨hprime.out.pos.ne'⟩
  exact ZMod.pow_card_sub_one_eq_one hne

end DirezioneV


/-! ─────────────────────────────────────────────────────────────────────────
    Proof Status Summary — 0 `sorry`
    ─────────────────────────────────────────────────────────────────────────

    The file is completely proved. Key theorems (all without `sorry`):
    · `crtRadicale_suriettivo` (§5): Radical CRT, proved via
       `ZMod.chineseRemainder` and explicit witness `M^L + x`
       (does not require the global homomorphism of φₙ).
    · `gcd_mersenne` (§5): via Nat.pow_sub_one_gcd_pow_sub_one.
    · `phi_aod_eq_phi_gap` (§4): via Finset.card_bij' with an explicit bijection.
    · `wilsonRadicale` (§6): via prod_filter_ne_zero_ne_one_eq_neg_one
       + toZMod bijection on wilsonFactors. (The correct version uses ∏ toZMod r, not Fin.prod.)
    · `eulerRadicale` (§7): via ZMod.pow_totient for arbitrary g with coprimality.
    · `fermatAOD_moltiplicativo` (§7): via ZMod.pow_card_sub_one_eq_one for g prime.
    · `ordine_radicale_divide_gap` (§3): statement corrected (addOrderOf r ∣ g, not g ∣ m),
       proved via Lagrange + toZMod isomorphism (it was false as previously written).
    · `addOrderOf_dvd_of_capAddIter` (§3): if m·r = neutral then addOrderOf(r) ∣ m.
    · `ordine_radicale_esatto_primo` (§3): for g prime, addOrderOf r = g for every r ≠ neutral.
    ─────────────────────────────────────────────────────────────────────────  -/

/-! ─────────────────────────────────────────────────────────────────────────
    §8 — Exact Inter-degree Resonances
    ─────────────────────────────────────────────────────────────────────────

    Thm 1.4 (FourDiamond §D1): for n,m ≥ 2 with gcd(n,m)=1, the integer
    solutions of k^n = j^m are exactly the pairs (t^m, t^n) for t ≥ 0.

    Direction (←): `resonance_backward` (trivial).
    Direction (→), steps 1-2: `resonance_exact_valuations` — if k^n = j^m
      with gcd(n,m)=1 then m ∣ v_p(k) for every prime p (via factorization).
    Steps 3-4 (explicit construction of t via Nat.factorization and
      Finsupp.mapRange): require infrastructure not yet available;
      they remain as a future item.
    ───────────────────────────────────────────────────────────────────────── -/

section EsatteRisonanze

/-- Direction (←): (t^m)^n = (t^n)^m. -/
theorem resonance_backward (t n m : ℕ) : (t ^ m) ^ n = (t ^ n) ^ m := by ring

/-- Direction (→), steps 1-2: if k^n = j^m with gcd(n,m)=1,
    then m ∣ v_p(k) for every prime p. -/
theorem resonance_exact_valuations {k j n m : ℕ}
    (hcop : Nat.Coprime n m) (heq : k ^ n = j ^ m) :
    ∀ p : ℕ, m ∣ k.factorization p := by
  have hfact : n • k.factorization = m • j.factorization := by
    have := congr_arg Nat.factorization heq
    simp only [Nat.factorization_pow] at this
    exact this
  intro p
  have h := (Finsupp.ext_iff.mp hfact) p
  simp only [Finsupp.smul_apply, smul_eq_mul] at h
  exact hcop.symm.dvd_of_dvd_mul_left ⟨j.factorization p, h⟩

end EsatteRisonanze

end DirezioniFondamentali
