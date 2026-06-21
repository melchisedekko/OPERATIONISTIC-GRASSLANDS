/-
  GrasslandFiveDirections.lean — CampiOperazionistici
  ===================================================
  The Five Arithmetic Directions for a GENERAL operationistic grassland.

  Paper: §11 (Five Research Directions) — general-grassland generalisation.

  The radical Directions of `fiveDirections.lean` are all proved by transport
  along the chapter isomorphism `toZMod = θ_{k^n}`.  Since
  `OperationisticGrassland.lean` establishes that the affine shift
  `grassToZMod = θ_B` is a ring isomorphism `Grass d ≃+* ZMod d.G` for an
  ARBITRARY base `B` (`Grass.toZModRingEquiv`), the four field-theoretic
  directions generalise verbatim:

    · Direction I  — additive Fermat / order structure
    · Direction II — units count = φ(G)
    · Direction IV — Wilson's law (prime gap)
    · Direction V  — Euler / multiplicative Fermat

  Each statement here, restricted to `radicalGrassland n k hn`, recovers the
  corresponding theorem of `fiveDirections.lean`; it also holds for the modular
  (`B = 0`) and Fibonacci (`B = F_k`) instances.

  Direction III (Radical CRT) is NOT generalised: it couples two distinct
  degrees through the Mersenne gaps `gap(n,1) = 2ⁿ−1`, the cross-degree gcd
  identity, and perfect-power landing — none of which exist for a general
  partition function.  It is genuinely radical and stays in `fiveDirections.lean`.

  This file imports only `OperationisticGrassland` (which re-exports the
  foundation + GroupStructure) and is self-contained: 0 `sorry`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Tactic
import CampiOperazionistici.OperationisticGrassland

open CampiOperazionistici
open BigOperators

namespace GrasslandDirezioni

/-! ─────────────────────────────────────────────────────────────────────────
    §0 — Neutral elements under the shift `θ_B`

    `grassToZMod` is the ring isomorphism `Grass.toZModRingEquiv`, so it sends
    the additive neutral to `0` and the multiplicative neutral to `1`.  These
    are the only facts about the neutrals the five directions need.
    ───────────────────────────────────────────────────────────────────────── -/

/-- The additive neutral maps to `0` under `θ_B` (it is `0` of the ring `Grass d`). -/
lemma grassToZMod_neutral_is_zero (d : GrasslandData) :
    grassToZMod d (grassNeutral d) = 0 :=
  map_zero (Grass.toZModRingEquiv d)

/-- The multiplicative neutral maps to `1` under `θ_B` (it is `1` of `Grass d`). -/
lemma grassToZMod_mulNeutral_is_one (d : GrasslandData) :
    grassToZMod d (grassMulNeutral d) = 1 :=
  map_one (Grass.toZModRingEquiv d)


/-! ─────────────────────────────────────────────────────────────────────────
    §1 — DIRECTION I: Additive order and additive Fermat

    The chapter additive group `(Fin G, ⊕_B)` has order `G`, so `G` iterations
    of `⊕_B` return to the neutral, for every gap `G` (prime or not).
    ───────────────────────────────────────────────────────────────────────── -/

section DirezioneI

variable (d : GrasslandData)

/-- The `m`-fold `grassAdd`-iterate of `r`. -/
def grassAddIter : ℕ → Fin d.G → Fin d.G
  | 0,     _ => grassNeutral d
  | m + 1, r => grassAdd d (grassAddIter m r) r

/-- `θ_B` transports `grassAddIter` to iterated addition in `ZMod G`. -/
lemma grassToZMod_addIter (m : ℕ) (r : Fin d.G) :
    grassToZMod d (grassAddIter d m r) = m • grassToZMod d r := by
  induction m with
  | zero => simp [grassAddIter, grassToZMod_neutral_is_zero]
  | succ m ih =>
      simp only [grassAddIter, succ_nsmul]
      rw [grassToZMod_add, ih]

/-- **Additive Fermat (general grassland)**: `G` iterations return to the
    neutral, for every gap. -/
theorem fermatGrass_additivo (r : Fin d.G) :
    grassAddIter d d.G r = grassNeutral d := by
  apply grassToZMod_injective d
  rw [grassToZMod_addIter, grassToZMod_neutral_is_zero]
  haveI : NeZero d.G := ⟨d.hG.ne'⟩
  simp [nsmul_eq_mul]

/-- The additive order of `θ_B r` in `ZMod G` divides the gap (Lagrange). -/
theorem grass_addOrderOf_dvd_gap (r : Fin d.G) :
    addOrderOf (grassToZMod d r) ∣ d.G := by
  haveI : NeZero d.G := ⟨d.hG.ne'⟩
  have := @addOrderOf_dvd_card (ZMod d.G) _ _ (grassToZMod d r)
  simpa [ZMod.card] using this

/-- If `grassAddIter m r = neutral`, then `addOrderOf (θ_B r) ∣ m`. -/
theorem grass_addOrderOf_dvd_of_addIter (r : Fin d.G) (m : ℕ)
    (hm : grassAddIter d m r = grassNeutral d) :
    addOrderOf (grassToZMod d r) ∣ m := by
  apply addOrderOf_dvd_of_nsmul_eq_zero
  have := congr_arg (grassToZMod d) hm
  rwa [grassToZMod_addIter, grassToZMod_neutral_is_zero] at this

/-- For a prime gap, every `r ≠ neutral` has additive order exactly `G`. -/
theorem grass_addOrderOf_eq_gap_prime [hprime : Fact (Nat.Prime d.G)]
    (r : Fin d.G) (hr : r ≠ grassNeutral d) :
    addOrderOf (grassToZMod d r) = d.G := by
  haveI : NeZero d.G := ⟨hprime.out.pos.ne'⟩
  have hne : grassToZMod d r ≠ 0 := by
    intro h; apply hr
    apply grassToZMod_injective d
    rw [h, grassToZMod_neutral_is_zero]
  have hdvd : addOrderOf (grassToZMod d r) ∣ d.G := grass_addOrderOf_dvd_gap d r
  have hone : addOrderOf (grassToZMod d r) ≠ 1 := by
    intro h
    rw [AddMonoid.addOrderOf_eq_one_iff] at h
    exact hne h
  rcases hprime.out.eq_one_or_self_of_dvd _ hdvd with h1 | hg
  · exact absurd h1 hone
  · exact hg

end DirezioneI


/-! ─────────────────────────────────────────────────────────────────────────
    §2 — DIRECTION II: Units and the totient

    `r` is a unit of `(Fin G, ⊗_B)` iff `gcd(B + r, G) = 1`.  The shift
    `r ↦ (B + r) mod G` is a translation of `{0,…,G−1}`, and coprimality with
    `G` is translation-invariant, so the number of units is `φ(G)`.
    ───────────────────────────────────────────────────────────────────────── -/

section DirezioneII

variable (d : GrasslandData)

/-- `r` is `B`-invertible iff its absolute representative `B + r` is coprime to `G`. -/
def isGrassMulInvertible (r : Fin d.G) : Prop :=
  Nat.Coprime (d.B + r.val) d.G

/-- The set of units of `(Fin G, ⊗_B)`. -/
def grassMulUnits (d : GrasslandData) : Finset (Fin d.G) :=
  Finset.filter (fun r => Nat.Coprime (d.B + r.val) d.G) Finset.univ

/-- The multiplicative neutral is always a unit. -/
theorem grassMulNeutral_isInvertible :
    Nat.Coprime (d.B + (grassMulNeutral d).val) d.G := by
  haveI : NeZero d.G := ⟨d.hG.ne'⟩
  have hmod : (d.B + (grassMulNeutral d).val) % d.G = 1 % d.G := by
    rw [← ZMod.natCast_eq_natCast_iff']
    have h := grassToZMod_mulNeutral_is_one d
    simp only [grassToZMod] at h
    push_cast at h ⊢
    rw [add_comm]
    exact h
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hmod]
  simp

/-- For a prime gap, every non-neutral element is a unit. -/
theorem grass_prime_gap_allInvertible [hprime : Fact (Nat.Prime d.G)]
    (r : Fin d.G) (hr : r ≠ grassNeutral d) :
    Nat.Coprime (d.B + r.val) d.G := by
  have hne : grassToZMod d r ≠ 0 := by
    intro h; apply hr
    apply grassToZMod_injective d
    rw [h, grassToZMod_neutral_is_zero]
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime]
  rw [Nat.Prime.coprime_iff_not_dvd hprime.out]
  intro hdvd
  have hzero : grassToZMod d r = 0 := by
    simp only [grassToZMod]
    rw [← ZMod.natCast_eq_zero_iff] at hdvd
    rw [add_comm]
    convert hdvd using 1
    push_cast; ring
  exact hne hzero

/-- **Totient (general grassland)**: the number of units equals `φ(G)`. -/
theorem grass_phi_eq_totient :
    (grassMulUnits d).card = Nat.totient d.G := by
  set g := d.G with hg_def
  have hg : 0 < g := d.hG
  rw [Nat.totient_eq_card_coprime]
  have hcop_mod : ∀ a : ℕ, Nat.Coprime a g ↔ Nat.Coprime (a % g) g := fun a => by
    simp only [Nat.Coprime, (Nat.gcd_comm a g).trans (Nat.gcd_rec g a)]
  have hadd_mod : ∀ x, (d.B + x) % g = (d.B % g + x) % g := fun x => by
    conv_lhs => rw [show d.B + x = d.B % g + x + g * (d.B / g) from by
      have := Nat.div_add_mod d.B g; omega]
    rw [Nat.add_mul_mod_self_left]
  set m := d.B % g with hm_def
  have hm : m < g := Nat.mod_lt _ hg
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
  apply Finset.card_nbij' (fun r => (d.B + r.val) % g)
      (fun a => ⟨(a + g - m) % g, Nat.mod_lt _ hg⟩)
  · intro r hr
    have hr' : Nat.Coprime (d.B + r.val) g := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hg),
      Nat.coprime_comm.mp ((hcop_mod _).mp hr')⟩
  · intro a ha
    have ha_mem : a < g := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have ha_cop : g.Coprime a := (Finset.mem_filter.mp ha).2
    have hkey : (d.B + (a + g - m) % g) % g = a := by
      rw [hadd_mod]; exact hkey_aux a ha_mem
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hcop_mod, hkey]; exact Nat.coprime_comm.mp ha_cop⟩
  · intro r _
    apply Fin.ext
    simp only []
    have h1 : r.val < g := r.isLt
    have heq : (d.B + r.val) % g = (m + r.val) % g := hadd_mod r.val
    rw [heq, hm_def]
    rcases Nat.lt_or_ge (m + r.val) g with h | h
    · have hq : (m + r.val) % g = m + r.val := Nat.mod_eq_of_lt h
      rw [hq, show m + r.val + g - m = r.val + g from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt h1]
    · have hlt2g : m + r.val < 2 * g := by omega
      have hq : (m + r.val) % g = m + r.val - g := by
        conv_lhs => rw [show m + r.val = g + (m + r.val - g) from by omega]
        simp [Nat.add_mod_left, Nat.mod_eq_of_lt (show m + r.val - g < g by omega)]
      rw [hq, show m + r.val - g + g - m = r.val from by omega, Nat.mod_eq_of_lt h1]
  · intro a ha
    have ha_mem : a < g := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    show (d.B + (a + g - m) % g) % g = a
    rw [hadd_mod]; exact hkey_aux a ha_mem

end DirezioneII


/-! ─────────────────────────────────────────────────────────────────────────
    §3 — DIRECTION IV: Wilson's law

    For a prime gap, the product over `Fin G \ {neutral, mulNeutral}` of the
    images under `θ_B` is `-1`.  As in the radical case the additive neutral —
    which equals the absorber `α` with `B + α ≡ 0` — must be excluded alongside
    the multiplicative neutral, since it maps to `0`.
    ───────────────────────────────────────────────────────────────────────── -/

section DirezioneIV

variable (d : GrasslandData)

/-- The absorber `α ∈ Fin G` with `B + α ≡ 0 (mod G)`. -/
def grassAbsorb : Fin d.G :=
  ⟨(d.G - d.B % d.G) % d.G, Nat.mod_lt _ d.hG⟩

/-- The absorber maps to `0` under `θ_B`. -/
theorem grassToZMod_absorb_is_zero :
    grassToZMod d (grassAbsorb d) = 0 := by
  simp only [grassToZMod, grassAbsorb]
  have hg := d.hG
  haveI : NeZero d.G := ⟨hg.ne'⟩
  rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  set m := d.B % d.G
  have hm_lt : m < d.G := Nat.mod_lt _ hg
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · simp [hm0, Nat.mod_self]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  · have hval : (d.G - m) % d.G = d.G - m := by
      apply Nat.mod_eq_of_lt; omega
    rw [hval]
    have hkn : d.B = m + d.G * (d.B / d.G) := by
      have := Nat.mod_add_div d.B d.G; omega
    refine ⟨d.B / d.G + 1, ?_⟩
    have hle : m ≤ d.G := Nat.le_of_lt hm_lt
    zify [hle]
    linarith [hkn]

/-- The additive neutral and the absorber coincide. -/
theorem grassNeutral_eq_grassAbsorb :
    grassNeutral d = grassAbsorb d := by
  apply Fin.ext
  simp [grassNeutral, grassAbsorb]

/-- The elements excluded from the Wilson product: `{neutral, mulNeutral}`. -/
def grassWilsonExcluded (d : GrasslandData) : Finset (Fin d.G) :=
  {grassNeutral d, grassMulNeutral d}

/-- The elements included in the Wilson product. -/
def grassWilsonFactors (d : GrasslandData) : Finset (Fin d.G) :=
  Finset.univ \ grassWilsonExcluded d

/-- Product of all `z ≠ 0, 1` in `ZMod p` (prime) equals `-1`. -/
private lemma prod_filter_ne_zero_ne_one_eq_neg_one (p : ℕ) [hp : Fact p.Prime]
    [hpn : NeZero p] :
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

/-- **Wilson's law (general grassland)**: for a prime gap, the product of the
    Wilson factors under `θ_B` is `-1`. -/
theorem grassWilson [hprime : Fact (Nat.Prime d.G)] :
    ∏ r ∈ grassWilsonFactors d, grassToZMod d r = -1 := by
  set g := d.G
  haveI hgne : NeZero g := ⟨hprime.out.pos.ne'⟩
  have hprod_eq : ∏ r ∈ grassWilsonFactors d, grassToZMod d r =
      ∏ z ∈ (Finset.univ : Finset (ZMod g)).filter (fun z => z ≠ 0 ∧ z ≠ 1), z := by
    apply Finset.prod_nbij (grassToZMod d)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [grassWilsonFactors, grassWilsonExcluded, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, Finset.mem_singleton, not_or, true_and] at hr
      exact ⟨fun h => hr.1 (grassToZMod_injective d _ _
                  (h.trans (grassToZMod_neutral_is_zero d).symm)),
             fun h => hr.2 (grassToZMod_injective d _ _
                  (h.trans (grassToZMod_mulNeutral_is_one d).symm))⟩
    · intro r1 _ r2 _ h
      exact grassToZMod_injective d _ _ h
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      obtain ⟨r, hr⟩ := grassToZMod_surjective d z
      refine ⟨r, ?_, hr⟩
      rw [Finset.mem_coe, grassWilsonFactors, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [grassWilsonExcluded, Finset.mem_insert, Finset.mem_singleton]
      rintro (heq | heq)
      · exact hz'.1 (show z = 0 by rw [← hr, heq]; exact grassToZMod_neutral_is_zero d)
      · exact hz'.2 (show z = 1 by rw [← hr, heq]; exact grassToZMod_mulNeutral_is_one d)
    · intro r _; rfl
  rw [hprod_eq]
  exact prod_filter_ne_zero_ne_one_eq_neg_one g

end DirezioneIV


/-! ─────────────────────────────────────────────────────────────────────────
    §4 — DIRECTION V: Euler / multiplicative Fermat

    For a unit `r`, the `φ(G)`-th `⊗_B`-power is the multiplicative neutral;
    for a prime gap the exponent becomes `G − 1` for every non-neutral element.
    ───────────────────────────────────────────────────────────────────────── -/

section DirezioneV

variable (d : GrasslandData)

/-- The `m`-fold `grassMul`-power of `r`. -/
def grassMulPow : ℕ → Fin d.G → Fin d.G
  | 0,     _ => grassMulNeutral d
  | m + 1, r => grassMul d (grassMulPow m r) r

/-- `θ_B` transports `grassMulPow` to powers in `ZMod G`. -/
lemma grassToZMod_mulPow (m : ℕ) (r : Fin d.G) :
    grassToZMod d (grassMulPow d m r) = grassToZMod d r ^ m := by
  induction m with
  | zero => simp [grassMulPow, grassToZMod_mulNeutral_is_one]
  | succ m ih =>
      simp only [grassMulPow, pow_succ]
      rw [grassToZMod_mul, ih]

/-- **Euler (general grassland)**: a unit raised to `φ(G)` returns to the
    multiplicative neutral. -/
theorem eulerGrass (r : Fin d.G)
    (hinv : Nat.Coprime (d.B + r.val) d.G) :
    grassMulPow d (Nat.totient d.G) r = grassMulNeutral d := by
  haveI : NeZero d.G := ⟨d.hG.ne'⟩
  apply grassToZMod_injective d
  rw [grassToZMod_mulPow, grassToZMod_mulNeutral_is_one]
  have hunit : IsUnit (grassToZMod d r) := by
    rw [show grassToZMod d r = ((d.B + r.val : ℕ) : ZMod d.G) from by
      simp only [grassToZMod]; push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    exact hinv
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]

/-- **Multiplicative Fermat (general grassland)**: for a prime gap, every
    non-neutral element raised to `G − 1` returns to the multiplicative neutral. -/
theorem fermatGrass_moltiplicativo [hprime : Fact (Nat.Prime d.G)]
    (r : Fin d.G) (hr : r ≠ grassNeutral d) :
    grassMulPow d (d.G - 1) r = grassMulNeutral d := by
  apply grassToZMod_injective d
  rw [grassToZMod_mulPow, grassToZMod_mulNeutral_is_one]
  have hne : grassToZMod d r ≠ 0 := by
    intro h; apply hr
    apply grassToZMod_injective d
    rw [h, grassToZMod_neutral_is_zero]
  haveI : NeZero d.G := ⟨hprime.out.pos.ne'⟩
  exact ZMod.pow_card_sub_one_eq_one hne

end DirezioneV


/-! ─────────────────────────────────────────────────────────────────────────
    §5 — The radical Five Directions are special cases (`B = k^n`)

    Each generalised theorem, instantiated at `radicalGrassland n k hn`,
    recovers the corresponding radical result of `fiveDirections.lean`; it is
    equally an instance for the modular (`B = 0`) and Fibonacci instances.
    ───────────────────────────────────────────────────────────────────────── -/

-- Direction I, radical instance.
example (n k : ℕ) (hn : n ≠ 0) (r : Fin (radicalGrassland n k hn).G) :
    grassAddIter (radicalGrassland n k hn) (radicalGrassland n k hn).G r
      = grassNeutral (radicalGrassland n k hn) :=
  fermatGrass_additivo (radicalGrassland n k hn) r

-- Direction II, radical instance.
example (n k : ℕ) (hn : n ≠ 0) :
    (grassMulUnits (radicalGrassland n k hn)).card
      = Nat.totient (radicalGrassland n k hn).G :=
  grass_phi_eq_totient (radicalGrassland n k hn)

-- Direction IV, modular instance (Wilson on a prime modulus).
example (p : ℕ) (hp : 0 < p) [Fact (Nat.Prime (modularGrassland p hp).G)] :
    ∏ r ∈ grassWilsonFactors (modularGrassland p hp),
        grassToZMod (modularGrassland p hp) r = -1 :=
  grassWilson (modularGrassland p hp)

-- Direction V, radical instance.
example (n k : ℕ) (hn : n ≠ 0) (r : Fin (radicalGrassland n k hn).G)
    (hinv : Nat.Coprime ((radicalGrassland n k hn).B + r.val)
                        (radicalGrassland n k hn).G) :
    grassMulPow (radicalGrassland n k hn)
        (Nat.totient (radicalGrassland n k hn).G) r
      = grassMulNeutral (radicalGrassland n k hn) :=
  eulerGrass (radicalGrassland n k hn) r hinv

end GrasslandDirezioni
