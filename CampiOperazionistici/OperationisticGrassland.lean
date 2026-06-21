/-
  OperationisticGrassland.lean — CampiOperazionistici
  Author: Alessandro Sgarbi — 2026-03-16
  Paper: §2 (Operationistic Grasslands: The General Framework)

  This file defines the general structure of an *Operationistic Grassland*,
  of which:
    • classical modular arithmetic  ℤ/mℤ  is the "flat" instance (B = 0)
    • the chapter radical structure  Aod_n  is the "curved" instance (B = k^n)

  The goal is to provide the unified mathematical foundation that justifies the
  name "Operationistic Field": when G is prime, every grassland is a Galois field.

  Scope:
    - the additive structure (abelian group) — §3–§4
    - the full commutative-ring / Galois-field structure for every grassland
      via the affine shift θ_B(r) = (r + B) mod G — §4b–§4f.  This makes
      precise that the per-chapter ring/field is not radical-specific: it is a
      universal feature of any partition function, proved here once for an
      arbitrary base B (the radical case b = k^n being the instance used in the
      remainder of the paper).
    - the canonical instances (modular, radical, Fibonacci)
    - no refactoring of existing files
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import CampiOperazionistici.CampiOperazionistici
import CampiOperazionistici.GroupStructure

namespace CampiOperazionistici

/-! ## 1. General structure: GrasslandData

  An *Operationistic Grassland* is determined by two natural parameters:
    • G : the chapter size (the modulus of the arithmetic)
    • B : the chapter base (the characteristic translation)

  The common operational scheme is:
      r ⊕ s  :=  (B + r + s) mod G

  For B = 0 one recovers classical modular arithmetic.
  For B = k^n one recovers the radical structure of chapter k of degree n.
-/

structure GrasslandData where
  /-- Chapter size: the modulus of the operation -/
  G : ℕ
  /-- Chapter base: the characteristic translation -/
  B : ℕ
  /-- Positivity required for the modular reduction -/
  hG : 0 < G

/-! ## 2. Canonical operation -/

/-- Operationistic addition on a grassland:
    r ⊕ s := (B + r + s) mod G -/
def grassAdd (d : GrasslandData) :
    Fin d.G → Fin d.G → Fin d.G :=
  fun r s => ⟨(d.B + r.val + s.val) % d.G,
              Nat.mod_lt _ d.hG⟩

/-- The additive identity: the unique e ∈ Fin G such that B + e ≡ 0 (mod G) -/
def grassNeutral (d : GrasslandData) : Fin d.G :=
  ⟨(d.G - d.B % d.G) % d.G, Nat.mod_lt _ d.hG⟩

/-- The additive inverse of r:
    s such that (B + r + s) ≡ (G - B%G) (mod G), i.e. s ≡ -2B - r (mod G) -/
def grassInv (d : GrasslandData) (r : Fin d.G) : Fin d.G :=
  ⟨(2 * d.G - (2 * d.B + r.val) % d.G) % d.G, Nat.mod_lt _ d.hG⟩

/-! ## 3. Group properties — valid for every GrasslandData -/

/-- Technical lemma: translating the base by the identity vanishes mod G -/
private lemma grassland_neutral_shift (d : GrasslandData) :
    (d.B + (d.G - d.B % d.G) % d.G) % d.G = 0 := by
  set G := d.G
  set B := d.B
  have hG : 0 < G := d.hG
  have hm : B % G < G := Nat.mod_lt _ hG
  rcases Nat.eq_zero_or_pos (B % G) with h | h
  · have hBeq : B = G * (B / G) := by
      have := Nat.div_add_mod B G; rw [h] at this; linarith
    rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero, hBeq]
    exact Nat.mul_mod_right G _
  · have hlt : G - B % G < G := Nat.sub_lt hG h
    rw [Nat.mod_eq_of_lt hlt]
    have heq : B + (G - B % G) = G * (B / G + 1) := by
      have := Nat.sub_add_cancel (Nat.le_of_lt hm)
      have hdiv := Nat.div_add_mod B G
      linarith
    rw [heq, Nat.mul_mod_right]

/-- The identity is a left identity -/
theorem grassNeutral_left (d : GrasslandData) (r : Fin d.G) :
    grassAdd d (grassNeutral d) r = r := by
  simp only [grassAdd, grassNeutral, Fin.ext_iff, Fin.val_mk]
  have h0 := grassland_neutral_shift d
  have hr := r.isLt
  rw [show d.B + (d.G - d.B % d.G) % d.G + r.val =
        (d.B + (d.G - d.B % d.G) % d.G) + r.val by ring,
      Nat.add_mod, h0, Nat.zero_add,
      Nat.mod_mod_of_dvd _ (dvd_refl _),
      Nat.mod_eq_of_lt hr]

/-- The identity is a right identity -/
theorem grassNeutral_right (d : GrasslandData) (r : Fin d.G) :
    grassAdd d r (grassNeutral d) = r := by
  simp only [grassAdd, grassNeutral, Fin.ext_iff, Fin.val_mk]
  have h0 := grassland_neutral_shift d
  have hr := r.isLt
  rw [show d.B + r.val + (d.G - d.B % d.G) % d.G =
        (d.B + (d.G - d.B % d.G) % d.G) + r.val by ring,
      Nat.add_mod, h0, Nat.zero_add,
      Nat.mod_mod_of_dvd _ (dvd_refl _),
      Nat.mod_eq_of_lt hr]

/-- Commutativity -/
theorem grassAdd_comm (d : GrasslandData) (r s : Fin d.G) :
    grassAdd d r s = grassAdd d s r := by
  simp only [grassAdd, Fin.ext_iff]
  congr 1; ring

/-- Associativity -/
private lemma mod_add_mid (a b c G : ℕ) :
    (a + b % G + c) % G = (a + b + c) % G := by
  rw [Nat.add_mod (a + b % G) c, Nat.add_mod a (b % G),
      Nat.mod_mod_of_dvd _ (dvd_refl G),
      ← Nat.add_mod a b, ← Nat.add_mod (a + b) c]

theorem grassAdd_assoc (d : GrasslandData) (r s t : Fin d.G) :
    grassAdd d (grassAdd d r s) t =
    grassAdd d r (grassAdd d s t) := by
  apply Fin.ext
  simp only [grassAdd, Fin.val_mk]
  have lhs : (d.B + (d.B + r.val + s.val) % d.G + t.val) % d.G =
             (2 * d.B + r.val + s.val + t.val) % d.G := by
    rw [mod_add_mid]; congr 1; ring
  have rhs : (d.B + r.val + (d.B + s.val + t.val) % d.G) % d.G =
             (2 * d.B + r.val + s.val + t.val) % d.G := by
    rw [show d.B + r.val + (d.B + s.val + t.val) % d.G =
            r.val + (d.B + s.val + t.val) % d.G + d.B by ring,
        mod_add_mid]; congr 1; ring
  rw [lhs, ← rhs]

-- (B + rv + (2g - (2B+rv)%g)%g) % g = (g - B%g) % g
private lemma grass_inv_sum_mod (g B rv : ℕ) (hg : 0 < g) :
    (B + rv + (2 * g - (2 * B + rv) % g) % g) % g = (g - B % g) % g := by
  -- Both sides equal (g - B % g) % g. Show via Nat.ModEq.
  -- Let m := (2*B+rv) % g.  Then (2g - m) % g = (g - m) % g ≡ -m ≡ -(2B+rv) mod g.
  -- So B+rv + (2g-m)%g ≡ B+rv - (2B+rv) = -(B) ≡ g - B%g mod g. ✓
  set m₁ := B % g
  set m₂ := (2 * B + rv) % g
  have hm₁ : m₁ < g := Nat.mod_lt _ hg
  have hm₂ : m₂ < g := Nat.mod_lt _ hg
  -- Reduce (2g - m₂) % g to (g - m₂) % g
  have step1 : (2 * g - m₂) % g = (g - m₂) % g := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · simp [h, Nat.mod_self]
    · have hlt : g - m₂ < g := Nat.sub_lt hg h
      rw [show 2 * g - m₂ = g + (g - m₂) from by omega,
          Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hlt,
          Nat.mod_eq_of_lt hlt]
  rw [step1]
  -- Now show (B + rv + (g - m₂) % g) % g = (g - m₁) % g
  -- Key arithmetic: (B + rv + (g - m₂)) % g = (g - m₁) % g
  -- because B + rv + g - m₂ ≡ B + rv - m₂ = B + rv - (2B+rv)%g
  -- and B + rv ≡ m₂ - m₁ + g*k for some k... use Nat.add_mod chain.
  -- Reduce via: (B+rv+(g-m₂)%g) % g = (B+rv+g-m₂) % g [when m₂>0, using mod_eq_of_lt]
  --           = (B%g + rv%g + g - m₂%g) % g ... messy.
  -- Cleaner: use that B+rv ≡ m₂ - m₁ (mod g) [since 2B+rv ≡ m₂ and B ≡ m₁]
  -- so B+rv+(g-m₂)%g ≡ m₂-m₁+g-m₂ = g-m₁ (mod g). ✓
  -- Formal: Nat.ModEq g
  suffices h : (B + rv + (g - m₂) % g) % g = (g - m₁) % g by exact h
  have hcong_B : B % g = m₁ := rfl
  have hcong_BR : (2 * B + rv) % g = m₂ := rfl
  -- (B + rv) % g = (m₂ - m₁ + g) % g  [since 2B+rv ≡ B + (B+rv), so B+rv ≡ m₂ - B ≡ m₂ - m₁]
  have hBrv : (B + rv) % g = (m₂ + g - m₁) % g := by
    -- We show ((B+rv)%g + m₁) % g = m₂, then case-split.
    -- Route: ((B+rv)%g + B%g)%g = (B+rv+B)%g by ← Nat.add_mod, and B+rv+B = 2B+rv.
    have h2 : ((B + rv) % g + m₁) % g = m₂ := by
      show ((B + rv) % g + B % g) % g = (2 * B + rv) % g
      rw [← Nat.add_mod (B + rv) B]
      congr 1; omega
    have hlt_Brv : (B + rv) % g < g := Nat.mod_lt _ hg
    rcases Nat.lt_or_ge ((B + rv) % g + m₁) g with hlt | hge
    · -- (B+rv)%g + m₁ < g, so h2 gives: (B+rv)%g + m₁ = m₂
      rw [Nat.mod_eq_of_lt hlt] at h2
      -- (B+rv)%g = m₂ - m₁; RHS = (m₂+g-m₁)%g = (g + (m₂-m₁))%g = (m₂-m₁)%g
      have heq : (B + rv) % g = m₂ - m₁ := by omega
      have hrhs : (m₂ + g - m₁) % g = m₂ - m₁ := by
        have : m₂ - m₁ < g := by omega
        rw [show m₂ + g - m₁ = g + (m₂ - m₁) from by omega,
            Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt this,
            Nat.mod_eq_of_lt this]
      rw [heq, hrhs]
    · -- (B+rv)%g + m₁ ≥ g, so h2 gives: (B+rv)%g + m₁ - g = m₂
      have hlt2 : (B + rv) % g + m₁ - g < g := by omega
      rw [show (B + rv) % g + m₁ = (B + rv) % g + m₁ - g + g from by omega,
          Nat.add_mod, Nat.mod_self, Nat.add_zero,
          Nat.mod_eq_of_lt hlt2] at h2
      -- h2 : ((B+rv)%g + m₁ - g) % g = m₂, and (B+rv)%g + m₁ - g < g
      -- so (B+rv)%g + m₁ - g = m₂, hence (B+rv)%g = m₂ + g - m₁
      rw [Nat.mod_eq_of_lt hlt2] at h2
      -- now h2 : (B+rv)%g + m₁ - g = m₂
      have heq : (B + rv) % g = m₂ + g - m₁ := by
        have hge' : g ≤ (B + rv) % g + m₁ := hge
        omega
      have hbound : m₂ + g - m₁ < g := by omega
      rw [heq, Nat.mod_eq_of_lt hbound]
  rw [Nat.add_mod, hBrv, ← Nat.add_mod]
  rcases Nat.eq_zero_or_pos m₂ with h | h
  · -- m₂ = 0; goal: (m₂ + g - m₁ + (g - m₂) % g) % g = (g - m₁) % g
    simp only [h, Nat.zero_add, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
  · rw [Nat.mod_eq_of_lt (Nat.sub_lt hg h)]
    rw [show m₂ + g - m₁ + (g - m₂) = 2 * g - m₁ from by omega]
    rcases Nat.eq_zero_or_pos m₁ with h1 | h1
    · simp [h1, Nat.mod_self]
    · rw [show 2 * g - m₁ = g + (g - m₁) from by omega,
          Nat.add_mod, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (Nat.sub_lt hg h1),
          Nat.mod_eq_of_lt (Nat.sub_lt hg h1)]

/-- Right inverse -/
theorem grassInv_right (d : GrasslandData) (r : Fin d.G) :
    grassAdd d r (grassInv d r) = grassNeutral d := by
  apply Fin.ext
  simp only [grassAdd, grassInv, grassNeutral, Fin.val_mk]
  exact grass_inv_sum_mod d.G d.B r.val d.hG

/-! ## 4. General group theorem

  Every GrasslandData defines an abelian group on Fin G.
  This is the result that mathematically justifies the name
  "Operationistic Field" (for the additive structure).
-/

/-- **Main theorem**: every Operationistic Grassland is an abelian group.

  Formally: (Fin G, grassAdd d) satisfies all the abelian group axioms,
  with identity grassNeutral d and inverse grassInv d. -/
theorem grassland_isAbelianGroup (d : GrasslandData) :
    let e := grassNeutral d
    (∀ r,   grassAdd d e r = r) ∧
    (∀ r,   grassAdd d r e = r) ∧
    (∀ r s, grassAdd d r s = grassAdd d s r) ∧
    (∀ r s t, grassAdd d (grassAdd d r s) t =
              grassAdd d r (grassAdd d s t)) ∧
    (∀ r,   grassAdd d r (grassInv d r) = e) :=
  ⟨grassNeutral_left d,
   grassNeutral_right d,
   grassAdd_comm d,
   grassAdd_assoc d,
   grassInv_right d⟩

/-- Left inverse, by commutativity. -/
theorem grassInv_left (d : GrasslandData) (r : Fin d.G) :
    grassAdd d (grassInv d r) r = grassNeutral d := by
  rw [grassAdd_comm]; exact grassInv_right d r

/-! ## 4b. General multiplication

  The multiplicative companion of `grassAdd`, following the same
  lift–multiply–subtract–reduce schema:
      r ⊗ s := ((B + r)·(B + s) − B) mod G.
  As with addition, the base `B` is arbitrary; nothing here uses that `B`
  is a perfect power. -/

/-- Operationistic multiplication on a grassland. -/
def grassMul (d : GrasslandData) :
    Fin d.G → Fin d.G → Fin d.G :=
  fun r s => ⟨((d.B + r.val) * (d.B + s.val) - d.B) % d.G,
              Nat.mod_lt _ d.hG⟩

/-- The multiplicative identity: the local address `e` with `B + e ≡ 1 (mod G)`. -/
def grassMulNeutral (d : GrasslandData) : Fin d.G :=
  ⟨(d.G + 1 - d.B % d.G) % d.G, Nat.mod_lt _ d.hG⟩

/-! ## 4c. The affine shift θ_B and its homomorphism property

  `grassToZMod d r = (r + B) mod G` is the affine shift `θ_B`.  It is
  simultaneously additive and multiplicative; this is the entire content of
  the general ring isomorphism, and it is independent of the base. -/

/-- The affine shift `θ_B : Fin G → ℤ/Gℤ`,  `θ_B(r) = (r + B) mod G`. -/
def grassToZMod (d : GrasslandData) (r : Fin d.G) : ZMod d.G :=
  (r.val : ZMod d.G) + (d.B : ℕ)

private lemma grassNatCastMod (a g : ℕ) : (a % g : ZMod g) = (a : ZMod g) := by
  conv_rhs => rw [← Nat.div_add_mod a g]
  push_cast; simp [mul_comm]

theorem grassToZMod_add (d : GrasslandData) (r s : Fin d.G) :
    grassToZMod d (grassAdd d r s) = grassToZMod d r + grassToZMod d s := by
  simp only [grassToZMod, grassAdd]; rw [grassNatCastMod]; push_cast; ring

-- The absolute product is ≥ B, so the ℕ-subtraction in `grassMul` is exact.
-- This is the only side condition, and it holds for every base B ≥ 0.
private lemma grass_abs_ge (d : GrasslandData) (r s : Fin d.G) :
    d.B ≤ (d.B + r.val) * (d.B + s.val) := by
  have h := Nat.zero_le (d.B * s.val + d.B * r.val + r.val * s.val + d.B * d.B)
  nlinarith [Nat.le_add_right d.B r.val]

theorem grassToZMod_mul (d : GrasslandData) (r s : Fin d.G) :
    grassToZMod d (grassMul d r s) = grassToZMod d r * grassToZMod d s := by
  simp only [grassToZMod, grassMul]
  rw [grassNatCastMod, Nat.cast_sub (grass_abs_ge d r s)]
  push_cast; ring

theorem grassToZMod_injective (d : GrasslandData) (r s : Fin d.G)
    (h : grassToZMod d r = grassToZMod d s) : r = s := by
  apply Fin.ext
  simp only [grassToZMod] at h
  have heq : (r.val : ZMod d.G) = s.val := add_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff] at heq
  simp only [Nat.ModEq, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] at heq
  exact heq

private lemma grassToZMod_zero (d : GrasslandData) :
    grassToZMod d (grassNeutral d) = 0 := by
  have hg : 0 < d.G := d.hG
  have hm : d.B % d.G < d.G := Nat.mod_lt _ hg
  simp only [grassToZMod, grassNeutral, grassNatCastMod]
  rw [Nat.cast_sub (by omega : d.B % d.G ≤ d.G), ZMod.natCast_self, grassNatCastMod]
  ring

private lemma grassToZMod_mulNeutral (d : GrasslandData) :
    grassToZMod d (grassMulNeutral d) = 1 := by
  have hg : 0 < d.G := d.hG
  have hm : d.B % d.G < d.G := Nat.mod_lt _ hg
  simp only [grassToZMod, grassMulNeutral, grassNatCastMod]
  rw [Nat.cast_sub (by omega : d.B % d.G ≤ d.G + 1),
      Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add, grassNatCastMod]
  ring

/-! ## 4d. Bijectivity of θ_B via an explicit inverse -/

/-- Explicit inverse of `grassToZMod`: `θ_B⁻¹(z) = (z.val + G − B mod G) mod G`. -/
def grassFromZMod (d : GrasslandData) (z : ZMod d.G) : Fin d.G :=
  ⟨(ZMod.val z + d.G - d.B % d.G) % d.G, Nat.mod_lt _ d.hG⟩

private lemma grassToZMod_fromZMod (d : GrasslandData) (z : ZMod d.G) :
    grassToZMod d (grassFromZMod d z) = z := by
  have hg : 0 < d.G := d.hG
  have hm : d.B % d.G < d.G := Nat.mod_lt _ hg
  haveI : NeZero d.G := ⟨by omega⟩
  simp only [grassToZMod, grassFromZMod, grassNatCastMod]
  rw [Nat.cast_sub (by omega : d.B % d.G ≤ ZMod.val z + d.G),
      Nat.cast_add, ZMod.natCast_self, add_zero, grassNatCastMod, ZMod.natCast_val]
  simp [sub_add_cancel]

private lemma grassFromZMod_toZMod (d : GrasslandData) (r : Fin d.G) :
    grassFromZMod d (grassToZMod d r) = r :=
  grassToZMod_injective d _ _ (grassToZMod_fromZMod d (grassToZMod d r))

theorem grassToZMod_surjective (d : GrasslandData) :
    Function.Surjective (grassToZMod d) :=
  fun z => ⟨grassFromZMod d z, grassToZMod_fromZMod d z⟩

theorem grassToZMod_bijective (d : GrasslandData) :
    Function.Bijective (grassToZMod d) :=
  ⟨grassToZMod_injective d, grassToZMod_surjective d⟩

/-! ## 4e. Ring laws on the operations (transported through θ_B) -/

theorem grassMul_comm (d : GrasslandData) (r s : Fin d.G) :
    grassMul d r s = grassMul d s r := by
  apply Fin.ext; simp only [grassMul]; congr 1; rw [mul_comm]

theorem grassMul_assoc (d : GrasslandData) (r s t : Fin d.G) :
    grassMul d (grassMul d r s) t = grassMul d r (grassMul d s t) := by
  apply grassToZMod_injective d
  simp only [grassToZMod_mul]; ring

theorem grassMul_neutral_left (d : GrasslandData) (r : Fin d.G) :
    grassMul d (grassMulNeutral d) r = r := by
  apply grassToZMod_injective d
  rw [grassToZMod_mul, grassToZMod_mulNeutral, one_mul]

theorem grassMul_distrib_left (d : GrasslandData) (r s t : Fin d.G) :
    grassMul d r (grassAdd d s t) =
    grassAdd d (grassMul d r s) (grassMul d r t) := by
  apply grassToZMod_injective d
  simp only [grassToZMod_mul, grassToZMod_add]; ring

/-! ## 4f. The carrier `Grass d`, ring and field structure

  As in `GroupStructure.lean`, the global `Fin.instAdd`/`Fin.instMul`
  instances conflict with the chapter operations, so we wrap `Fin d.G` in a
  dedicated structure `Grass d` carrying the grassland operations.  On it,
  `grassToZModRingEquiv` is a ring isomorphism `Grass d ≅ ℤ/Gℤ` for every
  grassland, and `Grass d` is a Galois field whenever `G` is prime. -/

-- nsmul/zsmul scaffolding, mirroring `capAddCommGroup`.
private def grassNsmul (d : GrasslandData) : ℕ → Fin d.G → Fin d.G
  | 0,     _ => grassNeutral d
  | m + 1, a => grassAdd d (grassNsmul d m a) a

def grassAddCommGroup (d : GrasslandData) : AddCommGroup (Fin d.G) where
  add a b         := grassAdd d a b
  zero            := grassNeutral d
  neg a           := grassInv d a
  sub a b         := grassAdd d a (grassInv d b)
  add_assoc       := grassAdd_assoc d
  zero_add        := grassNeutral_left d
  add_zero        := grassNeutral_right d
  neg_add_cancel  := grassInv_left d
  add_comm        := grassAdd_comm d
  sub_eq_add_neg  := fun _ _ => rfl
  nsmul m a       := grassNsmul d m a
  nsmul_zero _    := rfl
  nsmul_succ _ _  := rfl
  zsmul z a       := match z with
    | .ofNat m    => grassNsmul d m a
    | .negSucc m  => grassInv d (grassNsmul d (m + 1) a)
  zsmul_zero' _   := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _  := rfl

/-- Carrier type of the grassland ring: a wrapper around `Fin d.G` free of the
    global `Fin` algebraic instances. -/
structure Grass (d : GrasslandData) where
  toFin : Fin d.G

namespace Grass

variable {d : GrasslandData}

theorem ext {a b : Grass d} (h : a.toFin = b.toFin) : a = b := by
  cases a; cases b; simp_all

instance instAdd : Add (Grass d) := ⟨fun a b => ⟨grassAdd d a.toFin b.toFin⟩⟩
instance instMul : Mul (Grass d) := ⟨fun a b => ⟨grassMul d a.toFin b.toFin⟩⟩
instance instZero : Zero (Grass d) := ⟨⟨grassNeutral d⟩⟩
instance instOne : One (Grass d) := ⟨⟨grassMulNeutral d⟩⟩
instance instNeg : Neg (Grass d) := ⟨fun a => ⟨grassInv d a.toFin⟩⟩

@[simp] lemma add_toFin (a b : Grass d) :
    (a + b).toFin = grassAdd d a.toFin b.toFin := rfl
@[simp] lemma mul_toFin (a b : Grass d) :
    (a * b).toFin = grassMul d a.toFin b.toFin := rfl
@[simp] lemma zero_toFin : (0 : Grass d).toFin = grassNeutral d := rfl
@[simp] lemma one_toFin : (1 : Grass d).toFin = grassMulNeutral d := rfl
@[simp] lemma neg_toFin (a : Grass d) :
    (-a).toFin = grassInv d a.toFin := rfl

instance instAddCommGroup : AddCommGroup (Grass d) where
  add_assoc a b c  := ext (grassAdd_assoc d a.toFin b.toFin c.toFin)
  zero_add a       := ext (grassNeutral_left d a.toFin)
  add_zero a       := ext (grassNeutral_right d a.toFin)
  neg_add_cancel a := ext (grassInv_left d a.toFin)
  add_comm a b     := ext (grassAdd_comm d a.toFin b.toFin)
  nsmul m a        := ⟨(grassAddCommGroup d).nsmul m a.toFin⟩
  nsmul_zero a     := by apply ext; exact (grassAddCommGroup d).nsmul_zero a.toFin
  nsmul_succ m a   := by apply ext; exact (grassAddCommGroup d).nsmul_succ m a.toFin
  zsmul z a        := ⟨(grassAddCommGroup d).zsmul z a.toFin⟩
  zsmul_zero' a    := by apply ext; exact (grassAddCommGroup d).zsmul_zero' a.toFin
  zsmul_succ' m a  := by apply ext; exact (grassAddCommGroup d).zsmul_succ' m a.toFin
  zsmul_neg' m a   := by apply ext; exact (grassAddCommGroup d).zsmul_neg' m a.toFin

private lemma grassMul_one_right (a : Grass d) :
    grassMul d a.toFin (grassMulNeutral d) = a.toFin := by
  rw [grassMul_comm]; exact grassMul_neutral_left d a.toFin

instance instCommRing : CommRing (Grass d) where
  mul_assoc a b c     := ext (grassMul_assoc d a.toFin b.toFin c.toFin)
  one_mul a           := ext (grassMul_neutral_left d a.toFin)
  mul_one a           := ext (grassMul_one_right a)
  left_distrib a b c  := ext (grassMul_distrib_left d a.toFin b.toFin c.toFin)
  right_distrib a b c := by
    apply ext
    simp only [add_toFin, mul_toFin]
    rw [grassMul_comm d (grassAdd d a.toFin b.toFin) c.toFin,
        grassMul_distrib_left d c.toFin a.toFin b.toFin,
        grassMul_comm d c.toFin a.toFin, grassMul_comm d c.toFin b.toFin]
  mul_comm a b        := ext (grassMul_comm d a.toFin b.toFin)
  zero_mul a          := by
    apply ext; simp only [mul_toFin, zero_toFin]
    apply grassToZMod_injective d
    rw [grassToZMod_mul, grassToZMod_zero d, zero_mul]
  mul_zero a          := by
    apply ext; simp only [mul_toFin, zero_toFin]
    apply grassToZMod_injective d
    rw [grassToZMod_mul, grassToZMod_zero d, mul_zero]

/-- **General ring isomorphism**: every operationistic grassland is a
    commutative ring isomorphic to `ℤ/Gℤ`, via the affine shift `θ_B`. -/
def toZModRingEquiv (d : GrasslandData) : Grass d ≃+* ZMod d.G where
  toFun     := fun a => grassToZMod d a.toFin
  invFun    := fun z => ⟨grassFromZMod d z⟩
  left_inv  := fun a => ext (grassFromZMod_toZMod d a.toFin)
  right_inv := grassToZMod_fromZMod d
  map_add'  := fun a b => grassToZMod_add d a.toFin b.toFin
  map_mul'  := fun a b => grassToZMod_mul d a.toFin b.toFin

/-- **General field**: when the gap `G` is prime, every grassland chapter is a
    Galois field `GF(G)`, independently of the base `B`. -/
instance instField [Fact (Nat.Prime d.G)] : Field (Grass d) :=
  Equiv.field (toZModRingEquiv d).toEquiv

end Grass

/-! ## 5. Instance 1: Classical Modular Arithmetic

  ℤ/mℤ is the flat case B = 0.
  It is the "degenerate" grassland with a single chapter of size m.
  The identity is 0, the operation is ordinary modular addition.
-/

/-- The grassland of modular arithmetic with modulus m -/
def modularGrassland (m : ℕ) (hm : 0 < m) : GrasslandData :=
  { G := m, B := 0, hG := hm }

/-- The operation of the modular grassland coincides with addition in ℤ/mℤ -/
theorem modularGrassland_add_eq (m : ℕ) (hm : 0 < m)
    (r s : Fin m) :
    grassAdd (modularGrassland m hm) r s =
    ⟨(r.val + s.val) % m, Nat.mod_lt _ hm⟩ := by
  simp [grassAdd, modularGrassland]

/-- The identity of the modular grassland is 0 -/
theorem modularGrassland_neutral_zero (m : ℕ) (hm : 0 < m) :
    grassNeutral (modularGrassland m hm) = ⟨0, hm⟩ := by
  simp [grassNeutral, modularGrassland]

-- Computational check: ℤ/7ℤ as a grassland
#eval (grassAdd (modularGrassland 7 (by norm_num))
        ⟨3, by simp [modularGrassland]⟩ ⟨5, by simp [modularGrassland]⟩).val  -- expected: 1

/-! ## 6. Instance 2: Radical Structure — Aod_n

  The chapter structure Aod_n is the curved case B = k^n, G = (k+1)^n - k^n.
  Each chapter k of degree n defines a distinct grassland.
  The identity is capNeutral n k, the operation is capAdd n k.
-/

/-- The radical grassland at chapter k of degree n —
    this is the central structure of the Operationistic Fields -/
def radicalGrassland (n k : ℕ) (hn : n ≠ 0) : GrasslandData :=
  { G := capGap n k,
    B := k ^ n,
    hG := capGap_pos n k hn }

/-- The operation of the radical grassland coincides with capAdd -/
theorem radicalGrassland_add_eq (n k : ℕ) (hn : n ≠ 0)
    (r s : Fin (capGap n k)) :
    grassAdd (radicalGrassland n k hn) r s = capAdd n k hn r s := by
  simp [grassAdd, radicalGrassland, capAdd]

/-- The identity of the radical grassland coincides with capNeutral -/
theorem radicalGrassland_neutral_eq (n k : ℕ) (hn : n ≠ 0) :
    grassNeutral (radicalGrassland n k hn) = capNeutral n k hn := by
  simp [grassNeutral, radicalGrassland, capNeutral]

/-- The group theorems already proved in GroupStructure are
    automatically instances of the general theorem.
    This lemma makes that explicit for capAdd_comm'. -/
theorem radicalGrassland_comm_instance (n k : ℕ) (hn : n ≠ 0)
    (r s : Fin (capGap n k)) :
    capAdd n k hn r s = capAdd n k hn s r := by
  rw [← radicalGrassland_add_eq n k hn r s,
      ← radicalGrassland_add_eq n k hn s r]
  exact grassAdd_comm (radicalGrassland n k hn) r s

-- Computational checks: Aod_3, chapter k=1 (GF(7))
-- grassAdd computes (B + r + s) % G = (1 + r + s) % 7
-- To get 0: need r + s = 6, e.g. r=2, s=4 → (1+2+4)%7 = 0
#eval (grassAdd (radicalGrassland 3 1 (by norm_num))
        ⟨2, by simp [radicalGrassland, capGap]⟩
        ⟨4, by simp [radicalGrassland, capGap]⟩).val   -- expected: 0  (B=1, 1+2+4=7≡0 mod 7)

#eval (grassNeutral (radicalGrassland 3 1 (by norm_num))).val  -- expected: 6

/-! ## 6b. Instance 3: Fibonacci Grassland — an exponential example

  A partition function need not have polynomial chapters.  Taking
      φ_Fib(x) = max { F_k | F_k ≤ x }
  gives chapters [F_k, F_{k+1}) whose width is, by the Fibonacci recurrence,
      F_{k+1} - F_k = F_{k-1}.
  This illustrates the generality of (P1)–(P3): the abelian group on each
  chapter is obtained "for free" from `grassland_isAbelianGroup`, with no
  reference to the radical arithmetic.  (Multiplication / ring structure is
  out of scope for this file, which is additive by design.)
-/

/-- The Fibonacci grassland at chapter `k` (`k ≥ 2`): base `F_k`, gap `F_{k-1}`. -/
def fibonacciGrassland (k : ℕ) (hk : 2 ≤ k) : GrasslandData :=
  { G := Nat.fib (k - 1),
    B := Nat.fib k,
    hG := Nat.fib_pos.mpr (by omega) }

/-- The chapter width of the Fibonacci grassland is the Fibonacci gap
    `F_{k+1} - F_k = F_{k-1}`, confirming it is the chapter `[F_k, F_{k+1})`. -/
theorem fibonacciGrassland_gap_eq (k : ℕ) (hk : 2 ≤ k) :
    Nat.fib (k + 1) - Nat.fib k = Nat.fib (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : Nat.fib (m + 1 + 1) = Nat.fib (m + 1) + Nat.fib m := by
    rw [show m + 1 + 1 = m + 2 from rfl, Nat.fib_add_two]
    exact Nat.add_comm _ _
  simp only [Nat.add_sub_cancel]
  rw [h]; omega

/-- Every Fibonacci chapter is an abelian group `≅ ℤ/F_{k-1}ℤ`,
    as an immediate instance of the general theorem. -/
theorem fibonacciGrassland_isAbelianGroup (k : ℕ) (hk : 2 ≤ k) :
    let e := grassNeutral (fibonacciGrassland k hk)
    (∀ r,   grassAdd (fibonacciGrassland k hk) e r = r) ∧
    (∀ r,   grassAdd (fibonacciGrassland k hk) r e = r) ∧
    (∀ r s, grassAdd (fibonacciGrassland k hk) r s
              = grassAdd (fibonacciGrassland k hk) s r) ∧
    (∀ r s t, grassAdd (fibonacciGrassland k hk) (grassAdd (fibonacciGrassland k hk) r s) t
              = grassAdd (fibonacciGrassland k hk) r (grassAdd (fibonacciGrassland k hk) s t)) ∧
    (∀ r,   grassAdd (fibonacciGrassland k hk) r (grassInv (fibonacciGrassland k hk) r) = e) :=
  grassland_isAbelianGroup (fibonacciGrassland k hk)

-- Computational checks: chapter k=6 → base F_6 = 8, gap F_5 = 5, group ℤ/5ℤ
#eval (fibonacciGrassland 6 (by norm_num)).B                     -- expected: 8  (F_6)
#eval (fibonacciGrassland 6 (by norm_num)).G                     -- expected: 5  (F_5)
#eval Nat.fib 7 - Nat.fib 6                                      -- expected: 5  (gap = F_5)
#eval (grassNeutral (fibonacciGrassland 6 (by norm_num))).val    -- expected: 2  ((5 - 8%5)%5)

/-! ## 7. The fundamental distinction: flat vs curved

  The modular grassland has B = 0: the chapter is centered on the origin.
  The radical grassland has B = k^n ≥ 1: the chapter is translated along the
  line of the naturals. The family {Aod_n} is therefore a family of grasslands
  parametric in n (degree) and k (chapter), with variable size g_k.

  This explains why the two structures, despite having the same operational form,
  have different arithmetic properties: the identity of the radical grassland
  is not 0 (except for k=0), but depends on k^n mod g_k.

  Summary:
    Type               B       G            Identity
    ─────────────────────────────────────────────────
    Classical modular  0       m            0
    Radical Aod_n      k^n     (k+1)^n-k^n  (g_k - k^n % g_k) % g_k
-/

/-! ## 8. The general ring/field is inherited by every instance

  The modular, radical, and Fibonacci grasslands obtain their per-chapter
  commutative-ring (and, for prime gap, Galois-field) structure directly, as
  instances of the general `Grass` construction (§4f) — confirming that the
  intra-chapter algebra is base-independent.  The radical-specific content of
  the paper is the inter-chapter theory (growing frontier, translations,
  Aod∞, Aod★), not the intra-chapter algebra developed here. -/

-- The modular grassland's ring is exactly ℤ/mℤ (general construction).
example (m : ℕ) (hm : 0 < m) : CommRing (Grass (modularGrassland m hm)) := inferInstance

-- The Fibonacci grassland's chapter ring, involving no radical arithmetic.
example (k : ℕ) (hk : 2 ≤ k) : CommRing (Grass (fibonacciGrassland k hk)) := inferInstance

-- The radical chapter ring at degree n, chapter k — the instance the paper uses.
example (n k : ℕ) (hn : n ≠ 0) : CommRing (Grass (radicalGrassland n k hn)) := inferInstance

-- A prime-gap radical chapter is a Galois field, via the general field instance:
-- GF(7) = radical chapter k=1 of degree 3 (capGap 3 1 = 7).
example : Field (Grass (radicalGrassland 3 1 (by norm_num))) :=
  haveI : Fact (Nat.Prime (radicalGrassland 3 1 (by norm_num)).G) := ⟨by decide⟩
  inferInstance

#eval (grassMul (modularGrassland 7 (by norm_num))
        ⟨3, by simp [modularGrassland]⟩ ⟨5, by simp [modularGrassland]⟩).val  -- (0+3)*(0+5)%7 = 1

end CampiOperazionistici
