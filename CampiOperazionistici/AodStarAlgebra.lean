/-
  AodStarAlgebra.lean
  Algebraic Structures on Aod★: Radical Defect and the ⊕★ Operation
  Campi Operazionistici — Algebraic foundations of Aod★
  Author: Alessandro Sgarbi — 2026-03-19
  Paper: §21 (Radical Star Algebra)

  Dependencies:
  - `AodStar.lean` — mpp, radRemStar, isPPAny, aodStarEquiv, AodStarField

  File structure:
  § 1. Radical defect D★(a,b)                — proved (0 sorry)
  § 2. The ⊕★ operation on Aod★             — commutativity/idempotence/well-definedness
  § 3. Proof notes (R2)                      — ⊕★ is well defined on Aod★ classes
  § 4. Corollaries (defect, ⊕★ on the quotient)
  § 5. AddCommMonoid on AodStarField — Approach A (addition of representatives)
  § 6. Idempotence of r★
  § 7. AddCommMonoid on AodStarField — Approach B (direct addition on ℕ)
  § 8. Partial progress: special PP cases
  § 9. Commutative magma structure on (AodStarField, ⊕★)
  §10. Impossibility theorem: ¬ IsRadRemStarAdditive

  Terminological note:
  - "Aod★ class" (or "fiber of r★") = {x ∈ ℕ : r★(x) = c} for a given c.
    It is the set of equivalence classes of ≡★. It is NOT a contiguous interval.
  - "Aod★ chapter" (not used here) = interval (pᵢ, pᵢ₊₁) between consecutive
    perfect powers. The correct analogue of CapChap(n,k) for Aod★.
  - `capAddStar` keeps the name by analogy with `capAdd`, but it operates on the
    *Aod★ classes* via their canonical representatives, not on the chapters.

  Architectural note:
  - The M3-good and local meadow structures belong to Aod_n (CapChap),
    not to Aod★. They live in `MeadowLocal.lean`.
  - Approaches A and B show the structural limits of addition on AodStarField:
    see §10 for the impossibility theorem for IsRadRemStarAdditive.
-/

import CampiOperazionistici.AodStar
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

open CampiOperazionistici
open AodStar

namespace AodStarAlgebra

-- ================================================================
-- § 1. Universal Radical Defect D★
-- ================================================================

/-!
### Radical defect

`D★(a,b) = r★(a+b) − r★(a) − r★(b) : ℤ` measures how much r★ deviates
from additivity. The distribution on [2,79]×[2,79] is skewed toward the
negative (~59.5%): larger PPs tend to absorb the sum.
-/

/-- Radical defect of r★ with respect to addition. -/
def defectStar (a b : ℕ) : ℤ :=
  (radRemStar (a + b) : ℤ) - (radRemStar a : ℤ) - (radRemStar b : ℤ)

#eval defectStar 2 3   -- -2: r★(5)=1, r★(2)=1, r★(3)=2  →  1-1-2=-2
#eval defectStar 9 16  --  0: 9+16=25=5², r★(9)=r★(16)=0
#eval defectStar 4 4   --  0: 4+4=8=2³, r★(4)=r★(8)=0

/-- D★ is symmetric. -/
theorem defectStar_comm (a b : ℕ) : defectStar a b = defectStar b a := by
  simp only [defectStar, add_comm a b]; ring

/-- When a is PP: D★(a,b) = r★(a+b) − r★(b). -/
theorem defectStar_pp_left {a b : ℕ} (hPP : isPPAny a) :
    defectStar a b = (radRemStar (a + b) : ℤ) - (radRemStar b : ℤ) := by
  simp [defectStar, radRemStar_zero_of_isPPAny hPP]

/-- When b is PP: D★(a,b) = r★(a+b) − r★(a). -/
theorem defectStar_pp_right {a b : ℕ} (hPP : isPPAny b) :
    defectStar a b = (radRemStar (a + b) : ℤ) - (radRemStar a : ℤ) := by
  simp [defectStar, radRemStar_zero_of_isPPAny hPP, add_comm a b]

/-- When a and b are both PP: D★(a,b) = r★(a+b). -/
theorem defectStar_pp_both {a b : ℕ} (ha : isPPAny a) (hb : isPPAny b) :
    defectStar a b = (radRemStar (a + b) : ℤ) := by
  simp [defectStar, radRemStar_zero_of_isPPAny ha, radRemStar_zero_of_isPPAny hb]

/-- D★(a,b) ≥ −r★(a) − r★(b): the defect is bounded below. -/
theorem defectStar_lowerBound (a b : ℕ) :
    defectStar a b ≥ -(radRemStar a : ℤ) - (radRemStar b : ℤ) := by
  simp [defectStar]

-- ================================================================
-- § 2. Universal Chapter Operation ⊕★
-- ================================================================

/-!
### The ⊕★ operation

`capAddStar r s` operates on the *canonical representatives* `r' = r★(r)` and `s' = r★(s)`,
then applies the formula `r★(2·(mpp r' + mpp s') + r' + s')`.
Normalizing through r★ guarantees that the operation depends only on the
Aod★ class, not on the specific representative: this is condition R2.

Note: "Aod★ class of c" = {x ∈ ℕ : r★(x) = c}. The ⊕★ operation is well defined
on these classes (proved in §3).
-/

/-- Additive operation ⊕★, well defined on Aod★ classes.
    Normalizes the inputs through r★ before applying the formula. -/
def capAddStar (r s : ℕ) : ℕ :=
  let r' := radRemStar r
  let s' := radRemStar s
  radRemStar (2 * (mpp r' + mpp s') + r' + s')

#eval capAddStar 0 0  -- 0  (r★(0)=0, r★(0)=0 → r★(0)=0)
#eval capAddStar 1 1  -- 0  (r★(1)=0, same class → 0)
#eval capAddStar 4 4  -- 0  (r★(4)=0, same class as 1 → 0)
#eval capAddStar 2 2  -- 2  (r★(2)=1, r★(2)=1 → r★(6)=2)
#eval capAddStar 3 3  -- 0  (r★(3)=2, r★(3)=2 → r★(8)=0)

/-- Commutativity of ⊕★: immediate from the symmetry of the formula. -/
theorem capAddStar_comm (r s : ℕ) : capAddStar r s = capAddStar s r := by
  simp only [capAddStar]; congr 1; omega

/-- Base case: 0 ⊕★ 0 = 0. -/
theorem capAddStar_zero_idem : capAddStar 0 0 = 0 := by
  simp only [capAddStar]
  have h0 : radRemStar 0 = 0 := by simp [radRemStar, Nat.le_zero.mp (mpp_le_self 0)]
  simp only [h0]
  have hm : mpp 0 = 0 := Nat.le_zero.mp (mpp_le_self 0)
  simp [hm, radRemStar]

-- ================================================================
-- § 3. Proof Notes (R2 — well-definedness of ⊕★)
-- ================================================================

/-!
### capAddStar_well_defined (Problem R2 — resolved)

**Status:** PROVED.

The definition of `capAddStar` normalizes the two inputs through r★ before
applying the formula. Hence `capAddStar r s` depends only on
`radRemStar r` and `radRemStar s`, not on the specific representatives r and s.
Well-definedness on Aod★ classes is immediate by rewriting.
-/
theorem capAddStar_well_defined (r₁ r₂ s₁ s₂ : ℕ)
    (hr : aodStarEquiv r₁ r₂) (hs : aodStarEquiv s₁ s₂) :
    aodStarEquiv (capAddStar r₁ s₁) (capAddStar r₂ s₂) := by
  simp only [aodStarEquiv, capAddStar]
  rw [hr, hs]

-- ================================================================
-- § 4. Corollaries
-- ================================================================

/-!
### § 4.1 Corollaries of the radical defect
-/

/-- D★(0, b) = 0: the PP class does not contribute to the defect. -/
theorem defectStar_zero_left (b : ℕ) : defectStar 0 b = 0 := by
  rw [defectStar_pp_left isPPAny_zero]
  simp

/-- D★(a, 0) = 0. -/
theorem defectStar_zero_right (a : ℕ) : defectStar a 0 = 0 := by
  rw [defectStar_comm, defectStar_zero_left]

/-- If a+b is a PP, the defect equals −r★(a) − r★(b):
    the sum is completely "absorbed" by the nearest PP. -/
theorem defectStar_sum_isPP {a b : ℕ} (hPP : isPPAny (a + b)) :
    defectStar a b = -((radRemStar a : ℤ) + (radRemStar b : ℤ)) := by
  simp [defectStar, radRemStar_zero_of_isPPAny hPP]; ring

/-!
### § 4.2 Corollaries of ⊕★ and of well-definedness
-/

/-- If r is a PP, then r ⊕★ s = 0 ⊕★ s: the PP class is the zero of ⊕★. -/
theorem capAddStar_pp_left {r : ℕ} (hPP : isPPAny r) (s : ℕ) :
    capAddStar r s = capAddStar 0 s := by
  simp only [capAddStar, radRemStar_zero_of_isPPAny hPP, radRemStar_zero_of_isPPAny isPPAny_zero]

/-- If s is a PP, then r ⊕★ s = r ⊕★ 0. -/
theorem capAddStar_pp_right {s : ℕ} (hPP : isPPAny s) (r : ℕ) :
    capAddStar r s = capAddStar r 0 := by
  simp only [capAddStar, radRemStar_zero_of_isPPAny hPP, radRemStar_zero_of_isPPAny isPPAny_zero]

/-- ⊕★ is well defined on the quotient AodStarField. -/
def capAddStarQ : AodStarField → AodStarField → AodStarField :=
  Quotient.lift₂
    (fun a b => Quotient.mk aodStarSetoid (capAddStar a b))
    (fun a₁ b₁ a₂ b₂ ha hb => Quotient.sound (capAddStar_well_defined a₁ a₂ b₁ b₂ ha hb))

/-- ⊕★ on the quotient is commutative. -/
theorem capAddStarQ_comm (x y : AodStarField) : capAddStarQ x y = capAddStarQ y x := by
  induction x using Quotient.inductionOn with | _ a => ?_
  induction y using Quotient.inductionOn with | _ b => ?_
  exact Quotient.sound (by simp [capAddStar_comm])

-- ================================================================
-- § 5. AddCommMonoid on AodStarField — Approach A
-- ================================================================

/-!
### AddCommMonoid on AodStarField — Approach A: addition of canonical representatives

**Approach A**: `[a]★ + [b]★ := [r★(a) + r★(b)]★`

Well defined: the output depends only on `r★(a)` and `r★(b)`, class invariants.
Commutativity is immediate.

Structural problem: associativity and the neutrality of 0 require `r★(r★(x)) = r★(x)`
(idempotence), which is **false** (e.g. `r★(r★(10)) = r★(1) = 0 ≠ 1`).

Conclusion: Approach A with `hidem` collapses everything to the class [0] (the PPs):
it is the trivial monoid {[0]}. It is not algebraically interesting.
-/

private def addStarRaw (a b : ℕ) : ℕ := radRemStar a + radRemStar b

private theorem addStarRaw_wd (a₁ a₂ b₁ b₂ : ℕ)
    (ha : aodStarEquiv a₁ a₂) (hb : aodStarEquiv b₁ b₂) :
    aodStarEquiv (addStarRaw a₁ b₁) (addStarRaw a₂ b₂) := by
  simp only [aodStarEquiv, addStarRaw]
  rw [ha, hb]

/-- Addition (Approach A) on AodStarField: [a]★ + [b]★ = [r★(a) + r★(b)]★. -/
instance instAdd : Add AodStarField where
  add := Quotient.lift₂
    (fun a b => Quotient.mk aodStarSetoid (addStarRaw a b))
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (addStarRaw_wd a₁ a₂ b₁ b₂ ha hb))

/-- Neutral element: [0]★. -/
instance instZero : Zero AodStarField where
  zero := Quotient.mk aodStarSetoid 0

private theorem add_def (a b : ℕ) :
    (Quotient.mk aodStarSetoid a) + (Quotient.mk aodStarSetoid b)
    = Quotient.mk aodStarSetoid (addStarRaw a b) := rfl

private theorem zero_def :
    (0 : AodStarField) = Quotient.mk aodStarSetoid 0 := rfl

-- ================================================================
-- § 6. Idempotence of r★
-- ================================================================

/-!
### § 6. Idempotence of r★: characterization and closable cases

`r★(r★(a)) = r★(a)` is equivalent to `r★(a) = 0` (i.e. `a` is PP).
The only fixed point of r★ is 0: for x ≥ 1, r★(x) < x (T1).

Consequence for Approach A: `hidem` implies r★(a) = 0 for every a,
collapsing AodStarField to the trivial monoid {[0]}.
-/

/-- r★ is idempotent on `a` iff `r★a = 0` (i.e. `a` is PP). -/
theorem radRemStar_idem_iff {a : ℕ} :
    radRemStar (radRemStar a) = radRemStar a ↔ radRemStar a = 0 := by
  constructor
  · intro h
    by_cases h0 : radRemStar a = 0
    · exact h0
    · exfalso
      have hge : 1 ≤ radRemStar a := Nat.one_le_iff_ne_zero.mpr h0
      have hlt : radRemStar (radRemStar a) < radRemStar a := radRemStar_lt_self hge
      linarith [h ▸ hlt]
  · intro h
    rw [h]
    exact radRemStar_zero_of_isPPAny isPPAny_zero

/-- r★ is zero on the PPs, hence r★(r★a) = r★a for a ∈ PP. -/
theorem radRemStar_idem_of_pp {a : ℕ} (h : isPPAny a) :
    radRemStar (radRemStar a) = radRemStar a := by
  rw [radRemStar_zero_of_isPPAny h]
  exact radRemStar_zero_of_isPPAny isPPAny_zero

/-- If r★a = 0, then r★(r★a) = r★a. -/
theorem radRemStar_idem_of_zero {a : ℕ} (h : radRemStar a = 0) :
    radRemStar (radRemStar a) = radRemStar a :=
  radRemStar_idem_iff.mpr h

private theorem approachA_zero_add_iff (a : ℕ) :
    aodStarEquiv (addStarRaw 0 a) a ↔ radRemStar a = 0 := by
  simp only [aodStarEquiv, addStarRaw, radRemStar_zero_of_isPPAny isPPAny_zero, zero_add]
  exact radRemStar_idem_iff

/-- (AodStarField, +, 0) is an AddCommMonoid under `hidem` (Approach A).
    The hypothesis `hidem` holds only for PPs (r★a=0), not in general.
    Under `hidem` the monoid is trivial: every element coincides with [0]. -/
def addCommMonoidA_of_idem
    (hidem : ∀ a : ℕ, radRemStar (radRemStar a) = radRemStar a) :
    AddCommMonoid AodStarField where
  add           := instAdd.add
  zero          := instZero.zero
  add_assoc x y z := by
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    induction z using Quotient.inductionOn with | _ c => ?_
    simp only [add_def]
    apply Quotient.sound
    show aodStarEquiv (addStarRaw (addStarRaw a b) c) (addStarRaw a (addStarRaw b c))
    simp only [aodStarEquiv, addStarRaw]
    have h0 : ∀ x : ℕ, radRemStar x = 0 := fun x => radRemStar_idem_iff.mp (hidem x)
    simp [h0]
  zero_add x := by
    induction x using Quotient.inductionOn with | _ a => ?_
    simp only [zero_def, add_def]
    apply Quotient.sound
    show aodStarEquiv (addStarRaw 0 a) a
    rw [approachA_zero_add_iff]
    exact radRemStar_idem_iff.mp (hidem a)
  add_zero x := by
    induction x using Quotient.inductionOn with | _ a => ?_
    simp only [zero_def, add_def]
    apply Quotient.sound
    show aodStarEquiv (addStarRaw a 0) a
    simp only [aodStarEquiv, addStarRaw, radRemStar_zero_of_isPPAny isPPAny_zero, add_zero]
    exact hidem a
  add_comm x y := by
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    simp [add_def, addStarRaw, add_comm]
  nsmul         := nsmulRec
  nsmul_zero _  := rfl
  nsmul_succ _ _ := rfl

/-- Under `hidem`, every element of AodStarField is the class [0]. -/
theorem hidem_implies_all_zero
    (hidem : ∀ a : ℕ, radRemStar (radRemStar a) = radRemStar a)
    (x : AodStarField) : x = (0 : AodStarField) := by
  induction x using Quotient.inductionOn with | _ a => ?_
  simp only [zero_def]
  apply Quotient.sound
  show aodStarEquiv a 0
  simp only [aodStarEquiv]
  have h0 : ∀ y : ℕ, radRemStar y = 0 := fun y => radRemStar_idem_iff.mp (hidem y)
  simp [h0]

/-- Approach A with `hidem` is the trivial monoid {[0]}. -/
theorem addCommMonoidA_is_trivial
    (hidem : ∀ a : ℕ, radRemStar (radRemStar a) = radRemStar a) :
    ∀ x y : AodStarField, x = y := by
  intro x y
  rw [hidem_implies_all_zero hidem x, hidem_implies_all_zero hidem y]

/-- (AodStarField, +, 0) is an AddCommMonoid (Approach A) under `hidem`. -/
instance instAddCommMonoidAodStarField
    (hidem : ∀ a : ℕ, radRemStar (radRemStar a) = radRemStar a) :
    AddCommMonoid AodStarField :=
  addCommMonoidA_of_idem hidem

-- ================================================================
-- § 7. Approach B: direct addition on ℕ
-- ================================================================

/-!
### AddCommMonoid on AodStarField — Approach B: direct addition on ℕ

**Idea**: `[a]★ +₃ [b]★ := [a + b]★` (direct addition on representatives).

All the monoid laws (associativity, commutativity, neutrality of 0)
follow trivially from ℕ.

The only obstacle is well-definedness: one needs `r★(a₁+b₁) = r★(a₂+b₂)`
whenever `r★a₁ = r★a₂` and `r★b₁ = r★b₂`. This is false in general
(r★ is not additive with respect to ≡★). See §10 for the impossibility theorem.
-/

/-- Additivity condition of r★ with respect to ≡★.
    This proposition is **false** (see §10 `not_isRadRemStarAdditive`). -/
def IsRadRemStarAdditive : Prop :=
  ∀ a₁ a₂ b₁ b₂ : ℕ,
    radRemStar a₁ = radRemStar a₂ →
    radRemStar b₁ = radRemStar b₂ →
    radRemStar (a₁ + b₁) = radRemStar (a₂ + b₂)

/-- Well-definedness of addNat under `IsRadRemStarAdditive`. -/
theorem addNatRaw_wd_of_additive (hadditive : IsRadRemStarAdditive)
    (a₁ a₂ b₁ b₂ : ℕ)
    (ha : aodStarEquiv a₁ a₂) (hb : aodStarEquiv b₁ b₂) :
    aodStarEquiv (a₁ + b₁) (a₂ + b₂) := by
  simp only [aodStarEquiv] at *
  exact hadditive a₁ a₂ b₁ b₂ ha hb

/-- `addNat` well defined under `IsRadRemStarAdditive`. -/
def addNat_of_additive (hadditive : IsRadRemStarAdditive) :
    AodStarField → AodStarField → AodStarField :=
  Quotient.lift₂
    (fun a b => Quotient.mk aodStarSetoid (a + b))
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (addNatRaw_wd_of_additive hadditive a₁ a₂ b₁ b₂ ha hb))

private theorem addNat_of_additive_def (hadditive : IsRadRemStarAdditive) (a b : ℕ) :
    addNat_of_additive hadditive (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
    = Quotient.mk aodStarSetoid (a + b) := rfl

/-- (AodStarField, addNat, 0) is an AddCommMonoid under `IsRadRemStarAdditive`. -/
def addCommMonoidB_of_additive (hadditive : IsRadRemStarAdditive) :
    AddCommMonoid AodStarField where
  add           := addNat_of_additive hadditive
  zero          := instZero.zero
  add_assoc x y z := by
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    induction z using Quotient.inductionOn with | _ c => ?_
    show addNat_of_additive hadditive
           (addNat_of_additive hadditive (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b))
           (Quotient.mk aodStarSetoid c)
       = addNat_of_additive hadditive (Quotient.mk aodStarSetoid a)
           (addNat_of_additive hadditive (Quotient.mk aodStarSetoid b) (Quotient.mk aodStarSetoid c))
    rw [addNat_of_additive_def, addNat_of_additive_def, addNat_of_additive_def,
        addNat_of_additive_def, add_assoc]
  zero_add x := by
    induction x using Quotient.inductionOn with | _ a => ?_
    show addNat_of_additive hadditive (Quotient.mk aodStarSetoid 0) (Quotient.mk aodStarSetoid a)
       = Quotient.mk aodStarSetoid a
    rw [addNat_of_additive_def, zero_add]
  add_zero x := by
    induction x using Quotient.inductionOn with | _ a => ?_
    show addNat_of_additive hadditive (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid 0)
       = Quotient.mk aodStarSetoid a
    rw [addNat_of_additive_def, add_zero]
  add_comm x y := by
    induction x using Quotient.inductionOn with | _ a => ?_
    induction y using Quotient.inductionOn with | _ b => ?_
    show addNat_of_additive hadditive (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
       = addNat_of_additive hadditive (Quotient.mk aodStarSetoid b) (Quotient.mk aodStarSetoid a)
    rw [addNat_of_additive_def, addNat_of_additive_def, add_comm]
  nsmul n x :=
    Nat.rec (Quotient.mk aodStarSetoid 0)
      (fun _ acc => addNat_of_additive hadditive acc x) n
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

-- ================================================================
-- § 8. Partial progress: special PP cases
-- ================================================================

/-!
### § 8. Approach A: monoid laws closed for PP elements

`zero_add` and `add_zero` close when `a` is a perfect power.
`add_assoc` closes when all three arguments are PP.
-/

/-- [0] is a left neutral for the PP classes in Approach A. -/
theorem zero_add_of_pp {a : ℕ} (h : isPPAny a) :
    (0 : AodStarField) + Quotient.mk aodStarSetoid a
    = Quotient.mk aodStarSetoid a := by
  simp only [zero_def, add_def]
  exact Quotient.sound (by
    show aodStarEquiv (addStarRaw 0 a) a
    simp [aodStarEquiv, addStarRaw,
          radRemStar_zero_of_isPPAny isPPAny_zero,
          radRemStar_zero_of_isPPAny h])

/-- [0] is a right neutral for the PP classes in Approach A. -/
theorem add_zero_of_pp {a : ℕ} (h : isPPAny a) :
    Quotient.mk aodStarSetoid a + (0 : AodStarField)
    = Quotient.mk aodStarSetoid a := by
  simp only [zero_def, add_def]
  exact Quotient.sound (by
    show aodStarEquiv (addStarRaw a 0) a
    simp [aodStarEquiv, addStarRaw,
          radRemStar_zero_of_isPPAny isPPAny_zero,
          radRemStar_zero_of_isPPAny h])

/-- Associativity in Approach A when all three arguments are PP. -/
theorem add_assoc_of_pp_all {a b c : ℕ} (ha : isPPAny a) (hb : isPPAny b) (hc : isPPAny c) :
    Quotient.mk aodStarSetoid a
      + Quotient.mk aodStarSetoid b
      + Quotient.mk aodStarSetoid c
    = Quotient.mk aodStarSetoid a
      + (Quotient.mk aodStarSetoid b + Quotient.mk aodStarSetoid c) := by
  simp only [add_def]
  apply Quotient.sound
  show aodStarEquiv (addStarRaw (addStarRaw a b) c) (addStarRaw a (addStarRaw b c))
  simp [aodStarEquiv, addStarRaw,
        radRemStar_zero_of_isPPAny ha,
        radRemStar_zero_of_isPPAny hb,
        radRemStar_zero_of_isPPAny hc]

/-- Well-definedness of addNat when the representatives are canonical. -/
theorem addNatRaw_wd_canonical (a₁ a₂ b₁ b₂ : ℕ)
    (hcan_a  : radRemStar a₁ = a₁)
    (hcan_a₂ : radRemStar a₂ = a₂)
    (hcan_b  : radRemStar b₁ = b₁)
    (hcan_b₂ : radRemStar b₂ = b₂)
    (ha : aodStarEquiv a₁ a₂) (hb : aodStarEquiv b₁ b₂) :
    aodStarEquiv (a₁ + b₁) (a₂ + b₂) := by
  have ha2 : a₂ = a₁ := by
    simp only [aodStarEquiv] at ha
    rw [hcan_a, hcan_a₂] at ha
    exact ha.symm
  have hb2 : b₂ = b₁ := by
    simp only [aodStarEquiv] at hb
    rw [hcan_b, hcan_b₂] at hb
    exact hb.symm
  simp [aodStarEquiv, ha2, hb2]

-- ================================================================
-- § 9. Commutative magma structure on (AodStarField, ⊕★)
-- ================================================================

/-!
### § 9. Algebraic structure of ⊕★ on AodStarField

The pair `(AodStarField, ⊕★)` where `⊕★ = capAddStarQ` is:
- **Commutative magma**: ⊕★ is a well-defined and commutative binary operation.
- **Idempotent on the PP class**: `[PP] ⊕★ [PP] = [PP]`.

**Associativity FAILS** (`not_capAddStar_assoc`, `not_capAddStarQ_assoc`):
the magma is *not* a semigroup. The interference between distinct
perfect-power degrees destroys associativity, so no natural monoid (or even
semigroup) structure exists on Aod★. This refutes the former open
conjecture `conj:capAddStar-assoc`.
-/

/-- `(AodStarField, ⊕★)` is a commutative magma. -/
instance instCommMagmaCapAddStar : CommMagma AodStarField where
  mul       := capAddStarQ
  mul_comm  := capAddStarQ_comm

/-- 0 is idempotent for ⊕★: [0]★ ⊕★ [0]★ = [0]★. -/
theorem capAddStarQ_zero_idem :
    capAddStarQ (0 : AodStarField) 0 = 0 := by
  simp only [capAddStarQ, zero_def]
  exact Quotient.sound (by simp [capAddStar_zero_idem])

/-- All PPs have the same image 0 under ⊕★. -/
theorem capAddStarQ_pp_pp {a b : ℕ} (ha : isPPAny a) (hb : isPPAny b) :
    capAddStarQ (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
    = (0 : AodStarField) := by
  simp only [capAddStarQ, zero_def]
  apply Quotient.sound
  show aodStarEquiv (capAddStar a b) 0
  have ha0 : radRemStar a = 0 := radRemStar_zero_of_isPPAny ha
  have hb0 : radRemStar b = 0 := radRemStar_zero_of_isPPAny hb
  have hmpp0 : mpp 0 = 0 := Nat.le_zero.mp (mpp_le_self 0)
  simp [aodStarEquiv, capAddStar, ha0, hb0, hmpp0,
        radRemStar_zero_of_isPPAny isPPAny_zero]

/-- The PP class is closed under ⊕★. -/
theorem capAddStarQ_pp_class_closed {a b : ℕ} (ha : isPPAny a) (hb : isPPAny b) :
    ∃ c : ℕ, isPPAny c ∧
      capAddStarQ (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
      = Quotient.mk aodStarSetoid c :=
  ⟨0, isPPAny_zero, capAddStarQ_pp_pp ha hb⟩

/-!
### Non-associativity of ⊕★ (refutation of `conj:capAddStar-assoc`)

The star-addition is **not associative**, hence `(AodStarField, ⊕★)` is a
commutative magma but **not** a semigroup. The witness is the triple of
classes `([0]★, [0]★, [13]★)` (representatives `r★ = 0, 0, 4`):

  `([0]★ ⊕̂★ [0]★) ⊕̂★ [13]★ = [2]★`  but
  `[0]★ ⊕̂★ ([0]★ ⊕̂★ [13]★)  = [0]★`.

Indeed `capAddStar (capAddStar 0 0) 13 = capAddStar 0 13 = r★(12) = 3`
(class `[2]★`), while `capAddStar 0 (capAddStar 0 13) = capAddStar 0 3
= r★(4) = 0` (class `[0]★`). Both class labels differ, so associativity
fails on the quotient. The raw (representative-level) minimal counterexample
is `(0,0,7)`. Verified by kernel-checked `decide`, mirroring `not_isRadRemStarAdditive`.
-/

/-- **Non-associativity of ⊕★ (representative level).**
    There exist `a b c` with `(a ⊕★ b) ⊕★ c ≢★ a ⊕★ (b ⊕★ c)`.
    Counterexample `(0, 0, 13)`: `r★((0⊕★0)⊕★13) = 2 ≠ 0 = r★(0⊕★(0⊕★13))`. -/
theorem not_capAddStar_assoc :
    ¬ ∀ a b c : ℕ,
      aodStarEquiv (capAddStar (capAddStar a b) c) (capAddStar a (capAddStar b c)) := by
  unfold aodStarEquiv
  push_neg
  exact ⟨0, 0, 13, by decide⟩

/-- **Non-associativity of ⊕̂★ on the quotient AodStarField.**
    `(AodStarField, capAddStarQ)` is a commutative magma but **not** a
    semigroup: there is no natural monoid structure on Aod★. -/
theorem not_capAddStarQ_assoc :
    ¬ ∀ x y z : AodStarField,
      capAddStarQ (capAddStarQ x y) z = capAddStarQ x (capAddStarQ y z) := by
  intro h
  apply not_capAddStar_assoc
  intro a b c
  exact Quotient.exact
    (h (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
       (Quotient.mk aodStarSetoid c))

-- ================================================================
-- § 10. Impossibility theorem: ¬ IsRadRemStarAdditive
-- ================================================================

/-!
### § 10. Impossibility of the additivity of r★

`IsRadRemStarAdditive` (the condition that Approach B would require) is **false**.

This is a positive theorem: direct addition on ℕ/≡★ cannot be
well defined. It is a genuine structural result on Aod★.

**Proof strategy:** exhibit a concrete counterexample (a₁, a₂, b₁, b₂) such that:
  r★(a₁) = r★(a₂), r★(b₁) = r★(b₂), but r★(a₁+b₁) ≠ r★(a₂+b₂).

**Status:** PROVED, 0 sorry. The counterexample (a₁,a₂,b₁,b₂) = (2,10,3,11)
is encoded as an explicit proof term and verified with kernel-checked `decide`
(no `native_decide`; the trusted base is the Lean kernel alone, no compiler trust).
-/

/-- r★ is not additive with respect to ≡★: direct addition on ℕ/≡★ is not well defined.
    Counterexample: a₁=2, a₂=10, b₁=3, b₂=11.
    r★(2)=1=r★(10), r★(3)=2=r★(11), but r★(5)=1 ≠ 5=r★(21). -/
theorem not_isRadRemStarAdditive : ¬ IsRadRemStarAdditive := by
  unfold IsRadRemStarAdditive
  push_neg
  -- Counterexample: a₁=2, a₂=10, b₁=3, b₂=11
  -- r★(2)=1, r★(10)=1  →  same class
  -- r★(3)=2, r★(11)=2  →  same class
  -- r★(2+3)=r★(5)=1, r★(10+11)=r★(21)=5  →  1 ≠ 5
  exact ⟨2, 10, 3, 11, by decide, by decide, by decide⟩

-- ================================================================
-- § 11. Additional corollaries
-- ================================================================

/-!
### § 11. Low-effort corollaries

Direct consequences of the theorems already proved.
-/

/-- If a+b is a PP, the defect is non-positive (≤ 0).
    Follows from `defectStar_sum_isPP`: D★ = -(r★a + r★b) ≤ 0. -/
theorem defectStar_nonpos_of_sum_isPP {a b : ℕ} (hPP : isPPAny (a + b)) :
    defectStar a b ≤ 0 := by
  rw [defectStar_sum_isPP hPP]
  have ha : 0 ≤ (radRemStar a : ℤ) := Int.natCast_nonneg _
  have hb : 0 ≤ (radRemStar b : ℤ) := Int.natCast_nonneg _
  linarith

/-- D★ equals r★(2a) - 2·r★(a) when both arguments are a. -/
theorem defectStar_self (a : ℕ) :
    defectStar a a = (radRemStar (2 * a) : ℤ) - 2 * (radRemStar a : ℤ) := by
  simp [defectStar, two_mul]; ring

/-- [0]★ is an absorbing element for ⊕★ from the left:
    if the class b contains a PP, then [0]★ ⊕★ [b]★ = [0]★. -/
theorem capAddStarQ_zero_left_of_pp {b : ℕ} (hb : isPPAny b) :
    capAddStarQ (0 : AodStarField) (Quotient.mk aodStarSetoid b) = 0 := by
  simp only [capAddStarQ, zero_def]
  apply Quotient.sound
  show aodStarEquiv (capAddStar 0 b) 0
  have hb0 : radRemStar b = 0 := radRemStar_zero_of_isPPAny hb
  have h00 : radRemStar 0 = 0 := radRemStar_zero_of_isPPAny isPPAny_zero
  have hmpp0 : mpp 0 = 0 := Nat.le_zero.mp (mpp_le_self 0)
  simp [aodStarEquiv, capAddStar, hb0, h00, hmpp0]

/-- The defect is zero when one of the two arguments is 0. -/
theorem defectStar_zero_iff_left (b : ℕ) : defectStar 0 b = 0 := defectStar_zero_left b

/-- All values of ⊕★ lie in the class [0] when both inputs are PP. -/
theorem capAddStarQ_pp_is_zero {a b : ℕ} (ha : isPPAny a) (hb : isPPAny b) :
    capAddStarQ (Quotient.mk aodStarSetoid a) (Quotient.mk aodStarSetoid b)
    = (0 : AodStarField) :=
  capAddStarQ_pp_pp ha hb

end AodStarAlgebra
