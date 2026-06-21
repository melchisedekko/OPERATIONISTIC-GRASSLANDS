/-
  AodStarTree.lean
  Tree Structure of Aod★: Trajectory, LCA, Metric
  Campi Operazionistici — Combinatorial geometry of the tree T★
  Author: Alessandro Sgarbi — 2026-03-19
  Paper: §22 (The Radical Star Tree)

  Dependencies:
  - `AodStar.lean` — depthStar, radRemStar, depthStar_succ, radRemStar_lt_self,
                     depthStar_eq_of_same_class, aodStarEquiv, AodStarField

  File structure:
  § 1. T-MONO: Strict monotonicity of the depth              — proved (0 sorry)
  § 2. Trajectory traj(a): descent toward 0                  — proved (0 sorry)
  § 3. T-LCA: Lowest Common Ancestor by depth                — proved (0 sorry)
  § 4. T-METRIC: Metric on the tree T★                       — proved (0 sorry)
  § 5. T-DIST-RADICE, T-PADRE                                — proved (0 sorry)
  § 6. T-CLASS-TREE: classes as sets of children             — proved (0 sorry)

  Geometric note:
  The map r★ : ℕ → ℕ defines a directed graph T★ = (ℕ, {(a, r★(a)) : a ≥ 1}).
  This graph is a tree rooted at 0: every node a ≥ 1 has a unique parent r★(a),
  and the trajectory a → r★(a) → r★(r★(a)) → ⋯ → 0 is strictly decreasing (T1),
  hence always terminates at 0.

  Note on T-LCA-1 (well-definedness on classes fails):
  The statement "lca(a₁,b) = lca(a₂,b) whenever r★(a₁) = r★(a₂)" is FALSE,
  so the LCA does not descend to the quotient Aod★. Explicit counterexample with b = 3:
    • a₁ = 2 and a₂ = 10 have the same parent: r★(2) = 1 = r★(10);
    • the trajectories are traj(2) = [2,1,0], traj(10) = [10,1,0], traj(3) = [3,2,1,0];
    • since 2 ∈ traj(3), the lowest common ancestor of 2 and 3 is lca(2,3) = 2;
    • whereas traj(10) ∩ traj(3) = [1,0], giving lca(10,3) = 1.
  Therefore lca(2,3) = 2 ≠ 1 = lca(10,3) even though 2 ≡★ 10: the LCA is not
  well defined on the classes of Aod★.
-/

import CampiOperazionistici.AodStar
import Mathlib.Tactic
import Mathlib.Data.List.Basic

open CampiOperazionistici
open AodStar

namespace AodStarTree

-- ================================================================
-- § 1. T-MONO: Strict Monotonicity of the Depth
-- ================================================================

/-- T-MONO: depth★ is strictly decreasing along r★.
    For every a ≥ 1, depth★(r★(a)) < depth★(a). -/
theorem depthStar_strict_mono {a : ℕ} (ha : 1 ≤ a) :
    depthStar (radRemStar a) < depthStar a := by
  have hne : a ≠ 0 := by omega
  rw [depthStar_succ a hne]
  omega

-- ================================================================
-- § 2. Descent Trajectory: traj(a)
-- ================================================================

/-!
The trajectory `traj a = [a, r★(a), r★(r★(a)), ..., 0]` is built
fuel-based: the fuel is `a + 1`, which suffices because `depthStar a ≤ a`.
-/

/-- Fuel-based trajectory: trajGo fuel a produces exactly `min(fuel, depth★(a)+1)` elements. -/
private def trajGo : ℕ → ℕ → List ℕ
  | 0,     _ => []
  | f + 1, a => a :: trajGo f (radRemStar a)

/-- `traj a` = complete trajectory from a to 0 (both included). -/
def traj (a : ℕ) : List ℕ := trajGo (depthStar a + 1) a

-- Computational checks (depthStar provides the exact fuel)
#eval traj 0   -- [0]
#eval traj 1   -- [1, 0]
#eval traj 2   -- [2, 1, 0]
#eval traj 7   -- [7, 3, 2, 1, 0]
#eval traj 9   -- [9, 0]
#eval traj 23  -- [23, 7, 3, 2, 1, 0]
#eval traj 27  -- [27, 0]

/-- trajGo with fuel ≥ depthStar a + 1 produces the complete trajectory from a to 0. -/
private lemma trajGo_eq_of_fuel_ge (a : ℕ) :
    ∀ f, depthStar a ≤ f → trajGo (f + 1) a = a :: trajGo f (radRemStar a) := by
  intro f _
  simp [trajGo]

-- (trajGo_fuel_irrel not needed: we use depthStar as the exact fuel)

/-- traj 0 = [0]. -/
@[simp] lemma traj_zero : traj 0 = [0] := by
  simp [traj, trajGo, depthStar_zero]

/-- For a ≥ 1: traj a = a :: traj (r★a). -/
lemma traj_succ {a : ℕ} (ha : 1 ≤ a) : traj a = a :: traj (radRemStar a) := by
  simp only [traj]
  have hd : depthStar (radRemStar a) + 1 = depthStar a := by
    rw [depthStar_succ a (by omega)]; ring
  rw [show depthStar a = depthStar (radRemStar a) + 1 by omega]
  simp [trajGo]

/-- 0 always belongs to traj(a). -/
lemma zero_mem_traj (a : ℕ) : 0 ∈ traj a := by
  induction a using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [traj_zero]
    · rw [traj_succ (by omega)]
      simp only [List.mem_cons]
      right
      exact ih (radRemStar n) (radRemStar_lt_self (by omega))

/-- a belongs to traj(a). -/
lemma self_mem_traj (a : ℕ) : a ∈ traj a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [traj_zero]
  · rw [traj_succ ha]; simp

/-- x ∈ traj(r★a) → x ∈ traj(a), for a ≥ 1. -/
lemma mem_traj_of_mem_traj_radRemStar {a : ℕ} (ha : 1 ≤ a) {x : ℕ}
    (hx : x ∈ traj (radRemStar a)) : x ∈ traj a := by
  rw [traj_succ ha]; simp [hx]

/-- Characterization of membership in traj. -/
lemma mem_traj_iff {a x : ℕ} :
    x ∈ traj a ↔ x = a ∨ (1 ≤ a ∧ x ∈ traj (radRemStar a)) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [traj_zero, List.mem_singleton]
    constructor
    · intro h; left; exact h
    · rintro (rfl | ⟨h, _⟩)
      · rfl
      · exact absurd h (by omega)
  · rw [traj_succ ha, List.mem_cons]
    constructor
    · rintro (rfl | hx)
      · left; rfl
      · right; exact ⟨ha, hx⟩
    · rintro (rfl | ⟨_, hx⟩)
      · left; rfl
      · right; exact hx

/-- If x ∈ traj(a) then depth★(x) ≤ depth★(a). -/
lemma depthStar_le_of_mem_traj {a x : ℕ} (hx : x ∈ traj a) : depthStar x ≤ depthStar a := by
  induction a using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [traj_zero] at hx; subst hx; simp
    · rw [traj_succ (by omega)] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_refl _
      · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih (radRemStar n)
            (radRemStar_lt_self (by omega)) hx)
            (depthStar_strict_mono (by omega)))

/-- In a trajectory, a node with the same depth★ is the same node. -/
lemma eq_of_mem_traj_same_depth {a x : ℕ} (hx : x ∈ traj a)
    (hd : depthStar x = depthStar a) : x = a := by
  induction a using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [traj_zero] at hx; exact hx
    · rw [traj_succ (by omega)] at hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exfalso
        have h1 := depthStar_le_of_mem_traj hx
        have h2 := depthStar_strict_mono (a := n) (by omega)
        omega

-- ================================================================
-- § 3. T-LCA: Lowest Common Ancestor (via depth★)
-- ================================================================

/-!
### LCA via search in the intersection

`lcaFind a b` descends from `a` toward 0, looking for the first node that belongs to `traj b`.
Since 0 ∈ traj(b) always, it terminates. Termination: the measure is `depthStar a`.
-/

/-- lcaFind: descends from a looking for the first node in traj(b). -/
def lcaFind (a b : ℕ) : ℕ :=
  if a ∈ traj b then a
  else if _ha : 1 ≤ a then lcaFind (radRemStar a) b
  else 0
termination_by depthStar a
decreasing_by
  exact depthStar_strict_mono _ha

#eval lcaFind 7 23   -- 7
#eval lcaFind 23 7   -- 7
#eval lcaFind 9 27   -- 0
#eval lcaFind 2 3    -- 2
#eval lcaFind 10 3   -- 1
#eval lcaFind 5 6    -- 1

/-- `lca a b` = LCA node (start from the deeper one). -/
def lca (a b : ℕ) : ℕ :=
  if depthStar a ≥ depthStar b then lcaFind a b else lcaFind b a

#eval lca 7 23   -- 7
#eval lca 23 7   -- 7
#eval lca 9 27   -- 0
#eval lca 2 3    -- 2
#eval lca 3 2    -- 2
#eval lca 10 3   -- 1

-- ================================================================
-- § 3b. Properties of lcaFind
-- ================================================================

/-- lcaFind a b ∈ traj(b). -/
lemma lcaFind_mem_traj_right (a b : ℕ) : lcaFind a b ∈ traj b := by
  induction a using Nat.strongRecOn with
  | ind n ih =>
    unfold lcaFind
    split_ifs with h1 h2
    · exact h1
    · exact ih (radRemStar n) (radRemStar_lt_self h2)
    · -- n = 0 and n ∉ traj(b): contradiction with zero_mem_traj
      push_neg at h2
      have : n = 0 := by omega
      subst this; exact absurd h1 (by simp [zero_mem_traj])

/-- lcaFind a b ∈ traj(a). -/
lemma lcaFind_mem_traj_left (a b : ℕ) : lcaFind a b ∈ traj a := by
  induction a using Nat.strongRecOn with
  | ind n ih =>
    unfold lcaFind
    split_ifs with h1 h2
    · exact self_mem_traj n
    · exact mem_traj_of_mem_traj_radRemStar h2 (ih (radRemStar n) (radRemStar_lt_self h2))
    · push_neg at h2; have : n = 0 := by omega
      subst this; simp [traj_zero]

/-- Strong version of lcaFind_max_depth with y free (for induction). -/
private lemma lcaFind_max_depth_aux (b : ℕ) :
    ∀ a y : ℕ, y ∈ traj a → y ∈ traj b → depthStar y ≤ depthStar (lcaFind a b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro y hya hyb
    unfold lcaFind
    split_ifs with h1 h2
    · exact depthStar_le_of_mem_traj hya
    · rw [mem_traj_iff] at hya
      rcases hya with rfl | ⟨_, hya_sub⟩
      · exact absurd hyb h1
      · exact ih (radRemStar a) (radRemStar_lt_self h2) y hya_sub hyb
    · push_neg at h2
      have ha0 : a = 0 := by omega
      subst ha0
      simp [traj_zero] at hya; subst hya
      simp [depthStar_zero]

/-- lcaFind maximizes depth★ among nodes of traj(a) that are also in traj(b). -/
lemma lcaFind_max_depth (a b x : ℕ) (hxa : x ∈ traj a) (hxb : x ∈ traj b) :
    depthStar x ≤ depthStar (lcaFind a b) :=
  lcaFind_max_depth_aux b a x hxa hxb

-- ================================================================
-- § 3c. Properties of lca
-- ================================================================

/-- lca a b ∈ traj(a). -/
lemma lca_mem_traj_left (a b : ℕ) : lca a b ∈ traj a := by
  simp only [lca]
  split_ifs with h
  · exact lcaFind_mem_traj_left a b
  · -- lcaFind b a ∈ traj(b): but we need ∈ traj(a)
    -- Is lcaFind b a a node in traj(a) ∩ traj(b)?
    -- lcaFind b a ∈ traj(b) and ∈ traj(a)? Not directly.
    -- lca when depth(b) > depth(a): we start from b, descend along b,
    -- and find the first node in traj(a); this node ∈ traj(a) ✓ and ∈ traj(b) ✓.
    exact lcaFind_mem_traj_right b a

/-- lca a b ∈ traj(b). -/
lemma lca_mem_traj_right (a b : ℕ) : lca a b ∈ traj b := by
  simp only [lca]
  split_ifs with h
  · exact lcaFind_mem_traj_right a b
  · exact lcaFind_mem_traj_left b a

/-- lca is maximal by depth★ among common nodes. -/
theorem lca_is_max {a b x : ℕ} (hxa : x ∈ traj a) (hxb : x ∈ traj b) :
    depthStar x ≤ depthStar (lca a b) := by
  simp only [lca]
  split_ifs with h
  · exact lcaFind_max_depth a b x hxa hxb
  · push_neg at h
    exact lcaFind_max_depth b a x hxb hxa

/-- Depth of lca ≤ depth of a. -/
lemma depthStar_lca_le_left (a b : ℕ) : depthStar (lca a b) ≤ depthStar a :=
  depthStar_le_of_mem_traj (lca_mem_traj_left a b)

/-- Depth of lca ≤ depth of b. -/
lemma depthStar_lca_le_right (a b : ℕ) : depthStar (lca a b) ≤ depthStar b :=
  depthStar_le_of_mem_traj (lca_mem_traj_right a b)

/-- Depth of lca(a,b) = depth of lca(b,a). -/
theorem lca_depth_comm (a b : ℕ) : depthStar (lca a b) = depthStar (lca b a) :=
  Nat.le_antisymm
    (lca_is_max (lca_mem_traj_right a b) (lca_mem_traj_left a b))
    (lca_is_max (lca_mem_traj_right b a) (lca_mem_traj_left b a))

/-- T-LCA-2: depth★(lca(a,b)) = depth★(a) ↔ a ∈ traj(b). -/
theorem lca_depth_eq_left_iff {a b : ℕ} :
    depthStar (lca a b) = depthStar a ↔ a ∈ traj b := by
  constructor
  · intro h
    have hlca_mem := lca_mem_traj_left a b
    have hlca_eq : lca a b = a := eq_of_mem_traj_same_depth hlca_mem h
    rw [← hlca_eq]
    exact lca_mem_traj_right a b
  · intro h
    apply Nat.le_antisymm
    · exact depthStar_lca_le_left a b
    · exact lca_is_max (self_mem_traj a) h

-- ================================================================
-- § 3d. Structural Lemma: Linearity of Trajectories
-- ================================================================

/-!
### Linearity of T★

The trajectories in T★ are linear (every node has a unique parent), hence
if x,y ∈ traj(a) and depth★(x) ≤ depth★(y), then x ∈ traj(y).

This is the crucial lemma for the triangle inequality and for the tree structure.
-/

private lemma mem_traj_depth_le_aux (a x y : ℕ)
    (hxa : x ∈ traj a) (hya : y ∈ traj a) (hd : depthStar x ≤ depthStar y) : x ∈ traj y := by
  revert x y
  induction a using Nat.strongRecOn with
  | ind n ih =>
    intro x y hxa hya hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [traj_zero] at hxa hya; subst hxa; subst hya; simp [traj_zero]
    · rw [traj_succ hn] at hxa hya
      simp only [List.mem_cons] at hxa hya
      rcases hya with heqyn | hya_sub
      · -- heqyn : y = n; goal: x ∈ traj y, i.e. x ∈ traj n
        rw [heqyn]
        rcases hxa with heqxn | hxa_sub
        · rw [heqxn]; exact self_mem_traj _
        · exact mem_traj_of_mem_traj_radRemStar (by omega) hxa_sub
      · rcases hxa with heqxn | hxa_sub
        · exfalso
          -- heqxn : x = n; goal: False from depth(y_sub) < depth(n) ≤ depth(x=n) ≤ depth(y)
          rw [heqxn] at hd
          have h1 := depthStar_le_of_mem_traj hya_sub
          have h2 := depthStar_strict_mono (a := n) (by omega)
          omega
        · exact ih (radRemStar n) (radRemStar_lt_self (by omega)) x y hxa_sub hya_sub hd

/-- If x, y ∈ traj(a) and depth★(x) ≤ depth★(y), then x ∈ traj(y). -/
theorem mem_traj_of_mem_traj_depth_le {a x y : ℕ}
    (hxa : x ∈ traj a) (hya : y ∈ traj a) (hd : depthStar x ≤ depthStar y) :
    x ∈ traj y :=
  mem_traj_depth_le_aux a x y hxa hya hd

-- ================================================================
-- § 4. T-METRIC: Metric on the Tree T★
-- ================================================================

/-- Distance in the tree T★ (in ℤ). -/
def treeDist (a b : ℕ) : ℤ :=
  (depthStar a : ℤ) + (depthStar b : ℤ) - 2 * (depthStar (lca a b) : ℤ)

/-- T-METRIC non-negative. -/
theorem treeDist_nonneg (a b : ℕ) : 0 ≤ treeDist a b := by
  simp only [treeDist]
  have h1 := depthStar_lca_le_left a b
  have h2 := depthStar_lca_le_right a b
  linarith

/-- T-METRIC Symmetry. -/
theorem treeDist_symm (a b : ℕ) : treeDist a b = treeDist b a := by
  simp only [treeDist, lca_depth_comm a b]; ring

/-- T-METRIC Definiteness: d(a,a) = 0. -/
theorem treeDist_self (a : ℕ) : treeDist a a = 0 := by
  simp only [treeDist]
  have h : depthStar (lca a a) = depthStar a :=
    lca_depth_eq_left_iff.mpr (self_mem_traj a)
  linarith

/-- T-METRIC Separation: d(a,b) = 0 ↔ depth★(lca) = depth★(a) ∧ depth★(lca) = depth★(b). -/
theorem treeDist_eq_zero_iff {a b : ℕ} :
    treeDist a b = 0 ↔
    (depthStar (lca a b) = depthStar a ∧ depthStar (lca a b) = depthStar b) := by
  simp only [treeDist]
  have h1 := depthStar_lca_le_left a b
  have h2 := depthStar_lca_le_right a b
  constructor
  · intro h; push_cast at h; constructor <;> omega
  · intro ⟨ha, hb⟩; linarith

/-- T-METRIC Node separation: d(a,b) = 0 → a ∈ traj(b) and b ∈ traj(a). -/
theorem treeDist_zero_iff_mutual_traj {a b : ℕ} :
    treeDist a b = 0 ↔ (a ∈ traj b ∧ b ∈ traj a) := by
  rw [treeDist_eq_zero_iff]
  constructor
  · intro ⟨ha, hb⟩
    exact ⟨lca_depth_eq_left_iff.mp ha, lca_depth_eq_left_iff.mp (by rw [lca_depth_comm]; exact hb)⟩
  · intro ⟨ha, hb⟩
    exact ⟨lca_depth_eq_left_iff.mpr ha, by rw [lca_depth_comm]; exact lca_depth_eq_left_iff.mpr hb⟩

/-- Transitivity of membership in traj: x ∈ traj y and y ∈ traj z → x ∈ traj z. -/
private lemma mem_traj_trans {x y z : ℕ} (hxy : x ∈ traj y) (hyz : y ∈ traj z) : x ∈ traj z := by
  induction z using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [traj_zero] at hyz; rw [hyz] at hxy; exact hxy
    · rw [mem_traj_iff] at hyz
      rcases hyz with heqyn | ⟨_, hy_sub⟩
      · rw [← heqyn]; exact hxy
      · exact mem_traj_of_mem_traj_radRemStar hn (ih (radRemStar n) (radRemStar_lt_self hn) hy_sub)

/-- T-TRIANGLE: d(a,c) ≤ d(a,b) + d(b,c).
    Proof: the min of depth★(lca(a,b)) and depth★(lca(b,c)) is ≤ depth★(lca(a,c)).
    The node with smaller depth★ is a common ancestor of a and c (via b). -/
theorem treeDist_triangle (a b c : ℕ) :
    treeDist a c ≤ treeDist a b + treeDist b c := by
  simp only [treeDist]
  -- Equivalent to: depth(lca(a,b)) + depth(lca(b,c)) ≤ depth(b) + depth(lca(a,c))
  -- Proved by showing: min(depth(lab), depth(lbc)) ≤ depth(lac)
  -- and: depth(lab) + depth(lbc) ≤ depth(b) + min(depth(lab), depth(lbc))
  -- The second is: max(depth(lab), depth(lbc)) ≤ depth(b), which holds by ≤ def.
  set lab := lca a b
  set lbc := lca b c
  set lac := lca a c
  have hlab_b := depthStar_lca_le_right a b
  have hlbc_b := depthStar_lca_le_left b c
  have hmax_le : max (depthStar lab) (depthStar lbc) ≤ depthStar b := by
    simp only [max_le_iff]; exact ⟨hlab_b, hlbc_b⟩
  -- Sufficient: min(depth(lab), depth(lbc)) ≤ depth(lac)
  suffices hmin : min (depthStar lab) (depthStar lbc) ≤ depthStar lac by
    have hmax_le' : max (depthStar lab) (depthStar lbc) ≤ depthStar b := hmax_le
    have hmm : min (depthStar lab) (depthStar lbc) + max (depthStar lab) (depthStar lbc) =
        depthStar lab + depthStar lbc := min_add_max _ _
    linarith [hmin, hmax_le', hmm,
              Nat.min_le_left (depthStar lab) (depthStar lbc),
              Nat.min_le_right (depthStar lab) (depthStar lbc),
              Nat.le_max_left (depthStar lab) (depthStar lbc),
              Nat.le_max_right (depthStar lab) (depthStar lbc),
              depthStar_lca_le_left a c, depthStar_lca_le_right a c]
  -- Case: the smaller of the two is a common ancestor of a and c
  by_cases hle : depthStar lab ≤ depthStar lbc
  · simp only [Nat.min_eq_left hle]
    -- lab has depth ≤ lbc. lab ∈ traj(b) and lbc ∈ traj(b), depth(lab) ≤ depth(lbc)
    -- → lab ∈ traj(lbc) (linearity of T★)
    have hlab_in_traj_lbc : lab ∈ traj lbc :=
      mem_traj_of_mem_traj_depth_le
        (lca_mem_traj_right a b)  -- lab ∈ traj(b)
        (lca_mem_traj_left b c)   -- lbc ∈ traj(b)
        hle
    -- lab ∈ traj(lbc) and lbc ∈ traj(c) → lab ∈ traj(c)
    have hlab_in_c : lab ∈ traj c :=
      mem_traj_trans hlab_in_traj_lbc (lca_mem_traj_right b c)
    apply lca_is_max (lca_mem_traj_left a b) hlab_in_c
  · -- ¬(depthStar lab ≤ depthStar lbc), i.e. depthStar lbc < depthStar lab
    have hlt' : depthStar lbc < depthStar lab := Nat.lt_of_not_le (by assumption)
    simp only [Nat.min_eq_right (Nat.le_of_lt hlt')]
    -- lbc has depth < lab. lbc ∈ traj(b) and lab ∈ traj(b), depth(lbc) < depth(lab)
    -- → lbc ∈ traj(lab)
    have hlbc_in_traj_lab : lbc ∈ traj lab :=
      mem_traj_of_mem_traj_depth_le
        (lca_mem_traj_left b c)   -- lbc ∈ traj(b)
        (lca_mem_traj_right a b)  -- lab ∈ traj(b)
        (Nat.le_of_lt hlt')
    -- lbc ∈ traj(lab) and lab ∈ traj(a) → lbc ∈ traj(a)
    have hlbc_in_a : lbc ∈ traj a :=
      mem_traj_trans hlbc_in_traj_lab (lca_mem_traj_left a b)
    apply lca_is_max hlbc_in_a (lca_mem_traj_right b c)

-- ================================================================
-- § 5. T-DIST-RADICE and T-PADRE
-- ================================================================

/-- Lemma: lca(a, 0) ∈ traj(0) = {0}, hence it is 0. -/
lemma lca_with_zero_is_zero (a : ℕ) : depthStar (lca a 0) = 0 := by
  have h := lca_mem_traj_right a 0
  simp [traj_zero] at h
  simp [h]

/-- T-DIST-RADICE: d(a, 0) = depth★(a). -/
theorem treeDist_zero_left (a : ℕ) : treeDist a 0 = (depthStar a : ℤ) := by
  simp only [treeDist, depthStar_zero, lca_with_zero_is_zero]
  push_cast; ring

/-- r★(a) ∈ traj(a) for a ≥ 1. -/
lemma radRemStar_mem_traj {a : ℕ} (ha : 1 ≤ a) : radRemStar a ∈ traj a :=
  mem_traj_of_mem_traj_radRemStar ha (self_mem_traj _)

/-- T-PADRE: depth★(lca(a, r★a)) = depth★(r★a) for a ≥ 1. -/
theorem lca_parent_depth {a : ℕ} (ha : 1 ≤ a) :
    depthStar (lca a (radRemStar a)) = depthStar (radRemStar a) :=
  lca_depth_comm a (radRemStar a) ▸
    lca_depth_eq_left_iff.mpr (radRemStar_mem_traj ha)

/-- T-PADRE: d(a, r★a) = 1 for a ≥ 1. -/
theorem treeDist_parent {a : ℕ} (ha : 1 ≤ a) :
    treeDist a (radRemStar a) = 1 := by
  simp only [treeDist]
  have hlca : depthStar (lca a (radRemStar a)) = depthStar (radRemStar a) :=
    lca_parent_depth ha
  have hsucc := depthStar_succ a (by omega)
  linarith

-- ================================================================
-- § 6. T-CLASS-TREE: Classes as Sets of Children
-- ================================================================

/-- T-CLASS-TREE: the Aod★ class of r = {x | r★(x) = r★(r)}. -/
theorem aodStarClass_eq_children (r : ℕ) :
    {x : ℕ | aodStarEquiv x r} = {x : ℕ | radRemStar x = radRemStar r} := by
  ext x; simp [aodStarEquiv]

/-- Version with canonical r: the class [r]★ = {children of r in T★}. -/
theorem aodStarClass_eq_children_canon {r : ℕ} (hcan : radRemStar r = r) :
    {x : ℕ | aodStarEquiv x r} = {x : ℕ | radRemStar x = r} := by
  ext x; simp [aodStarEquiv, hcan]

/-- Two siblings (same parent r★) have distance 2 in the tree if they are not equal.
    More precisely: d(a,b) = depth★(a) + depth★(b) - 2 * depth★(r★a). -/
theorem treeDist_siblings {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hclass : aodStarEquiv a b) (hab : a ≠ b) :
    depthStar (lca a b) = depthStar (radRemStar a) := by
  simp only [aodStarEquiv] at hclass
  apply Nat.le_antisymm
  · -- depth(lca) ≤ depth(r★a):
    -- If depth(lca) > depth(r★a), then lca has depth > depth(r★a).
    -- lca ∈ traj(a) = [a, r★a, ...], hence lca = a or lca ∈ traj(r★a).
    -- If lca ∈ traj(r★a), depth(lca) ≤ depth(r★a). Contradiction.
    -- Hence lca = a. Then a ∈ traj(b).
    -- Let depth(a) = depth(b) (same class → same depth via depthStar_eq_of_same_class).
    -- a ∈ traj(b) and depth(a) = depth(b) → a = b. Contradiction with hab.
    by_contra hc
    push_neg at hc
    -- depth(lca) > depth(r★a) → lca = a (the only node in traj(a) with depth ≥ depth(r★a)+1 = depth(a))
    have hlca_in_a := lca_mem_traj_left a b
    have hdepth_rra : depthStar (radRemStar a) + 1 = depthStar a := by
      rw [depthStar_succ a (by omega)]; ring
    have hlca_depth_a : depthStar (lca a b) = depthStar a := by
      have hle := depthStar_lca_le_left a b; omega
    have hlca_is_a : lca a b = a := eq_of_mem_traj_same_depth hlca_in_a hlca_depth_a
    -- Hence a ∈ traj(b)
    have ha_in_b : a ∈ traj b := hlca_is_a ▸ lca_mem_traj_right a b
    -- depth(a) = depth(b)
    have hdepth_eq : depthStar a = depthStar b :=
      depthStar_eq_of_same_class ha hb hclass
    -- a ∈ traj(b) and depth(a) = depth(b) → a = b
    exact hab (eq_of_mem_traj_same_depth ha_in_b hdepth_eq)
  · -- depth(r★a) ≤ depth(lca):
    -- r★a ∈ traj(a) (obvious) and r★a ∈ traj(b) (because r★(b) = r★(a) = tail of traj(b))
    apply lca_is_max
    · exact radRemStar_mem_traj ha
    · -- r★a = r★b ∈ traj(b)
      rw [hclass]
      exact radRemStar_mem_traj hb

/-- Corollary: treeDist of two siblings. -/
theorem treeDist_siblings_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hclass : aodStarEquiv a b) (hab : a ≠ b) :
    treeDist a b = 2 := by
  simp only [treeDist]
  rw [treeDist_siblings ha hb hclass hab]
  have hdepth_eq : depthStar a = depthStar b :=
    depthStar_eq_of_same_class ha hb (by simpa [aodStarEquiv] using hclass)
  have hdepth_rr : depthStar (radRemStar a) + 1 = depthStar a := by
    rw [depthStar_succ a (by omega)]; ring
  linarith

-- ================================================================
-- § 7. Corollaries: lca_self, lca_comm, true metric, ancestor-descendant
-- ================================================================

/-!
### § 7. Geometric corollaries

We complete the metric structure of the tree T★ with:
- `lca_self`: the LCA of a node with itself is the node itself
- `lca_of_traj`: if a ∈ traj(b) then lca(a,b) = a (the ancestor is the LCA)
- `lca_comm`: the LCA is commutative (not just the depth, but the node itself)
- `lca_zero_right`: lca(a, 0) = 0
- `treeDist_zero_iff_eq`: d(a,b) = 0 ↔ a = b (true metric, not pseudo-metric)
- `treeDist_pos_of_ne`: a ≠ b → 0 < d(a,b)
-/

/-- T-LCA-SELF: lca(a,a) = a. -/
theorem lca_self (a : ℕ) : lca a a = a := by
  apply eq_of_mem_traj_same_depth (lca_mem_traj_left a a)
  exact lca_depth_eq_left_iff.mpr (self_mem_traj a)

/-- T-LCA-ANCESTOR: If a ∈ traj(b), then lca(a,b) = a.
    The LCA of an ancestor with its descendant is the ancestor itself. -/
theorem lca_of_traj {a b : ℕ} (h : a ∈ traj b) : lca a b = a := by
  apply eq_of_mem_traj_same_depth (lca_mem_traj_left a b)
  exact lca_depth_eq_left_iff.mpr h

/-- T-LCA-COMM: lca(a,b) = lca(b,a). -/
theorem lca_comm (a b : ℕ) : lca a b = lca b a := by
  -- Both have the same depth (by lca_depth_comm).
  -- We show that lca(a,b) ∈ traj(lca(b,a)) and lca(b,a) ∈ traj(lca(a,b)),
  -- then by the linearity of the tree (same depth implies same node).
  apply eq_of_mem_traj_same_depth
  · -- lca(a,b) ∈ traj(lca(b,a)):
    -- lca(a,b) ∈ traj(a) and lca(a,b) ∈ traj(b);
    -- lca(b,a) ∈ traj(b) and lca(b,a) ∈ traj(a).
    -- Since both are in traj(a) ∩ traj(b) and depth(lca(a,b)) = depth(lca(b,a)),
    -- we use mem_traj_of_mem_traj_depth_le with ≤ in both directions.
    have hd := lca_depth_comm a b
    -- lca(a,b) ∈ traj(a), lca(b,a) ∈ traj(a), same depth → lca(a,b) ∈ traj(lca(b,a))
    exact mem_traj_of_mem_traj_depth_le
      (lca_mem_traj_left a b)
      (lca_mem_traj_right b a)
      (le_of_eq hd)
  · -- depth(lca(a,b)) = depth(lca(b,a))
    exact lca_depth_comm a b

/-- T-LCA-ZERO-RIGHT: lca(a, 0) = 0. -/
theorem lca_zero_right (a : ℕ) : lca a 0 = 0 := by
  apply eq_of_mem_traj_same_depth (lca_mem_traj_right a 0)
  simp [lca_with_zero_is_zero, depthStar_zero]

/-- Auxiliary lemma: if a ∈ traj(b) and b ∈ traj(a) then a = b. -/
private lemma eq_of_mutual_traj {a b : ℕ} (hab : a ∈ traj b) (hba : b ∈ traj a) : a = b := by
  have hd_ab : depthStar a ≤ depthStar b := depthStar_le_of_mem_traj hab
  have hd_ba : depthStar b ≤ depthStar a := depthStar_le_of_mem_traj hba
  have hd : depthStar a = depthStar b := Nat.le_antisymm hd_ab hd_ba
  exact eq_of_mem_traj_same_depth hab hd

/-- T-METRIC-TRUE: d(a,b) = 0 ↔ a = b.
    This theorem shows that treeDist is a true metric (not just a pseudo-metric). -/
theorem treeDist_zero_iff_eq {a b : ℕ} : treeDist a b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [treeDist_zero_iff_mutual_traj] at h
    exact eq_of_mutual_traj h.1 h.2
  · rintro rfl
    exact treeDist_self a

/-- T-METRIC-POS: a ≠ b → 0 < d(a,b). -/
theorem treeDist_pos_of_ne {a b : ℕ} (h : a ≠ b) : 0 < treeDist a b := by
  have := (treeDist_zero_iff_eq (a := a) (b := b)).not
  have hne : treeDist a b ≠ 0 := fun heq => h (treeDist_zero_iff_eq.mp heq)
  have hnn := treeDist_nonneg a b
  omega

/-- T-LCA-ZERO-LEFT: lca(0, a) = 0. -/
theorem lca_zero_left (a : ℕ) : lca 0 a = 0 := by
  rw [lca_comm]; exact lca_zero_right a

/-- T-DIST-ZERO-RIGHT: d(0, a) = depth★(a). -/
theorem treeDist_zero_right (a : ℕ) : treeDist 0 a = (depthStar a : ℤ) := by
  rw [treeDist_symm]; exact treeDist_zero_left a

/-- T-ANCESTOR-DIST: Se a ∈ traj(b), allora d(a,b) = depth★(b) - depth★(a). -/
theorem treeDist_of_traj {a b : ℕ} (h : a ∈ traj b) :
    treeDist a b = (depthStar b : ℤ) - (depthStar a : ℤ) := by
  simp only [treeDist]
  rw [lca_of_traj h]
  ring

end AodStarTree
