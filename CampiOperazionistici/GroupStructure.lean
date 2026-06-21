/-
  GroupStructure.lean — CampiOperazionistici
  Author: Alessandro Sgarbi — 2026-03-01
  Paper: §9 (Chapter Field Structure)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Field.TransferInstance
import CampiOperazionistici.CampiOperazionistici

namespace CampiOperazionistici

/-! ## 1. Primitives -/

/- irootAux, irootN, radRem: imported from CampiOperazionistici.CampiOperazionistici
def irootAux (n a : ℕ) : ℕ → ℕ
  | 0     => 0
  | k + 1 => if (k + 1) ^ n ≤ a then k + 1 else irootAux n a k

def irootN (n a : ℕ) : ℕ := if n = 0 then 1 else irootAux n a a
def radRem (n a : ℕ) : ℕ := a - (irootN n a) ^ n
-/

-- capGap is not in CampiOperazionistici.lean (there it is called `gap`)
def capGap (n k : ℕ) : ℕ := (k + 1) ^ n - k ^ n

#eval capGap 2 1  -- 3
#eval capGap 3 1  -- 7
#eval capGap 3 2  -- 19
#eval capGap 4 1  -- 15

/- Lemmas on irootAux/irootN already in CampiOperazionistici.lean, commented out to avoid conflicts
lemma irootAux_pow_le (n a b : ℕ) (hn : n ≠ 0) : (irootAux n a b) ^ n ≤ a := by
  induction b with
  | zero      => simp [irootAux, Nat.zero_pow (Nat.pos_of_ne_zero hn)]
  | succ k ih => simp only [irootAux]; split_ifs with h; exact h; exact ih

lemma irootAux_lt_succ_pow (n a b : ℕ) (_hn : n ≠ 0) (hb : a < (b+1)^n) :
    a < (irootAux n a b + 1) ^ n := by
  induction b with
  | zero      => simp [irootAux]; simpa using hb
  | succ k ih => simp only [irootAux]; split_ifs with h; simpa using hb; push_neg at h; exact ih h

theorem irootN_pow_le (n a : ℕ) (hn : n ≠ 0) : (irootN n a) ^ n ≤ a := by
  simp [irootN, hn]; exact irootAux_pow_le n a a hn

theorem irootN_lt_succ_pow (n a : ℕ) (hn : n ≠ 0) : a < (irootN n a + 1) ^ n := by
  simp [irootN, hn]
  exact irootAux_lt_succ_pow n a a hn
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_self_pow hn _))

lemma irootN_mono (n a b : ℕ) (hn : n ≠ 0) (hab : a ≤ b) : irootN n a ≤ irootN n b := by
  by_contra h; push_neg at h
  linarith [irootN_pow_le n b hn, irootN_lt_succ_pow n b hn, irootN_pow_le n a hn,
            Nat.pow_le_pow_left h n]
-/

lemma capGap_pos (n k : ℕ) (hn : n ≠ 0) : 0 < capGap n k := by
  simp only [capGap]
  have : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn
  omega

lemma irootN_perfect (n k : ℕ) (hn : n ≠ 0) : irootN n (k ^ n) = k := by
  apply Nat.le_antisymm
  · by_contra h; push_neg at h
    linarith [irootN_pow_le n (k^n) hn, Nat.pow_le_pow_left h n,
              Nat.pow_lt_pow_left (Nat.lt_succ_self k) hn]
  · by_contra hc; push_neg at hc
    linarith [irootN_lt_succ_pow n (k^n) hn, Nat.pow_le_pow_left hc n]

lemma sum_in_chapter' (n k r : ℕ) (hn : n ≠ 0) (hr : r < capGap n k) :
    irootN n (k^n + r) = k := by
  apply Nat.le_antisymm
  · by_contra h; push_neg at h
    linarith [irootN_pow_le n (k^n+r) hn, Nat.pow_le_pow_left h n,
              show k^n + r < (k+1)^n by simp [capGap] at hr; omega]
  · calc k = irootN n (k^n)     := (irootN_perfect n k hn).symm
         _ ≤ irootN n (k^n + r) := irootN_mono n _ _ hn (Nat.le_add_right _ _)

/-! ## 2. capAdd -/

def capAdd (n k : ℕ) (hn : n ≠ 0) : Fin (capGap n k) → Fin (capGap n k) → Fin (capGap n k) :=
  fun r s => ⟨(k^n + r.val + s.val) % capGap n k, Nat.mod_lt _ (capGap_pos n k hn)⟩

#eval! (capAdd 3 1 (by norm_num) ⟨3, by norm_num [capGap]⟩ ⟨4, by norm_num [capGap]⟩).val
#eval! (capAdd 3 2 (by norm_num) ⟨5, by norm_num [capGap]⟩ ⟨8, by norm_num [capGap]⟩).val

/-! ## 3. Identity element -/

def capNeutral (n k : ℕ) (hn : n ≠ 0) : Fin (capGap n k) :=
  ⟨(capGap n k - k^n % capGap n k) % capGap n k, Nat.mod_lt _ (capGap_pos n k hn)⟩

#eval! (capNeutral 2 1 (by norm_num)).val  -- 2
#eval! (capNeutral 3 1 (by norm_num)).val  -- 6
#eval! (capNeutral 3 2 (by norm_num)).val  -- 11

private lemma shift_neutral_zero (n k : ℕ) (hn : n ≠ 0) :
    (k^n + (capGap n k - k^n % capGap n k) % capGap n k) % capGap n k = 0 := by
  set g := capGap n k
  have hg : 0 < g := capGap_pos n k hn
  have hm : k^n % g < g := Nat.mod_lt _ hg
  have hdiv : k^n = g * (k^n / g) + k^n % g := (Nat.div_add_mod _ _).symm
  rcases Nat.eq_zero_or_pos (k^n % g) with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    rw [show k^n = g * (k^n / g) by linarith]
    exact Nat.mul_mod_right g _
  · have hlt : g - k^n % g < g := Nat.sub_lt hg h
    rw [Nat.mod_eq_of_lt hlt]
    have heq : k^n + (g - k^n % g) = g * (k^n / g + 1) := by
      have := Nat.sub_add_cancel (Nat.le_of_lt hm); linarith
    rw [heq, Nat.mul_mod_right]

theorem capNeutral_add (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capAdd n k hn (capNeutral n k hn) r = r := by
  simp only [capAdd, capNeutral, Fin.ext_iff]
  have h0 := shift_neutral_zero n k hn
  have hr := r.isLt
  rw [show k^n + (capGap n k - k^n % capGap n k) % capGap n k + r.val =
          (k^n + (capGap n k - k^n % capGap n k) % capGap n k) + r.val by ring,
      Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod_of_dvd _ (dvd_refl _),
      Nat.mod_eq_of_lt hr]

theorem capAdd_neutral (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capAdd n k hn r (capNeutral n k hn) = r := by
  simp only [capAdd, capNeutral, Fin.ext_iff]
  have h0 := shift_neutral_zero n k hn
  have hr := r.isLt
  rw [show k^n + r.val + (capGap n k - k^n % capGap n k) % capGap n k =
          (k^n + (capGap n k - k^n % capGap n k) % capGap n k) + r.val by ring,
      Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod_of_dvd _ (dvd_refl _),
      Nat.mod_eq_of_lt hr]

/-! ## 4. Commutativity and Associativity -/

theorem capAdd_comm' (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    capAdd n k hn r s = capAdd n k hn s r := by
  simp only [capAdd, Fin.ext_iff]; congr 1; omega

private lemma add_mod_mid_left (a b c g : ℕ) :
    (a + b % g + c) % g = (a + b + c) % g := by
  rw [Nat.add_mod (a + b % g) c, Nat.add_mod a (b % g),
      Nat.mod_mod_of_dvd _ (dvd_refl g), ← Nat.add_mod a b, ← Nat.add_mod (a + b) c]

theorem capAdd_assoc' (n k : ℕ) (hn : n ≠ 0) (r s t : Fin (capGap n k)) :
    capAdd n k hn (capAdd n k hn r s) t = capAdd n k hn r (capAdd n k hn s t) := by
  apply Fin.ext
  simp only [capAdd, Fin.val_mk]
  have lhs : (k^n + (k^n + r.val + s.val) % capGap n k + t.val) % capGap n k =
             (2 * k^n + r.val + s.val + t.val) % capGap n k := by
    rw [add_mod_mid_left]; congr 1; ring
  have rhs : (k^n + r.val + (k^n + s.val + t.val) % capGap n k) % capGap n k =
             (2 * k^n + r.val + s.val + t.val) % capGap n k := by
    rw [show k^n + r.val + (k^n + s.val + t.val) % capGap n k =
            r.val + (k^n + s.val + t.val) % capGap n k + k^n by ring,
        add_mod_mid_left]; congr 1; ring
  rw [lhs, ← rhs]

/-! ## 5. Inverse -/

def capInv (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) : Fin (capGap n k) :=
  ⟨(2 * capGap n k - (2 * k^n + r.val) % capGap n k) % capGap n k,
   Nat.mod_lt _ (capGap_pos n k hn)⟩

#eval! (capInv 3 1 (by norm_num) ⟨3, by norm_num [capGap]⟩).val
#eval! (capAdd 3 1 (by norm_num) ⟨3, by norm_num [capGap]⟩ ⟨2, by norm_num [capGap]⟩).val
#eval! (capNeutral 3 1 (by norm_num)).val

-- (2g - x%g) % g = (g - x%g) % g
private lemma two_mul_sub_mod (x g : ℕ) (hg : 0 < g) :
    (2 * g - x % g) % g = (g - x % g) % g := by
  have hx : x % g < g := Nat.mod_lt _ hg
  rcases Nat.eq_zero_or_pos (x % g) with h | h
  · simp [h, Nat.mod_self]
  · have hlt : g - x % g < g := Nat.sub_lt hg h
    have heq : 2 * g - x % g = g + (g - x % g) := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hlt]
    exact Nat.mod_eq_of_lt hlt

-- inv_sum_mod: (k^n + rv + (g - (2k^n+rv)%g)) % g = (g - k^n%g) % g
-- Proof by 4 cases on (m₁ = k^n%g, m₂ = (2k^n+rv)%g).
-- In each case we rewrite the sum in the form g*q + (g-m₁) and apply
-- Nat.add_mul_mod_self_left + Nat.mod_eq_of_lt — without ever calling omega
-- on products or subtractions of quotients.
private lemma inv_sum_mod (n k : ℕ) (hn : n ≠ 0) (rv : ℕ) :
    (k^n + rv + (capGap n k - (2 * k^n + rv) % capGap n k)) % capGap n k =
    (capGap n k - k^n % capGap n k) % capGap n k := by
  set g := capGap n k
  have hg  : 0 < g := capGap_pos n k hn
  have hm₁ : k^n % g < g        := Nat.mod_lt _ hg
  have hm₂ : (2*k^n+rv) % g < g := Nat.mod_lt _ hg
  -- Euclidean equations: we use them to construct exact rewrites
  set q₁ := k^n / g
  set q₂ := (2*k^n+rv) / g
  set m₁ := k^n % g
  set m₂ := (2*k^n+rv) % g
  have hd₁ : k^n     = g * q₁ + m₁ := (Nat.div_add_mod _ _).symm
  have hd₂ : 2*k^n+rv = g * q₂ + m₂ := (Nat.div_add_mod _ _).symm
  -- From the Euclidean equation: rv = g*q₂ + m₂ - 2*(g*q₁+m₁)
  --   = g*(q₂-2*q₁) + (m₂-2*m₁)   (over ℤ; over ℕ we use the fact that the equality holds)
  -- Hence: k^n + rv + g - m₂
  --   = g*q₁+m₁ + [g*q₂+m₂-2*g*q₁-2*m₁] + g - m₂
  --   = g*(q₂-q₁+1) + (m₁-m₂+m₂-m₁) = g*(q₂-q₁+1)  when m₁≤m₂
  -- But m₁≤m₂ does not always hold; the correct formula is:
  --   k^n + rv + (g-m₂) = g*(q₂-q₁+1) + (g-m₁) - g   if m₁ < m₂
  --                      = g*(q₂-q₁)   + (g-m₁)         always!
  -- Check: g*q₁+m₁ + g*q₂+m₂-2*g*q₁-2*m₁ + g-m₂ = g*(q₂-q₁+1)-m₁
  --   if q₂≥q₁ and 2q₁≤q₂+1 — guaranteed by 2k^n+rv≥2k^n=2(g*q₁+m₁)≥2g*q₁.
  -- The final form is always: g*(q₂-q₁) + (g-m₁)
  -- CASE m₂>0: g-m₂ < g, RHS = g-m₁
  -- CASE m₂=0: g-m₂ = g, LHS = k^n+rv+g, RHS = (g-m₁)%g
  -- Useful shortcut: (g * q + r) % g = r % g  when the order is g*q+r
  -- Mathlib has Nat.add_mul_mod_self_left : (a + b*c) % b = a % b  (b*c on the right)
  -- For (g*q + r) % g we use: rw [show g*q + r = r + g*q by ring, Nat.add_mul_mod_self_left]
  rcases Nat.eq_zero_or_pos m₁ with h₁ | h₁
  · -- m₁ = 0 → RHS = g%g = 0
    simp only [h₁, Nat.sub_zero, Nat.mod_self]
    rcases Nat.eq_zero_or_pos m₂ with h₂ | h₂
    · -- m₂ = 0: LHS = (k^n+rv+g)%g = 0
      simp only [h₂, Nat.sub_zero]
      have hk  : k^n      = g * q₁ := by linarith [hd₁, h₁]
      have hk2 : 2*k^n+rv = g * q₂ := by linarith [hd₂, h₂]
      have hq  : q₂ ≥ q₁ := by nlinarith
      have hrw : k^n + rv + g = g * (q₂ - q₁ + 1) := by
        have := Nat.sub_add_cancel hq; nlinarith
      rw [hrw, Nat.mul_mod_right]
    · -- m₂ > 0: (k^n+rv+(g-m₂)) % g = 0
      have hlt₂ : g - m₂ < g := Nat.sub_lt hg h₂
      have hk  : k^n = g * q₁       := by linarith [hd₁, h₁]
      have hk2 : g * q₂ + m₂ = 2 * k^n + rv := by linarith [hd₂]
      have hq  : q₂ ≥ q₁            := by nlinarith
      set d := q₂ - q₁ with hd_def
      have hd_add : d + q₁ = q₂ := Nat.sub_add_cancel hq
      -- g*d is linear with respect to g*q₁ and g*q₂ via this identity:
      have hgd : g * d + g * q₁ = g * q₂ := by
        calc g * d + g * q₁ = g * (d + q₁) := (Nat.mul_add g d q₁).symm
          _                 = g * q₂       := by rw [hd_add]
      -- Now k^n = g*q₁ and g*d+g*q₁ = g*q₂ → k^n+rv+(g-m₂) = g*d+g
      -- rv = g*q₂+m₂-2*g*q₁ (from hk2 and hk); substituting: everything is linear
      have hrw : k^n + rv + (g - m₂) = g * d + g := by
        -- Additive form without ℕ subtractions: 2*g*q₁ + rv = g*q₂ + m₂
        have hadd : 2 * (g * q₁) + rv = g * q₂ + m₂ := by linarith
        -- g - m₂ + m₂ = g  (m₂ < g guarantees m₂ ≤ g)
        have hgm : g - m₂ + m₂ = g := Nat.sub_add_cancel (Nat.le_of_lt hm₂)
        linarith
      rw [hrw, show g * d + g = g * (d + 1) by ring, Nat.mul_mod_right]
  · -- m₁ > 0 → RHS = g-m₁ (< g)
    have hlt₁ : g - m₁ < g := Nat.sub_lt hg h₁
    rw [Nat.mod_eq_of_lt hlt₁]
    rcases Nat.eq_zero_or_pos m₂ with h₂ | h₂
    · -- m₂ = 0: (k^n+rv+g) % g = g-m₁
      simp only [h₂, Nat.sub_zero]
      have hq : q₂ ≥ q₁ := by
        have hk2 : g * q₂ = 2 * k^n + rv := by linarith [hd₂, h₂]
        have hk1 : g * q₁ ≤ k^n          := by linarith [hd₁]
        nlinarith
      set d := q₂ - q₁ with hd_def
      have hd_add : d + q₁ = q₂ := Nat.sub_add_cancel hq
      have hgd : g * d + g * q₁ = g * q₂ := by
        calc g * d + g * q₁ = g * (d + q₁) := (Nat.mul_add g d q₁).symm
          _                 = g * q₂       := by rw [hd_add]
      have hk2 : 2 * k^n + rv = g * q₂ := by linarith [hd₂, h₂]
      -- k^n = g*q₁+m₁ (hd₁), 2k^n+rv = g*q₂ → rv = g*q₂-2*g*q₁-2*m₁
      -- k^n+rv+g = g*q₁+m₁+rv+g; substituting rv:
      --          = g*q₁+m₁+(g*q₂-2*g*q₁-2*m₁)+g = g*q₂-g*q₁+g-m₁ = g*d+g-m₁ = (g-m₁)+g*d
      have hrw : k^n + rv + g = (g - m₁) + g * d := by
        have hadd : 2 * k^n + rv = g * q₂ := by linarith [hd₂, h₂]
        have hgm₁ : g - m₁ + m₁ = g := Nat.sub_add_cancel (Nat.le_of_lt hm₁)
        linarith
      rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt₁]
    · -- m₂ > 0: (k^n+rv+(g-m₂)) % g = g-m₁
      have hlt₂ : g - m₂ < g := Nat.sub_lt hg h₂
      have hq : q₂ ≥ q₁ := by
        have h2k : g * q₂ + m₂ = 2 * (g * q₁ + m₁) + rv := by linarith [hd₁, hd₂]
        nlinarith
      set d := q₂ - q₁ with hd_def
      have hd_add : d + q₁ = q₂ := Nat.sub_add_cancel hq
      have hgd : g * d + g * q₁ = g * q₂ := by
        calc g * d + g * q₁ = g * (d + q₁) := (Nat.mul_add g d q₁).symm
          _                 = g * q₂       := by rw [hd_add]
      -- k^n = g*q₁+m₁, 2k^n+rv = g*q₂+m₂ → rv = g*q₂+m₂-2*g*q₁-2*m₁
      -- k^n+rv+(g-m₂) = g*q₁+m₁+rv+g-m₂
      --               = g*q₁+m₁+(g*q₂+m₂-2*g*q₁-2*m₁)+g-m₂
      --               = g*q₂-g*q₁+g-m₁ = g*d+g-m₁ = (g-m₁)+g*d
      have hrw : k^n + rv + (g - m₂) = (g - m₁) + g * d := by
        have hadd : 2 * k^n + rv = g * q₂ + m₂ := by linarith [hd₂]
        have hgm₁ : g - m₁ + m₁ = g := Nat.sub_add_cancel (Nat.le_of_lt hm₁)
        have hgm₂ : g - m₂ + m₂ = g := Nat.sub_add_cancel (Nat.le_of_lt hm₂)
        linarith
      rw [hrw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt₁]

theorem capAdd_right_inv (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capAdd n k hn r (capInv n k hn r) = capNeutral n k hn := by
  apply Fin.ext
  simp only [capAdd, capInv, capNeutral, Fin.val_mk]
  have hg := capGap_pos n k hn
  rw [two_mul_sub_mod _ _ hg]
  rcases Nat.eq_zero_or_pos ((2 * k^n + r.val) % capGap n k) with h | h
  · -- m₂ = 0: (g - 0)%g = g%g = 0, goal: (k^n + r + 0) % g = (g - k^n%g) % g
    rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    -- inv_sum_mod (with m₂=0) gives: (k^n + r + g) % g = (g - k^n%g) % g
    -- but (k^n + r + g) % g = (k^n + r) % g  via Nat.add_mod_right
    have key := inv_sum_mod n k hn r.val
    simp only [h, Nat.sub_zero] at key
    rwa [Nat.add_mod_right] at key
  · -- m₂ > 0: (g - m₂)%g = g - m₂  (via Nat.mod_eq_of_lt)
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hg h)]
    exact inv_sum_mod n k hn r.val

theorem capInv_add (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capAdd n k hn (capInv n k hn r) r = capNeutral n k hn :=
  capAdd_comm' n k hn _ r ▸ capAdd_right_inv n k hn r

/-! ## 6. Main theorem (bundled) -/

theorem capAdd_isGroup (n k : ℕ) (hn : n ≠ 0) :
    (∀ r s t : Fin (capGap n k),
        capAdd n k hn (capAdd n k hn r s) t = capAdd n k hn r (capAdd n k hn s t)) ∧
    (∀ r : Fin (capGap n k), capAdd n k hn (capNeutral n k hn) r = r) ∧
    (∀ r : Fin (capGap n k), capAdd n k hn (capInv n k hn r) r = capNeutral n k hn) ∧
    (∀ r s : Fin (capGap n k), capAdd n k hn r s = capAdd n k hn s r) :=
  ⟨capAdd_assoc' n k hn, capNeutral_add n k hn, capInv_add n k hn, capAdd_comm' n k hn⟩

/-! ## 7. Homomorphism into ZMod -/

def toZMod (n k : ℕ) (r : Fin (capGap n k)) : ZMod (capGap n k) :=
  (r.val : ZMod (capGap n k)) + (k^n : ℕ)

private lemma natCast_mod (a g : ℕ) : (a % g : ZMod g) = (a : ZMod g) := by
  conv_rhs => rw [← Nat.div_add_mod a g]
  push_cast; simp [mul_comm]

theorem toZMod_add (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    toZMod n k (capAdd n k hn r s) = toZMod n k r + toZMod n k s := by
  simp only [toZMod, capAdd]; rw [natCast_mod]; push_cast; ring

/-! ## 8. Connection with radRem -/

theorem capAdd_eq_radRem_noOverflow (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k))
    (hno : k^n + r.val + s.val < capGap n k) :
    (capAdd n k hn r s).val = radRem n (k^n + r.val + (k^n + s.val)) := by
  simp only [capAdd, radRem]
  have hbound : k^n + r.val + (k^n + s.val) < (k+1)^n := by simp [capGap] at hno; omega
  have hroot : irootN n (k^n + r.val + (k^n + s.val)) = k := by
    apply Nat.le_antisymm
    · by_contra h; push_neg at h
      linarith [irootN_pow_le n (k^n + r.val + (k^n + s.val)) hn, Nat.pow_le_pow_left h n]
    · calc k = irootN n (k^n) := (irootN_perfect n k hn).symm
           _ ≤ _               := irootN_mono n _ _ hn (by omega)
  rw [hroot, show k^n + r.val + (k^n + s.val) - k^n = k^n + r.val + s.val by omega,
      Nat.mod_eq_of_lt hno]

/-
  ## Note on capAdd_eq_radRem_mod

  The lemma without hypotheses is FALSE: counterexample n=2, k=2, r=4, s=4
  gives LHS=2 and RHS=0. Two conditions are needed:
  · h2k  : 2*k^n < (k+1)^n  ("stable" chapter)
  · hsum : k^n + r + s < capGap n k  (local no-overflow)

  Under these hypotheses, landingCongruence_diag (imported) gives:
    radRem n (k^n + r + (k^n + s)) = k^n + r + s
  and the result follows immediately from the definition of capAdd.

  The no-overflow case for capAdd is proved in capAdd_eq_radRem_noOverflow.
-/
lemma capAdd_eq_radRem_mod (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k))
    (h2k  : 2 * k ^ n < (k + 1) ^ n)
    (hsum : k ^ n + r.val + s.val < capGap n k) :
    (capAdd n k hn r s).val =
    radRem n (k ^ n + r.val + (k ^ n + s.val)) % capGap n k := by
  -- capGap and gap have the same definition (different names, different namespace)
  have hcg : capGap n k = gap n k := by simp [capGap, gap]
  -- convert the hypotheses on Fin into ones about gap (required by landingCongruence_diag)
  have hr'   : r.val < gap n k                  := by rw [← hcg]; exact r.isLt
  have hs'   : s.val < gap n k                  := by rw [← hcg]; exact s.isLt
  have hsum' : k ^ n + r.val + s.val < gap n k := by rw [← hcg]; exact hsum
  -- the diagonal theorem provides the exact equality
  rw [landingCongruence_diag n k r.val s.val hn h2k hr' hs' hsum']
  -- what remains: (capAdd …).val = (k^n + r + s) % capGap n k, true by definition
  simp [capAdd]

/-! ## 9. Stability condition -/

def isStableChapter (n k : ℕ) : Prop := 2 * k^n < (k+1)^n

#eval 2 * 1^2 < 2^2   -- true
#eval 2 * 2^2 < 3^2   -- false
#eval 2 * 3^3 < 4^3   -- true
#eval 2 * 4^3 < 5^3   -- false

/-! ## 10. AddCommGroup (def, not instance — depends on hn : n ≠ 0) -/

-- Since hn : n ≠ 0 is not a typeclass, we produce an explicit term
-- rather than a global instance. Whoever wants to use it uses `letI := capAddCommGroup n k hn`.

private def capNsmul (n k : ℕ) (hn : n ≠ 0) : ℕ → Fin (capGap n k) → Fin (capGap n k)
  | 0,     _ => capNeutral n k hn
  | m + 1, a => capAdd n k hn (capNsmul n k hn m a) a

def capAddCommGroup (n k : ℕ) (hn : n ≠ 0) : AddCommGroup (Fin (capGap n k)) where
  add a b         := capAdd n k hn a b
  zero            := capNeutral n k hn
  neg a           := capInv n k hn a
  sub a b         := capAdd n k hn a (capInv n k hn b)
  add_assoc       := capAdd_assoc' n k hn
  zero_add        := capNeutral_add n k hn
  add_zero        := capAdd_neutral n k hn
  neg_add_cancel  := capInv_add n k hn
  add_comm        := capAdd_comm' n k hn
  sub_eq_add_neg  := fun _ _ => rfl
  nsmul m a       := capNsmul n k hn m a
  nsmul_zero _    := rfl
  nsmul_succ _ _  := rfl
  zsmul z a       := match z with
    | .ofNat m    => capNsmul n k hn m a
    | .negSucc m  => capInv n k hn (capNsmul n k hn (m + 1) a)
  zsmul_zero' _   := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _  := rfl

/-! ## 11. capMul — chapter multiplicative operation -/

/-- Radical projection of the product in chapter k:
    capMul r s := ((k^n + r) * (k^n + s) - k^n) % g
    Same structure as capAdd with ★ = × instead of +. -/
def capMul (n k : ℕ) (hn : n ≠ 0) : Fin (capGap n k) → Fin (capGap n k) → Fin (capGap n k) :=
  fun r s => ⟨((k^n + r.val) * (k^n + s.val) - k^n) % capGap n k,
              Nat.mod_lt _ (capGap_pos n k hn)⟩

#eval! (capMul 3 1 (by norm_num) ⟨3, by norm_num [capGap]⟩ ⟨4, by norm_num [capGap]⟩).val
#eval! (capMul 2 1 (by norm_num) ⟨0, by norm_num [capGap]⟩ ⟨1, by norm_num [capGap]⟩).val

/-! ## 12. toZMod_mul and injectivity -/

-- The product (kn+r)*(kn+s) ≥ kn: necessary for Nat.cast_sub
private lemma capMul_abs_ge (n k : ℕ) (r s : Fin (capGap n k)) :
    k^n ≤ (k^n + r.val) * (k^n + s.val) := by
  have h := Nat.zero_le (k ^ n * s.val + k ^ n * r.val + r.val * s.val + k ^ n * k ^ n)
  nlinarith [Nat.le_add_right (k ^ n) r.val]

theorem toZMod_mul (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    toZMod n k (capMul n k hn r s) = toZMod n k r * toZMod n k s := by
  simp only [toZMod, capMul]
  rw [natCast_mod, Nat.cast_sub (capMul_abs_ge n k r s)]
  push_cast; ring

theorem toZMod_injective (n k : ℕ) (_hn : n ≠ 0) (r s : Fin (capGap n k))
    (h : toZMod n k r = toZMod n k s) : r = s := by
  apply Fin.ext
  simp only [toZMod] at h
  have heq : (r.val : ZMod (capGap n k)) = s.val := add_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff] at heq
  simp only [Nat.ModEq, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] at heq
  exact heq

/-! ## 13. Commutativity, Associativity, Multiplicative identity, Distributivity -/

theorem capMul_comm (n k : ℕ) (hn : n ≠ 0) (r s : Fin (capGap n k)) :
    capMul n k hn r s = capMul n k hn s r := by
  apply Fin.ext; simp only [capMul]
  congr 1
  rw [mul_comm]

theorem capMul_assoc (n k : ℕ) (hn : n ≠ 0) (r s t : Fin (capGap n k)) :
    capMul n k hn (capMul n k hn r s) t = capMul n k hn r (capMul n k hn s t) := by
  apply toZMod_injective n k hn
  simp only [toZMod_mul]; ring

/-- Multiplicative identity: the local address r such that k^n + r ≡ 1 (mod g). -/
def capMulNeutral (n k : ℕ) (hn : n ≠ 0) : Fin (capGap n k) :=
  ⟨(capGap n k + 1 - k^n % capGap n k) % capGap n k,
   Nat.mod_lt _ (capGap_pos n k hn)⟩

#eval! (capMulNeutral 2 1 (by norm_num)).val   -- 0 (g=3, kn=1, (3+1-1)%3 = 0? 1%3=1→e=0)
#eval! (capMulNeutral 3 1 (by norm_num)).val   -- 0 (g=7, kn=1, (7+1-1)%7=0)
#eval! (capMulNeutral 3 2 (by norm_num)).val   -- (19+1-8%19)%19 = (20-8)%19=12

private lemma toZMod_capMulNeutral (n k : ℕ) (hn : n ≠ 0) :
    toZMod n k (capMulNeutral n k hn) = 1 := by
  set g := capGap n k
  have hg : 0 < g := capGap_pos n k hn
  have hm : k^n % g < g := Nat.mod_lt _ hg
  simp only [toZMod, capMulNeutral, natCast_mod]
  -- goal: ((g + 1 - k^n % g : ℕ) : ZMod g) + (k^n : ZMod g) = 1
  rw [Nat.cast_sub (by omega : k^n % g ≤ g + 1),
      Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add, natCast_mod]
  ring

theorem capMul_neutral_left (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capMul n k hn (capMulNeutral n k hn) r = r := by
  apply toZMod_injective n k hn
  rw [toZMod_mul, toZMod_capMulNeutral, one_mul]

theorem capMul_distrib_left (n k : ℕ) (hn : n ≠ 0) (r s t : Fin (capGap n k)) :
    capMul n k hn r (capAdd n k hn s t) =
    capAdd n k hn (capMul n k hn r s) (capMul n k hn r t) := by
  apply toZMod_injective n k hn
  simp only [toZMod_mul, toZMod_add]; ring

/-! ## 14. Surjectivity and bijectivity of toZMod -/

-- Explicit inverse of toZMod: given z : ZMod g, fromZMod z has val = (z.val + g - k^n%g) % g.
-- This makes toZModEquiv computable (no Classical.choice).

private def fromZMod (n k : ℕ) (hn : n ≠ 0) (z : ZMod (capGap n k)) : Fin (capGap n k) :=
  ⟨(ZMod.val z + capGap n k - k^n % capGap n k) % capGap n k,
   Nat.mod_lt _ (capGap_pos n k hn)⟩

private lemma toZMod_fromZMod (n k : ℕ) (hn : n ≠ 0) (z : ZMod (capGap n k)) :
    toZMod n k (fromZMod n k hn z) = z := by
  have hg : 0 < capGap n k := capGap_pos n k hn
  have hm : k^n % capGap n k < capGap n k := Nat.mod_lt _ hg
  haveI : NeZero (capGap n k) := ⟨by omega⟩
  simp only [toZMod, fromZMod, natCast_mod]
  rw [Nat.cast_sub (by omega : k^n % capGap n k ≤ ZMod.val z + capGap n k),
      Nat.cast_add, ZMod.natCast_self, add_zero, natCast_mod, ZMod.natCast_val]
  simp [sub_add_cancel]

private lemma fromZMod_toZMod (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    fromZMod n k hn (toZMod n k r) = r :=
  toZMod_injective n k hn _ _ (toZMod_fromZMod n k hn (toZMod n k r))

theorem toZMod_surjective (n k : ℕ) (hn : n ≠ 0) : Function.Surjective (toZMod n k) :=
  fun z => ⟨fromZMod n k hn z, toZMod_fromZMod n k hn z⟩

theorem toZMod_bijective (n k : ℕ) (hn : n ≠ 0) : Function.Bijective (toZMod n k) :=
  ⟨toZMod_injective n k hn, toZMod_surjective n k hn⟩

/-! ## 15. Additive identity and Equiv -/

private lemma toZMod_zero (n k : ℕ) (hn : n ≠ 0) :
    toZMod n k (capNeutral n k hn) = 0 := by
  set g := capGap n k
  have hg : 0 < g := capGap_pos n k hn
  have hm : k^n % g < g := Nat.mod_lt _ hg
  simp only [toZMod, capNeutral, natCast_mod]
  rw [Nat.cast_sub (by omega : k^n % g ≤ g), ZMod.natCast_self, natCast_mod]
  ring

/-- Bijection (Equiv) between Fin (capGap n k) and ZMod (capGap n k).
    Computable: explicit inverse fromZMod, no Classical.choice. -/
def toZModEquiv (n k : ℕ) (hn : n ≠ 0) : Fin (capGap n k) ≃ ZMod (capGap n k) where
  toFun     := toZMod n k
  invFun    := fromZMod n k hn
  left_inv  := fromZMod_toZMod n k hn
  right_inv := toZMod_fromZMod n k hn

/-! ## 16–17. Notes on AddEquiv and RingEquiv
    The chapter structure (Fin (capGap n k), capAdd, capMul) is isomorphic to ZMod g
    as a field. The propositional fact is captured by capField_isomorphic_zmod (§19).
    The bundled AddEquiv / RingEquiv forms require letI to override Fin.instAdd
    and Fin.instMul, but in Lean 4 the global Fin instances take precedence in struct literals,
    causing an unresolvable type conflict without a dedicated carrier type.
    These forms are not used by any theorem in the file, so they are omitted. -/

/-! ## 18. Step E — Operational multiplicative inverse (computable)

    Strategy: instead of transferring Field from ZMod via Classical.choice,
    we define the inverse directly via Fermat's Little Theorem
    expressed in the chapter operations.

    Formula: capMulInv(r) = capMulPow(r, g - 2)

    Correctness:
      r ⊗ capMulPow(r, g-2)
      = capMulPow(r, g-1)
      →[toZMod_capMulPow] toZMod(r)^{g-1} in ZMod g
      = 1                  [ZMod.pow_card_sub_one_eq_one, g prime]
      →[toZMod_injective]  capMulNeutral

    This definition is COMPUTABLE: structural recursion over ℕ,
    no use of Classical.choice.
-/

/-- Chapter multiplicative power: r^m with respect to capMul.
    Computable via structural recursion. -/
def capMulPow (n k : ℕ) (hn : n ≠ 0) :
    ℕ → Fin (capGap n k) → Fin (capGap n k)
  | 0,     _ => capMulNeutral n k hn
  | m + 1, r => capMul n k hn (capMulPow n k hn m r) r

-- toZMod transports capMulPow into the standard pow in ZMod.
lemma toZMod_capMulPow (n k : ℕ) (hn : n ≠ 0)
    (m : ℕ) (r : Fin (capGap n k)) :
    toZMod n k (capMulPow n k hn m r) = toZMod n k r ^ m := by
  induction m with
  | zero      =>
    simp only [capMulPow, pow_zero]
    exact toZMod_capMulNeutral n k hn
  | succ m ih =>
    simp only [capMulPow, pow_succ]
    rw [toZMod_mul, ih]

/-- Chapter multiplicative inverse via operational Fermat:
      capMulInv(r) = r^{g-2}   with respect to ⊗
    Computable, no use of Classical.choice. -/
def capMulInv (n k : ℕ) (hn : n ≠ 0)
    [Fact (Nat.Prime (capGap n k))]
    (r : Fin (capGap n k)) : Fin (capGap n k) :=
  capMulPow n k hn (capGap n k - 2) r

/-- Correctness of capMulInv: r ⊗ r^{g-2} = capMulNeutral.
    Proof: Fermat in ZMod g, pullback via toZMod_injective. -/
theorem capMul_mul_inv (n k : ℕ) (hn : n ≠ 0)
    [hprime : Fact (Nat.Prime (capGap n k))]
    (r : Fin (capGap n k))
    (hr : r ≠ capNeutral n k hn) :
    capMul n k hn r (capMulInv n k hn r) = capMulNeutral n k hn := by
  apply toZMod_injective n k hn
  rw [toZMod_mul, toZMod_capMulNeutral, capMulInv, toZMod_capMulPow]
  -- goal: toZMod n k r * toZMod n k r ^ (g - 2) = 1
  -- that is: toZMod n k r ^ (g - 1) = 1  (Fermat in ZMod g)
  have hg := hprime.out
  have hne : toZMod n k r ≠ 0 := by
    intro h
    apply hr
    apply toZMod_injective n k hn
    rw [h, toZMod_zero n k hn]
  have hge : 2 ≤ capGap n k := hg.two_le
  -- goal: toZMod r * toZMod r ^ (g-2) = 1
  -- step 1: reorder to get r^(g-2+1)
  rw [mul_comm, ← pow_succ,
      show capGap n k - 2 + 1 = capGap n k - 1 from by omega]
  -- goal: toZMod r ^ (g-1) = 1  (Fermat's Little Theorem in ZMod g)
  haveI : NeZero (capGap n k) := ⟨hg.pos.ne'⟩
  exact ZMod.pow_card_sub_one_eq_one hne

/-! ## 19. Final bundled theorem -/

/-- Substantial Theorem C — complete propositional statement.
    toZMod is an isomorphism between the chapter structure and ZMod g,
    and capMulInv provides the multiplicative inverse in operational closed form. -/
theorem capField_isomorphic_zmod (n k : ℕ) (hn : n ≠ 0) :
    Function.Bijective (toZMod n k) ∧
    (∀ r s : Fin (capGap n k),
      toZMod n k (capAdd n k hn r s) = toZMod n k r + toZMod n k s) ∧
    (∀ r s : Fin (capGap n k),
      toZMod n k (capMul n k hn r s) = toZMod n k r * toZMod n k s) ∧
    toZMod n k (capNeutral n k hn) = 0 ∧
    toZMod n k (capMulNeutral n k hn) = 1 :=
  ⟨toZMod_bijective n k hn, toZMod_add n k hn, toZMod_mul n k hn,
   toZMod_zero n k hn, toZMod_capMulNeutral n k hn⟩

/-! ## 20. CapChap — dedicated carrier type for the field structure

    The problem: Lean 4 has global instances Fin.instAdd, Fin.instMul that take precedence
    over any local `letI` in struct literals. This makes it impossible to construct
    AddEquiv/RingEquiv directly on Fin (capGap n k) with the chapter operations.

    Solution: a wrapper `structure CapChap` without preexisting algebraic instances.
    On it we define Add, Mul, Zero, One, Neg via the chapter operations,
    without conflicts. The RingEquiv with ZMod g is then a trivial record. -/

section CapChap

variable {n k : ℕ} (hn : n ≠ 0)

/-- Carrier type of the chapter field.
    Wrapper around Fin (capGap n k) without global algebraic instances. -/
structure CapChap (n k : ℕ) (hn : n ≠ 0) where
  toFin : Fin (capGap n k)

namespace CapChap

theorem ext {n k : ℕ} {hn : n ≠ 0} {a b : CapChap n k hn} (h : a.toFin = b.toFin) : a = b := by
  cases a; cases b; simp_all

instance instAdd : Add (CapChap n k hn) :=
  ⟨fun a b => ⟨capAdd n k hn a.toFin b.toFin⟩⟩

instance instMul : Mul (CapChap n k hn) :=
  ⟨fun a b => ⟨capMul n k hn a.toFin b.toFin⟩⟩

instance instZero : Zero (CapChap n k hn) :=
  ⟨⟨capNeutral n k hn⟩⟩

instance instOne : One (CapChap n k hn) :=
  ⟨⟨capMulNeutral n k hn⟩⟩

instance instNeg : Neg (CapChap n k hn) :=
  ⟨fun a => ⟨capInv n k hn a.toFin⟩⟩

-- convenience lemmas: operations on toFin
@[simp] lemma add_toFin (a b : CapChap n k hn) :
    (a + b).toFin = capAdd n k hn a.toFin b.toFin := rfl

@[simp] lemma mul_toFin (a b : CapChap n k hn) :
    (a * b).toFin = capMul n k hn a.toFin b.toFin := rfl

@[simp] lemma zero_toFin : (0 : CapChap n k hn).toFin = capNeutral n k hn := rfl

@[simp] lemma one_toFin : (1 : CapChap n k hn).toFin = capMulNeutral n k hn := rfl

@[simp] lemma neg_toFin (a : CapChap n k hn) :
    (-a).toFin = capInv n k hn a.toFin := rfl

/-! ### AddCommGroup — delegated to capAddCommGroup -/

instance instAddCommGroup : AddCommGroup (CapChap n k hn) where
  add_assoc a b c  := ext (capAdd_assoc' n k hn a.toFin b.toFin c.toFin)
  zero_add a       := ext (capNeutral_add n k hn a.toFin)
  add_zero a       := ext (capAdd_neutral n k hn a.toFin)
  neg_add_cancel a := ext (capInv_add n k hn a.toFin)
  add_comm a b     := ext (capAdd_comm' n k hn a.toFin b.toFin)
  nsmul m a        := ⟨(capAddCommGroup n k hn).nsmul m a.toFin⟩
  nsmul_zero a     := by apply ext; exact (capAddCommGroup n k hn).nsmul_zero a.toFin
  nsmul_succ m a   := by apply ext; exact (capAddCommGroup n k hn).nsmul_succ m a.toFin
  zsmul z a        := ⟨(capAddCommGroup n k hn).zsmul z a.toFin⟩
  zsmul_zero' a    := by apply ext; exact (capAddCommGroup n k hn).zsmul_zero' a.toFin
  zsmul_succ' m a  := by apply ext; exact (capAddCommGroup n k hn).zsmul_succ' m a.toFin
  zsmul_neg' m a   := by apply ext; exact (capAddCommGroup n k hn).zsmul_neg' m a.toFin

/-! ### CommRing -/

private lemma capMul_one_right (n k : ℕ) (hn : n ≠ 0) (r : Fin (capGap n k)) :
    capMul n k hn r (capMulNeutral n k hn) = r := by
  rw [capMul_comm]; exact capMul_neutral_left n k hn r

instance instCommRing : CommRing (CapChap n k hn) where
  mul_assoc a b c    := ext (capMul_assoc n k hn a.toFin b.toFin c.toFin)
  one_mul a          := ext (capMul_neutral_left n k hn a.toFin)
  mul_one a          := ext (capMul_one_right n k hn a.toFin)
  left_distrib a b c := ext (capMul_distrib_left n k hn a.toFin b.toFin c.toFin)
  right_distrib a b c := by
    apply ext
    simp only [add_toFin, mul_toFin]
    rw [capMul_comm n k hn (capAdd n k hn a.toFin b.toFin) c.toFin,
        capMul_distrib_left n k hn c.toFin a.toFin b.toFin,
        capMul_comm n k hn c.toFin a.toFin, capMul_comm n k hn c.toFin b.toFin]
  mul_comm a b       := ext (capMul_comm n k hn a.toFin b.toFin)
  zero_mul a         := by
    apply ext; simp only [mul_toFin, zero_toFin]
    apply toZMod_injective n k hn
    rw [toZMod_mul, toZMod_zero n k hn, zero_mul]
  mul_zero a         := by
    apply ext; simp only [mul_toFin, zero_toFin]
    apply toZMod_injective n k hn
    rw [toZMod_mul, toZMod_zero n k hn, mul_zero]

/-! ### RingEquiv with ZMod -/

/-- Ring isomorphism between CapChap and ZMod (capGap n k). -/
def toZModRingEquiv (n k : ℕ) (hn : n ≠ 0) :
    CapChap n k hn ≃+* ZMod (capGap n k) where
  toFun     := fun a => toZMod n k a.toFin
  invFun    := fun z => ⟨fromZMod n k hn z⟩
  left_inv  := fun a => ext (fromZMod_toZMod n k hn a.toFin)
  right_inv := toZMod_fromZMod n k hn
  map_add'  := fun a b => toZMod_add n k hn a.toFin b.toFin
  map_mul'  := fun a b => toZMod_mul n k hn a.toFin b.toFin

/-! ### Field -/

/-- The chapter field: if capGap n k is prime, CapChap is a (Galois) field GF(g). -/
instance instField [hprime : Fact (Nat.Prime (capGap n k))] :
    Field (CapChap n k hn) :=
  Equiv.field (toZModRingEquiv n k hn).toEquiv

end CapChap  -- closes namespace CapChap

end CapChap  -- closes section CapChap

/-! ## 21. Connection with Mersenne Numbers -/

/-- capGap(n, 1) = 2^n - 1: the chapter k=1 of degree n has width 2^n - 1.
    Directly connects the chapter structure to the Mersenne numbers. -/
lemma capGap_one_eq_mersenne (n : ℕ) : capGap n 1 = 2 ^ n - 1 := by
  simp [capGap]

#eval capGap 3 1  -- 7 = 2^3 - 1
#eval capGap 5 1  -- 31 = 2^5 - 1
#eval capGap 7 1  -- 127 = 2^7 - 1

/-- If 2^n - 1 is prime (Mersenne number), then CapChap n 1 is a Galois field GF(2^n - 1).
    `def` (not `theorem`) because Field is not a Prop. -/
def capField_mersenne (n : ℕ) (hn : n ≠ 0)
    [hprime : Fact (Nat.Prime (2 ^ n - 1))] :
    Field (CapChap n 1 hn) :=
  have h : capGap n 1 = 2 ^ n - 1 := capGap_one_eq_mersenne n
  haveI : Fact (Nat.Prime (capGap n 1)) := h ▸ hprime
  CapChap.instField hn

-- operational GF(7): chapter k=1, degree n=3 (2^3 - 1 = 7 is prime)
example : Field (CapChap 3 1 (by norm_num)) :=
  haveI : Fact (Nat.Prime (2 ^ 3 - 1)) := ⟨by norm_num⟩
  capField_mersenne 3 (by norm_num)

-- operational GF(31): chapter k=1, degree n=5 (2^5 - 1 = 31 is prime)
example : Field (CapChap 5 1 (by norm_num)) :=
  haveI : Fact (Nat.Prime (2 ^ 5 - 1)) := ⟨by norm_num⟩
  capField_mersenne 5 (by norm_num)

-- operational GF(127): chapter k=1, degree n=7 (2^7 - 1 = 127 is prime)
example : Field (CapChap 7 1 (by norm_num)) :=
  haveI : Fact (Nat.Prime (2 ^ 7 - 1)) := ⟨by norm_num⟩
  capField_mersenne 7 (by norm_num)

/-! ## 22. Binomial Formula for capGap -/

/-- capGap(n, k) = ∑_{i < n} C(n, i) * k^i
    Binomial expansion of (k+1)^n - k^n via Newton. -/
lemma capGap_binomial (n k : ℕ) :
    capGap n k = ∑ i ∈ Finset.range n, n.choose i * k ^ i := by
  simp only [capGap]
  have hle : k ^ n ≤ (k + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ k) _
  -- add_pow k 1 n : (k+1)^n = ∑_{i≤n} C(n,i) * k^i * 1^(n-i)
  have hexp : (k + 1) ^ n = ∑ i ∈ Finset.range (n + 1), n.choose i * k ^ i := by
    have h := add_pow k 1 n
    simp only [one_pow, mul_one] at h
    simp_rw [Nat.cast_id, mul_comm (k ^ _)] at h
    exact h
  -- the i=n term in the sum is C(n,n)*k^n = k^n
  rw [Finset.sum_range_succ] at hexp
  simp only [Nat.choose_self, one_mul] at hexp
  omega

/-- capGap(n, k) ≡ 1 (mod k) for k > 0.
    Follows from the binomial formula: the i=0 term equals 1, all the others are divisible by k. -/
-- Auxiliary lemma: (k+1)^n ≡ 1 (mod k)
private lemma succ_pow_mod (n k : ℕ) : (k + 1) ^ n % k = 1 % k := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    -- goal: 1 % k * ((k + 1) % k) % k = 1 % k
    -- (k + 1) % k = 1 % k  via Nat.add_mod_left: (n + a) % n = a % n
    have hstep : (k + 1) % k = 1 % k := by
      conv_lhs => rw [show k + 1 = k + 1 from rfl]
      rw [Nat.add_mod_left]
    rw [hstep, ← Nat.mul_mod, one_mul]

/-! ## 23. Conditional Multiplicative LCC -/

/-- Conditional Multiplicative LCC: if the product (k^n+r)*(k^n+s) stays in chapter k
    (that is, irootN of the product = k), then capMul(r,s).val = radRem(n, product).
    Multiplicative analogue of capAdd_eq_radRem_noOverflow. -/
theorem capMul_radRem_same_chapter (n k : ℕ) (hn : n ≠ 0)
    (r s : Fin (capGap n k))
    (hstay : irootN n ((k ^ n + r.val) * (k ^ n + s.val)) = k) :
    (capMul n k hn r s).val =
    radRem n ((k ^ n + r.val) * (k ^ n + s.val)) := by
  simp only [capMul, radRem]
  rw [hstay]
  -- goal: ((k^n+r)*(k^n+s) - k^n) % g = (k^n+r)*(k^n+s) - k^n
  apply Nat.mod_eq_of_lt
  -- needed: (k^n+r)*(k^n+s) - k^n < capGap n k
  -- from hstay: irootN of the product = k → product < (k+1)^n
  have hprod_lt : (k ^ n + r.val) * (k ^ n + s.val) < (k + 1) ^ n := by
    have := irootN_lt_succ_pow n ((k ^ n + r.val) * (k ^ n + s.val)) hn
    rw [hstay] at this
    exact this
  -- k^n ≤ (k^n + r) * (k^n + s):
  -- irootN_pow_le says k^n = iroot(prod)^n ≤ prod (via hstay)
  have hkn_le : k ^ n ≤ (k ^ n + r.val) * (k ^ n + s.val) := by
    have := irootN_pow_le n ((k ^ n + r.val) * (k ^ n + s.val)) hn
    rw [hstay] at this
    exact this
  simp only [capGap]
  omega

/-- Decomposition of capMul via radRem and irootN (documentary lemma).
    Makes explicit the "landing chapter correction" structure of capMul:
    capMul(r,s) = (radRem(prod) + iroot(prod)^n - k^n) % g -/
lemma capMul_radRem_decomposition (n k : ℕ) (hn : n ≠ 0)
    (r s : Fin (capGap n k)) :
    let prod := (k ^ n + r.val) * (k ^ n + s.val)
    (capMul n k hn r s).val =
    (radRem n prod + irootN n prod ^ n - k ^ n) % capGap n k := by
  intro prod
  simp only [capMul, radRem, prod]
  congr 1
  -- radRem(prod) + iroot(prod)^n = prod  (by definition of radRem)
  have h : irootN n ((k ^ n + r.val) * (k ^ n + s.val)) ^ n ≤ (k ^ n + r.val) * (k ^ n + s.val) :=
    irootN_pow_le n _ hn
  omega

end CampiOperazionistici
