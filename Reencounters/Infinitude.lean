/-
  Reencounters/Infinitude.lean — for n = 3 and n = 4, infinitely many chapter pairs
  meet again in a later chapter.

  These results accompany the note Translations in the Quotient by the n-th Power Remainder.

  n = 3: Ramanujan's identity
    (α² + 7αβ − 9β²)³ + (2α² − 4αβ + 12β²)³ = (2α² + 10β²)³ + (α² − 9αβ − β²)³,
  at α = 1, β = t, gives for every t ≥ 3 a pair of chapters (t² + 9t − 1, 10t² + 2) that
  meets again in the later chapters (9t² − 7t − 1, 12t² − 4t + 2). These pairs are not
  multiples of one another (the first coordinates are not proportional), so the
  infinitude is not the trivial one obtained by scaling a single solution.
  n = 4: Euler's 59⁴ + 158⁴ = 133⁴ + 134⁴, scaled by c.
  For n ≥ 5 no example is known (Lander–Parkin–Selfridge); nothing is claimed.
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import CampiOperazionistici.CampiOperazionistici

namespace Reencounters

open CampiOperazionistici

/-- Chapters `k < h` meet again in a later chapter (for the exponent `n`). -/
def ForwardReencounter (n k h : ℕ) : Prop :=
  k < h ∧ ∃ k' h' : ℕ, k < k' ∧ k' ^ n + (h ^ n - k ^ n) = h' ^ n

/-- At `t = s + 3`, Ramanujan's four parameters expand to subtraction-free polynomials. -/
private lemma ramanujan_params (s : ℕ) :
    (s + 3) ^ 2 + 9 * (s + 3) - 1 = s ^ 2 + 15 * s + 35 ∧
    9 * (s + 3) ^ 2 - 7 * (s + 3) - 1 = 9 * s ^ 2 + 47 * s + 59 ∧
    10 * (s + 3) ^ 2 + 2 = 10 * s ^ 2 + 60 * s + 92 ∧
    12 * (s + 3) ^ 2 - 4 * (s + 3) + 2 = 12 * s ^ 2 + 68 * s + 98 := by
  have hk0 : (s + 3) ^ 2 + 9 * (s + 3) = s ^ 2 + 15 * s + 36 := by ring
  have hk : (s + 3) ^ 2 + 9 * (s + 3) - 1 = s ^ 2 + 15 * s + 35 := by
    rw [hk0, Nat.add_sub_assoc (by decide) (s ^ 2 + 15 * s)]
  have hexp9 : 9 * (s + 3) ^ 2 = 9 * s ^ 2 + 54 * s + 81 := by ring
  have hlin7 : 7 * (s + 3) = 7 * s + 21 := by ring
  have hsplit9 : 9 * s ^ 2 + 54 * s + 81 = (9 * s ^ 2 + 47 * s + 60) + (7 * s + 21) := by ring
  have hsub9 : 9 * (s + 3) ^ 2 - 7 * (s + 3) = 9 * s ^ 2 + 47 * s + 60 := by
    rw [hexp9, hlin7, hsplit9]
    exact Nat.add_sub_cancel (9 * s ^ 2 + 47 * s + 60) (7 * s + 21)
  have hk' : 9 * (s + 3) ^ 2 - 7 * (s + 3) - 1 = 9 * s ^ 2 + 47 * s + 59 := by
    rw [hsub9, Nat.add_sub_assoc (by decide) (9 * s ^ 2 + 47 * s)]
  have hh : 10 * (s + 3) ^ 2 + 2 = 10 * s ^ 2 + 60 * s + 92 := by ring
  have hexp12 : 12 * (s + 3) ^ 2 = 12 * s ^ 2 + 72 * s + 108 := by ring
  have hlin4 : 4 * (s + 3) = 4 * s + 12 := by ring
  have hsplit12 : 12 * s ^ 2 + 72 * s + 108 = (12 * s ^ 2 + 68 * s + 96) + (4 * s + 12) := by ring
  have hsub12 : 12 * (s + 3) ^ 2 - 4 * (s + 3) = 12 * s ^ 2 + 68 * s + 96 := by
    rw [hexp12, hlin4, hsplit12]
    exact Nat.add_sub_cancel (12 * s ^ 2 + 68 * s + 96) (4 * s + 12)
  have hh' : 12 * (s + 3) ^ 2 - 4 * (s + 3) + 2 = 12 * s ^ 2 + 68 * s + 98 := by
    rw [hsub12]
  exact ⟨hk, hk', hh, hh'⟩

set_option maxHeartbeats 1000000 in
/-- Subtraction-free form of Ramanujan's identity along the ray `t = s + 3`. -/
private lemma ramanujan_cubic (s : ℕ) :
    (9 * s ^ 2 + 47 * s + 59) ^ 3 + (10 * s ^ 2 + 60 * s + 92) ^ 3 =
      (12 * s ^ 2 + 68 * s + 98) ^ 3 + (s ^ 2 + 15 * s + 35) ^ 3 := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  ring

/-- In Ramanujan's family the source chapter sits strictly before its partner. -/
private lemma ramanujan_k_lt_h (t : ℕ) (ht : 3 ≤ t) :
    t ^ 2 + 9 * t - 1 < 10 * t ^ 2 + 2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rcases ramanujan_params s with ⟨hk, -, hh, -⟩
  rw [hk, hh]
  have hsum :
      s ^ 2 + 15 * s + 35 + (9 * s ^ 2 + 45 * s + 57) = 10 * s ^ 2 + 60 * s + 92 := by ring
  rw [← hsum]
  exact Nat.lt_add_of_pos_right <|
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 57) (Nat.le_add_left 57 (9 * s ^ 2 + 45 * s))

/-- Ramanujan's family, n = 3. -/
theorem ramanujan_forward (t : ℕ) (ht : 3 ≤ t) :
    (t ^ 2 + 9 * t - 1) < 9 * t ^ 2 - 7 * t - 1 ∧
    (9 * t ^ 2 - 7 * t - 1) ^ 3 + ((10 * t ^ 2 + 2) ^ 3 - (t ^ 2 + 9 * t - 1) ^ 3)
      = (12 * t ^ 2 - 4 * t + 2) ^ 3 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rcases ramanujan_params s with ⟨hk, hk', hh, hh'⟩
  rw [hk, hk', hh, hh']
  constructor
  · have hsum :
        s ^ 2 + 15 * s + 35 + (8 * s ^ 2 + 32 * s + 24) = 9 * s ^ 2 + 47 * s + 59 := by ring
    rw [← hsum]
    exact Nat.lt_add_of_pos_right <|
      Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 24) (Nat.le_add_left 24 (8 * s ^ 2 + 32 * s))
  · have hle : (s ^ 2 + 15 * s + 35) ^ 3 ≤ (10 * s ^ 2 + 60 * s + 92) ^ 3 :=
      Nat.pow_le_pow_left (by
        have hsum :
            s ^ 2 + 15 * s + 35 + (9 * s ^ 2 + 45 * s + 57) = 10 * s ^ 2 + 60 * s + 92 := by ring
        rw [← hsum]
        exact Nat.le_add_right _ _) 3
    calc
      (9 * s ^ 2 + 47 * s + 59) ^ 3 +
          ((10 * s ^ 2 + 60 * s + 92) ^ 3 - (s ^ 2 + 15 * s + 35) ^ 3)
        = (9 * s ^ 2 + 47 * s + 59) ^ 3 + (10 * s ^ 2 + 60 * s + 92) ^ 3 -
            (s ^ 2 + 15 * s + 35) ^ 3 :=
          (Nat.add_sub_assoc hle _).symm
      _ = (12 * s ^ 2 + 68 * s + 98) ^ 3 + (s ^ 2 + 15 * s + 35) ^ 3 -
            (s ^ 2 + 15 * s + 35) ^ 3 := by
          rw [ramanujan_cubic s]
      _ = (12 * s ^ 2 + 68 * s + 98) ^ 3 :=
          Nat.add_sub_cancel _ _

/-- The first coordinate of Ramanujan's family is strictly increasing in the shift. -/
private lemma ramanujan_k_strictMono :
    StrictMono fun t : ℕ => (t + 3) ^ 2 + 9 * (t + 3) - 1 := by
  have heq : ∀ t : ℕ, (t + 3) ^ 2 + 9 * (t + 3) - 1 = t ^ 2 + 15 * t + 35 :=
    fun t => (ramanujan_params t).1
  refine strictMono_nat_of_lt_succ fun t => ?_
  rw [heq t, heq (t + 1)]
  have hsum : t ^ 2 + 15 * t + 35 + (2 * t + 16) = (t + 1) ^ 2 + 15 * (t + 1) + 35 := by ring
  rw [← hsum]
  exact Nat.lt_add_of_pos_right <|
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 16) (Nat.le_add_left 16 (2 * t))

theorem forwardReencounter_three_infinite :
    {p : ℕ × ℕ | ForwardReencounter 3 p.1 p.2}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
      (f := fun t : ℕ => ((t + 3) ^ 2 + 9 * (t + 3) - 1, 10 * (t + 3) ^ 2 + 2))
  · intro a b hab
    exact ramanujan_k_strictMono.injective (congrArg Prod.fst hab)
  · intro t
    unfold ForwardReencounter
    have ht : 3 ≤ t + 3 := Nat.le_add_left 3 t
    have hr := ramanujan_forward (t + 3) ht
    exact ⟨ramanujan_k_lt_h (t + 3) ht,
      9 * (t + 3) ^ 2 - 7 * (t + 3) - 1,
      12 * (t + 3) ^ 2 - 4 * (t + 3) + 2, hr.1, hr.2⟩

/-- The base Euler equality `59⁴ + 158⁴ = 133⁴ + 134⁴`. -/
private lemma euler_59_158 : 59 ^ 4 + 158 ^ 4 = 133 ^ 4 + 134 ^ 4 := by
  decide

/-- Scaling a difference of equal powers: `(a*c)^n - (b*c)^n = c^n * (a^n - b^n)`. -/
private lemma mul_pow_sub (a b c n : ℕ) :
    (a * c) ^ n - (b * c) ^ n = c ^ n * (a ^ n - b ^ n) := by
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_comm (a ^ n), Nat.mul_comm (b ^ n), ← Nat.mul_sub]

/-- Euler's solution, scaled: n = 4. -/
theorem euler_forward (c : ℕ) (hc : 0 < c) : ForwardReencounter 4 (59 * c) (133 * c) := by
  unfold ForwardReencounter
  have hkh : 59 * c < 133 * c := Nat.mul_lt_mul_of_pos_right (by decide : 59 < 133) hc
  have hkk : 59 * c < 134 * c := Nat.mul_lt_mul_of_pos_right (by decide : 59 < 134) hc
  refine ⟨hkh, 134 * c, 158 * c, hkk, ?_⟩
  have h59 : 59 ^ 4 ≤ 133 ^ 4 := Nat.pow_le_pow_left (by decide : 59 ≤ 133) 4
  have hbase : 134 ^ 4 + (133 ^ 4 - 59 ^ 4) = 158 ^ 4 := by
    calc
      134 ^ 4 + (133 ^ 4 - 59 ^ 4)
          = 134 ^ 4 + 133 ^ 4 - 59 ^ 4 := (Nat.add_sub_assoc h59 (134 ^ 4)).symm
      _ = 133 ^ 4 + 134 ^ 4 - 59 ^ 4 := by rw [Nat.add_comm (134 ^ 4) (133 ^ 4)]
      _ = 59 ^ 4 + 158 ^ 4 - 59 ^ 4 := by rw [← euler_59_158]
      _ = 158 ^ 4 := Nat.add_sub_cancel_left (59 ^ 4) (158 ^ 4)
  calc
    (134 * c) ^ 4 + ((133 * c) ^ 4 - (59 * c) ^ 4)
        = 134 ^ 4 * c ^ 4 + c ^ 4 * (133 ^ 4 - 59 ^ 4) := by
          rw [Nat.mul_pow, mul_pow_sub 133 59 c 4]
    _ = c ^ 4 * 134 ^ 4 + c ^ 4 * (133 ^ 4 - 59 ^ 4) := by rw [Nat.mul_comm (134 ^ 4)]
    _ = c ^ 4 * (134 ^ 4 + (133 ^ 4 - 59 ^ 4)) := by rw [← Nat.mul_add]
    _ = c ^ 4 * 158 ^ 4 := by rw [hbase]
    _ = 158 ^ 4 * c ^ 4 := by rw [Nat.mul_comm]
    _ = (158 * c) ^ 4 := by rw [← Nat.mul_pow]

theorem forwardReencounter_four_infinite :
    {p : ℕ × ℕ | ForwardReencounter 4 p.1 p.2}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
      (f := fun c : ℕ => (59 * (c + 1), 133 * (c + 1)))
  · intro a b hab
    exact (Nat.add_one_inj).mp <|
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 59) (congrArg Prod.fst hab)
  · intro c
    exact euler_forward (c + 1) (Nat.succ_pos c)

end Reencounters
