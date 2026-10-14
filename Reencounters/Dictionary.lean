/-
  Reencounters/Dictionary.lean — the point form of the reencounter dictionary,
  and eventual permanent separation for every distance Δ.

  These results accompany the note Translations in the Quotient by the n-th Power Remainder.

  Two points at distance Δ are equivalent exactly when the base of the chapter of the
  first, shifted by Δ, is again a perfect n-th power. Hence equivalence at distance Δ
  only happens in chapters of gap at most Δ: finitely many, and none from Δ^n on.
-/

import CampiOperazionistici.CapitolarGroupoid

namespace Reencounters

open CampiOperazionistici

/-- Remainder of `a` is the offset of `a` inside its chapter. -/
lemma radRem_eq_chapter_offset (n a : ℕ) (hn : n ≠ 0) :
    a = irootN n a ^ n + radRem n a := by
  have hle := irootN_pow_le n a hn
  simp [radRem]
  omega

/-- The point dictionary: `a` and `a + Δ` are equivalent iff `⌊a^{1/n}⌋^n + Δ` is a
perfect `n`-th power. -/
theorem aodEquiv_add_iff (n a Δ : ℕ) (hn : 2 ≤ n) :
    radRem n a = radRem n (a + Δ) ↔ ∃ h : ℕ, irootN n a ^ n + Δ = h ^ n := by
  have hnn : n ≠ 0 := by omega
  constructor
  · intro heq
    refine ⟨irootN n (a + Δ), ?_⟩
    have hdiff := aodEquiv_pow_diff_eq n a (a + Δ) hnn heq
    have hpa := irootN_pow_le n a hnn
    have hpb := irootN_pow_le n (a + Δ) hnn
    -- (irootN (a+Δ))^n - (irootN a)^n = Δ in ℤ
    zify [hpa, hpb] at hdiff ⊢
    linarith
  · intro ⟨h, hh⟩
    set k := irootN n a
    set s := radRem n a
    have ha : a = k ^ n + s := radRem_eq_chapter_offset n a hnn
    have hs : s < gap n k := by
      simpa [k, gap] using radRem_lt_gap n a hnn
    have haΔ : a + Δ = h ^ n + s := by
      calc a + Δ = k ^ n + s + Δ := by rw [ha]
        _ = (k ^ n + Δ) + s := by ring
        _ = h ^ n + s := by rw [hh]
    -- Need s < gap n h so that radRem (a+Δ) = s
    have hkh : k ≤ h := by
      by_contra hlt
      push_neg at hlt
      have : h ^ n < k ^ n := Nat.pow_lt_pow_left hlt hnn
      have : k ^ n + Δ < k ^ n := by
        calc k ^ n + Δ = h ^ n := hh
          _ < k ^ n := this
      omega
    have hs_h : s < gap n h := by
      cases Nat.lt_or_eq_of_le hkh with
      | inl hlt =>
        exact lt_of_lt_of_le hs (gap_le_of_lt n k h hn hlt)
      | inr heq =>
        simpa [heq] using hs
    have rhs : radRem n (a + Δ) = s := by
      rw [haΔ]
      exact radRem_base_add n h s hnn hs_h
    simp [s] at rhs
    exact rhs.symm ▸ rfl

/-- Equivalence at a positive distance `Δ` only happens in a chapter of gap at most `Δ`. -/
theorem gap_le_of_aodEquiv_add (n a Δ : ℕ) (hn : 2 ≤ n) (hΔ : 0 < Δ)
    (heq : radRem n a = radRem n (a + Δ)) : gap n (irootN n a) ≤ Δ := by
  have hnn : n ≠ 0 := by omega
  obtain ⟨h, hh⟩ := (aodEquiv_add_iff n a Δ hn).mp heq
  set k := irootN n a
  have hgt : k < h := by
    by_contra hle
    push_neg at hle
    have : h ^ n ≤ k ^ n := Nat.pow_le_pow_left hle n
    have : Δ = 0 := by
      have hkΔ : k ^ n + Δ = h ^ n := hh
      omega
    omega
  have hge : k + 1 ≤ h := Nat.succ_le_of_lt hgt
  have hpow : (k + 1) ^ n ≤ h ^ n := Nat.pow_le_pow_left hge n
  -- Δ = h^n - k^n ≥ (k+1)^n - k^n = gap n k
  have hk_le : k ^ n ≤ h ^ n := by
    have := Nat.pow_le_pow_left (Nat.le_of_lt hgt) n
    exact this
  have : gap n k ≤ Δ := by
    simp only [gap]
    have hcalc : h ^ n - k ^ n = Δ := by
      have : k ^ n + Δ = h ^ n := hh
      omega
    have : (k + 1) ^ n - k ^ n ≤ h ^ n - k ^ n :=
      Nat.sub_le_sub_right hpow _
    omega
  exact this

/-- Eventual permanent separation: from `Δ ^ n` on, no point is equivalent to its
translate by `Δ`. -/
theorem eventual_separation (n a Δ : ℕ) (hn : 2 ≤ n) (hΔ : 0 < Δ) (ha : Δ ^ n ≤ a) :
    radRem n a ≠ radRem n (a + Δ) := by
  intro heq
  have hnn : n ≠ 0 := by omega
  have hg := gap_le_of_aodEquiv_add n a Δ hn hΔ heq
  set k := irootN n a
  have hkΔ : Δ ≤ k := by
    have : irootN n (Δ ^ n) ≤ irootN n a := irootN_mono n _ _ hnn ha
    rwa [irootN_perfectPow n Δ hnn] at this
  have hgap : k + 1 ≤ gap n k := gap_ge_succ n k hn
  -- gap n k ≥ k+1 > Δ (since k ≥ Δ), contradicting gap ≤ Δ
  have : gap n k > Δ := by omega
  omega

/-- The set of points equivalent to their translate by `Δ > 0` is finite. -/
theorem reencounterSet_finite (n Δ : ℕ) (hn : 2 ≤ n) (hΔ : 0 < Δ) :
    {a : ℕ | radRem n a = radRem n (a + Δ)}.Finite := by
  refine (Set.finite_lt_nat (Δ ^ n)).subset ?_
  intro a ha
  by_contra hge
  have hge' : Δ ^ n ≤ a := Nat.le_of_not_lt hge
  exact eventual_separation n a Δ hn hΔ hge' ha

/-- The reencounter set at distance `Δ` is a union of whole chapters: if `a` is equivalent
to `a + Δ`, so is every point of the chapter of `a`. -/
theorem reencounterSet_chapter_closed (n a b Δ : ℕ) (hn : 2 ≤ n)
    (hab : irootN n a = irootN n b) (heq : radRem n a = radRem n (a + Δ)) :
    radRem n b = radRem n (b + Δ) := by
  have ⟨h, hh⟩ := (aodEquiv_add_iff n a Δ hn).mp heq
  refine (aodEquiv_add_iff n b Δ hn).mpr ⟨h, ?_⟩
  simpa [hab] using hh

end Reencounters
