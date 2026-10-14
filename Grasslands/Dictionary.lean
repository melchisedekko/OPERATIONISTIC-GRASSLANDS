/-
  Grasslands/Dictionary.lean — translation dynamics in an arbitrary global grassland.

  These results accompany the note Remainder Quotients of Interval Partitions of ℕ.

  For a gap sequence g (bases B_k, chapters, remainders `res`), a point a and its translate
  a + Δ are equivalent iff B_{chap a} + Δ is again a base B_h AND the remainder of a fits in
  chapter h. Consequences: equivalence at a positive distance Δ only happens in chapters of
  width ≤ Δ; and every distance has finitely many equivalent points iff the gaps tend to ∞.
-/

import CampiOperazionistici.GrasslandFlatLimit

namespace Grasslands

open CampiOperazionistici
open GapSeq

/-- Reconstruct a point from its chapter base and residue. -/
private lemma eq_base_chap_add_res (g : GapSeq) (a : ℕ) :
    a = g.base (g.chap a) + g.res a := by
  simpa [phi] using (g.phi_add_res a).symm

/-- **General point dictionary.** -/
theorem seqEquiv_add_iff (g : GapSeq) (a Δ : ℕ) :
    g.res a = g.res (a + Δ) ↔
      ∃ h : ℕ, g.base h = g.base (g.chap a) + Δ ∧ g.res a < g.gap h := by
  constructor
  · intro heq
    refine ⟨g.chap (a + Δ), ?_, ?_⟩
    · have ha := eq_base_chap_add_res g a
      have had := eq_base_chap_add_res g (a + Δ)
      have : g.base (g.chap a) + g.res a + Δ =
          g.base (g.chap (a + Δ)) + g.res (a + Δ) := by
        rw [← ha, ← had]
      rw [heq] at this
      omega
    · have := g.res_lt_gap (a + Δ)
      rwa [← heq] at this
  · rintro ⟨h, hb, hs⟩
    have ha := eq_base_chap_add_res g a
    have had : a + Δ = g.base h + g.res a := by
      calc
        a + Δ = g.base (g.chap a) + g.res a + Δ := by nth_rw 1 [ha]
        _ = g.base (g.chap a) + Δ + g.res a := by omega
        _ = g.base h + g.res a := by rw [← hb]
    rw [had, g.res_base_add hs]

/-- Equivalence at a positive distance `Δ` only happens in a chapter of width at most `Δ`. -/
theorem gap_chap_le_of_seqEquiv_add (g : GapSeq) (a Δ : ℕ) (hΔ : 0 < Δ)
    (heq : g.res a = g.res (a + Δ)) : g.gap (g.chap a) ≤ Δ := by
  obtain ⟨h, hb, _hs⟩ := (seqEquiv_add_iff g a Δ).mp heq
  have hlt : g.base (g.chap a) < g.base h := by omega
  have hchap : g.chap a < h := (g.base_strictMono.lt_iff_lt).mp hlt
  have hge : g.base (g.chap a + 1) ≤ g.base h := g.base_mono (Nat.succ_le_of_lt hchap)
  rw [base_succ] at hge
  omega

/-- If gaps tend to infinity, residues equal after a fixed shift only below a finite threshold. -/
private lemma seqEquiv_add_subset_Iio_of_tendsto (g : GapSeq) {Δ K : ℕ} (hΔ : 0 < Δ)
    (hK : ∀ k ≥ K, Δ < g.gap k) :
    {a : ℕ | g.res a = g.res (a + Δ)} ⊆ Set.Iio (g.base K) := by
  intro a ha
  by_contra hge
  have hge' : g.base K ≤ a := le_of_not_gt hge
  have hKa : K ≤ a := le_trans (g.le_base K) hge'
  have hchap : K ≤ g.chap a := Nat.le_findGreatest hKa hge'
  have hle := gap_chap_le_of_seqEquiv_add g a Δ hΔ ha
  have hgt := hK (g.chap a) hchap
  omega

/-- Bases of chapters with gap `v` are reencounter points at distance `v`. -/
private lemma base_mem_reencounters_of_gap_eq (g : GapSeq) {k v : ℕ} (hk : g.gap k = v) :
    g.base k ∈ {a : ℕ | g.res a = g.res (a + v)} := by
  have h0 : g.res (g.base k) = 0 := g.res_base k
  have had : g.base k + v = g.base (k + 1) := by rw [base_succ, hk]
  simp [h0, had, g.res_base]

/-- An infinite fiber of the gap map yields infinitely many reencounters at that distance. -/
private lemma infinite_reencounters_of_infinite_gap_fiber (g : GapSeq) {v : ℕ} (_hv : 0 < v)
    (hinf : {k : ℕ | g.gap k = v}.Infinite) :
    {a : ℕ | g.res a = g.res (a + v)}.Infinite := by
  have hinj : Set.InjOn g.base {k : ℕ | g.gap k = v} :=
    fun _ _ _ _ h => g.base_strictMono.injective h
  refine Set.Infinite.mono ?_ (hinf.image hinj)
  rintro _ ⟨k, hk, rfl⟩
  exact base_mem_reencounters_of_gap_eq g hk

/-- If every fiber of `gap` below `M` is finite, then `{k | gap k < M}` is finite. -/
private lemma finite_gap_lt_of_finite_fibers (g : GapSeq) (M : ℕ)
    (hfib : ∀ v < M, {k : ℕ | g.gap k = v}.Finite) :
    {k : ℕ | g.gap k < M}.Finite := by
  have hEq : {k : ℕ | g.gap k < M} = ⋃ v ∈ Finset.range M, {k : ℕ | g.gap k = v} := by
    ext k
    constructor
    · intro hk
      simp only [Set.mem_iUnion, Finset.mem_range]
      exact ⟨g.gap k, hk, rfl⟩
    · intro hk
      simp only [Set.mem_iUnion, Finset.mem_range] at hk
      obtain ⟨v, hv, rfl⟩ := hk
      exact hv
  rw [hEq]
  exact (Finset.finite_toSet _).biUnion fun v hv =>
    hfib v (Finset.mem_range.mp hv)

/-- **Eventual separation ⇔ gaps tend to infinity.** Every positive distance has only
finitely many points equivalent to their translate iff `gap k → ∞`. -/
theorem finite_reencounters_iff_tendsto (g : GapSeq) :
    (∀ Δ : ℕ, 0 < Δ → {a : ℕ | g.res a = g.res (a + Δ)}.Finite) ↔
      Filter.Tendsto g.gap Filter.atTop Filter.atTop := by
  constructor
  · intro hfin
    rw [Filter.tendsto_atTop_atTop]
    intro M
    by_contra hnot
    push_neg at hnot
    -- Negation: ∀ N, ∃ k ≥ N, gap k < M, so the sublevel set is unbounded.
    have hinfK : {k : ℕ | g.gap k < M}.Infinite := by
      refine Set.infinite_of_not_bddAbove ?_
      rintro ⟨N, hN⟩
      obtain ⟨k, hkN, hk⟩ := hnot (N + 1)
      have hkmem : k ∈ {k : ℕ | g.gap k < M} := hk
      have := hN hkmem
      omega
    have hfib : ∃ v < M, {k : ℕ | g.gap k = v}.Infinite := by
      by_contra hall
      push_neg at hall
      exact hinfK (finite_gap_lt_of_finite_fibers g M hall)
    obtain ⟨v, hvM, hinfv⟩ := hfib
    have hvpos : 0 < v := by
      by_contra h0
      push_neg at h0
      obtain ⟨k, hk⟩ := hinfv.nonempty
      have hk' : g.gap k = v := hk
      have : g.gap k = 0 := by omega
      exact absurd this (ne_of_gt (g.pos k))
    exact (infinite_reencounters_of_infinite_gap_fiber g hvpos hinfv) (hfin v hvpos)
  · intro htend Δ hΔ
    obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.mp htend) (Δ + 1)
    have hK' : ∀ k ≥ K, Δ < g.gap k := fun k hk => Nat.lt_of_succ_le (hK k hk)
    exact (Set.finite_Iio _).subset (seqEquiv_add_subset_Iio_of_tendsto g hΔ hK')

end Grasslands
