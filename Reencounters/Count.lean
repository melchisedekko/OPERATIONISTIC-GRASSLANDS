/-
  Reencounters/Count.lean — the exact total time a translated pair spends equivalent.

  These results accompany the note Translations in the Quotient by the n-th Power Remainder.

  For k < h and t < gap(n,k), translate the pair (k^n + t, h^n + t) by m = 0, 1, 2, …
  With Δ = h^n − k^n, the offsets m at which the pair is equivalent are: the first window,
  of length gap(n,k) − t, and then one WHOLE chapter k' (length gap(n,k')) for each
  later chapter k' > k such that k'^n + Δ is an n-th power. Nothing else, and only
  finitely many offsets in all.
-/

import Reencounters.Dictionary

namespace Reencounters

open CampiOperazionistici
open Finset

/-- The chapters `k' > k` in which a pair at distance `Δ` meets again. All of them are
`< Δ`, since `gap n k' ≥ k' + 1` must be `≤ Δ`. -/
def laterMeetings (n k Δ : ℕ) : Finset ℕ :=
  (Finset.Ioo k Δ).filter (fun k' => irootN n (k' ^ n + Δ) ^ n = k' ^ n + Δ)

/-! ### Helpers: distance Δ and the point dictionary on translates -/

/-- Positive power gap when the chapters are ordered. -/
lemma delta_pos (n k h : ℕ) (hn : n ≠ 0) (hkh : k < h) : 0 < h ^ n - k ^ n :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hkh hn)

/-- The chapter gap of `k` is at most the power distance to a later chapter `h`. -/
lemma gap_le_delta (n k h : ℕ) (_hn : n ≠ 0) (hkh : k < h) :
    gap n k ≤ h ^ n - k ^ n := by
  have hle : (k + 1) ^ n ≤ h ^ n := Nat.pow_le_pow_left (Nat.succ_le_of_lt hkh) n
  simp only [gap]
  omega

/-- Rewrite the second translate as a shift by `Δ = h^n − k^n`. -/
lemma translate_eq_add_delta (n k h t m : ℕ) (hkh : k < h) :
    h ^ n + t + m = (k ^ n + t + m) + (h ^ n - k ^ n) := by
  have : k ^ n ≤ h ^ n := Nat.pow_le_pow_left (Nat.le_of_lt hkh) n
  omega

/-- Dictionary in perfect-power form: `a ~ a+Δ` iff `⌊a^{1/n}⌋^n + Δ` is an `n`-th power. -/
lemma aodEquiv_add_iff_irootN (n a Δ : ℕ) (hn : 2 ≤ n) :
    radRem n a = radRem n (a + Δ) ↔
      irootN n (irootN n a ^ n + Δ) ^ n = irootN n a ^ n + Δ := by
  rw [aodEquiv_add_iff n a Δ hn]
  constructor
  · rintro ⟨h, hh⟩
    simp [hh, irootN_perfectPow n h (by omega)]
  · intro h
    exact ⟨irootN n (irootN n a ^ n + Δ), h.symm⟩

/-- Equivalence of the translated pair is the point dictionary at `a = k^n + t + m`. -/
lemma reencounter_iff_aodEquiv_add (n k h t m : ℕ) (_hn : 2 ≤ n) (hkh : k < h) :
    radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m) ↔
      radRem n (k ^ n + t + m) =
        radRem n ((k ^ n + t + m) + (h ^ n - k ^ n)) := by
  rw [translate_eq_add_delta n k h t m hkh]

/-- Offsets with `a ≥ Δ^n` never reencounter. -/
lemma not_reencounter_of_delta_pow_le (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (hm : (h ^ n - k ^ n) ^ n ≤ k ^ n + t + m) :
    radRem n (k ^ n + t + m) ≠ radRem n (h ^ n + t + m) := by
  set Δ := h ^ n - k ^ n
  have hnn : n ≠ 0 := by omega
  have hΔ : 0 < Δ := delta_pos n k h hnn hkh
  intro heq
  have heq' : radRem n (k ^ n + t + m) = radRem n ((k ^ n + t + m) + Δ) :=
    (reencounter_iff_aodEquiv_add n k h t m hn hkh).mp heq
  exact eventual_separation n (k ^ n + t + m) Δ hn hΔ hm heq'

/-- A translated pair is equivalent at only finitely many offsets. -/
theorem reencounter_offsets_finite (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h) :
    {m : ℕ | radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m)}.Finite := by
  set Δ := h ^ n - k ^ n
  refine (Set.finite_lt_nat (Δ ^ n)).subset ?_
  intro m hm
  by_contra hge
  have hge' : Δ ^ n ≤ m := Nat.le_of_not_lt hge
  have ha : Δ ^ n ≤ k ^ n + t + m := by omega
  exact not_reencounter_of_delta_pow_le n k h t m hn hkh ha hm

/-! ### Helpers: chapter of the left translate and the first window -/

/-- Chapter index of the left translate `k^n + t + m`. -/
def leftChapter (n k t m : ℕ) : ℕ := irootN n (k ^ n + t + m)

/-- The left translate stays in chapter `k` exactly on the first window. -/
lemma leftChapter_eq_k_iff (n k t m : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    leftChapter n k t m = k ↔ m < gap n k - t := by
  simp only [leftChapter]
  constructor
  · intro hk
    have hlt := irootN_lt_succ_pow n (k ^ n + t + m) hn
    rw [hk, succ_pow_eq_add_gap n k hn] at hlt
    omega
  · intro hm
    have htm : t + m < gap n k := by omega
    have : k ^ n + t + m = k ^ n + (t + m) := by ring
    rw [this, sum_in_chapter n k (t + m) hn htm]

/-- First window: the translated pair is always equivalent. -/
lemma reencounter_of_lt_gap_sub (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht : t < gap n k) (hm : m < gap n k - t) :
    radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m) :=
  additive_utd_first_jump n k h t m hn hkh ht hm

/-- Unfolded membership in `laterMeetings`. -/
lemma mem_laterMeetings_iff (n k Δ k' : ℕ) :
    k' ∈ laterMeetings n k Δ ↔
      k < k' ∧ k' < Δ ∧ irootN n (k' ^ n + Δ) ^ n = k' ^ n + Δ := by
  simp [laterMeetings, mem_filter, mem_Ioo, and_assoc]

/-- If `a ~ a+Δ` with `Δ > 0`, then the chapter of `a` is strictly less than `Δ`. -/
lemma irootN_lt_delta_of_aodEquiv_add (n a Δ : ℕ) (hn : 2 ≤ n) (hΔ : 0 < Δ)
    (heq : radRem n a = radRem n (a + Δ)) : irootN n a < Δ := by
  have hg := gap_le_of_aodEquiv_add n a Δ hn hΔ heq
  have hge := gap_ge_succ n (irootN n a) hn
  omega

/-- The left chapter is at least `k`. -/
lemma k_le_leftChapter (n k t m : ℕ) (hn : n ≠ 0) : k ≤ leftChapter n k t m := by
  have hmono := irootN_mono n (k ^ n) (k ^ n + t + m) hn (by omega)
  simpa [leftChapter, irootN_perfectPow n k hn] using hmono

/-- Equivalence iff first-window offset or a later meeting chapter. -/
lemma reencounter_iff_window_or_later (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h)
    (ht : t < gap n k) :
    radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m) ↔
      m < gap n k - t ∨
        leftChapter n k t m ∈ laterMeetings n k (h ^ n - k ^ n) := by
  set Δ := h ^ n - k ^ n with hΔdef
  set a := k ^ n + t + m
  set k' := leftChapter n k t m
  have hnn : n ≠ 0 := by omega
  have hΔ : 0 < Δ := delta_pos n k h hnn hkh
  have hadd : h ^ n + t + m = a + Δ := translate_eq_add_delta n k h t m hkh
  constructor
  · intro heq
    have heq' : radRem n a = radRem n (a + Δ) := by
      rwa [hadd] at heq
    have hpow : irootN n (k' ^ n + Δ) ^ n = k' ^ n + Δ := by
      simpa [k', leftChapter, a] using (aodEquiv_add_iff_irootN n a Δ hn).mp heq'
    have hk'ge : k ≤ k' := k_le_leftChapter n k t m hnn
    cases Nat.lt_or_eq_of_le hk'ge with
    | inr hk'eq =>
      left
      exact (leftChapter_eq_k_iff n k t m hnn ht).mp hk'eq.symm
    | inl hk'lt =>
      right
      have hk'Δ : k' < Δ := by
        simpa [k', leftChapter, a] using irootN_lt_delta_of_aodEquiv_add n a Δ hn hΔ heq'
      exact (mem_laterMeetings_iff n k Δ k').mpr ⟨hk'lt, hk'Δ, hpow⟩
  · intro h
    rcases h with hm | hmem
    · exact reencounter_of_lt_gap_sub n k h t m hn hkh ht hm
    · have ⟨_, _, hpow⟩ := (mem_laterMeetings_iff n k Δ k').mp hmem
      have heq' : radRem n a = radRem n (a + Δ) := by
        refine (aodEquiv_add_iff_irootN n a Δ hn).mpr ?_
        simpa [k', leftChapter, a] using hpow
      rwa [← hadd] at heq'

/-! ### Helpers: whole-chapter offset blocks for later meetings -/

/-- Offsets `m` at which the left translate lies in chapter `k'`. -/
def chapterOffsets (n k t k' : ℕ) : Finset ℕ :=
  (Finset.range (gap n k')).image (fun i => k' ^ n - k ^ n - t + i)

/-- For `k' > k` and `t < gap n k`, the start of chapter `k'` is past `k^n + t`. -/
lemma pow_add_t_le_of_lt_chapter (n k t k' : ℕ) (hn : n ≠ 0) (ht : t < gap n k)
    (hlt : k < k') : k ^ n + t ≤ k' ^ n := by
  have : (k + 1) ^ n ≤ k' ^ n := Nat.pow_le_pow_left (Nat.succ_le_of_lt hlt) n
  rw [succ_pow_eq_add_gap n k hn] at this
  omega

/-- Membership in a chapter-offset block is the chapter interval for `k^n + t + m`. -/
lemma mem_chapterOffsets_iff (n k t k' m : ℕ) (hn : n ≠ 0)
    (hle : k ^ n + t ≤ k' ^ n) :
    m ∈ chapterOffsets n k t k' ↔
      k' ^ n ≤ k ^ n + t + m ∧ k ^ n + t + m < (k' + 1) ^ n := by
  simp only [chapterOffsets, mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hsucc : (k' + 1) ^ n = k' ^ n + gap n k' := succ_pow_eq_add_gap n k' hn
    constructor <;> omega
  · intro ⟨hlo, hhi⟩
    refine ⟨k ^ n + t + m - k' ^ n, ?_, by omega⟩
    have hsucc : (k' + 1) ^ n = k' ^ n + gap n k' := succ_pow_eq_add_gap n k' hn
    omega

/-- Each chapter-offset block has cardinality `gap n k'`. -/
lemma card_chapterOffsets (n k t k' : ℕ) (_hle : k ^ n + t ≤ k' ^ n) :
    (chapterOffsets n k t k').card = gap n k' := by
  simp only [chapterOffsets]
  rw [card_image_of_injective _ (fun i j h => by omega), card_range]

/-- On a chapter-offset block for `k'`, the left chapter is exactly `k'`. -/
lemma leftChapter_of_mem_chapterOffsets (n k t k' m : ℕ) (hn : n ≠ 0)
    (hle : k ^ n + t ≤ k' ^ n) (hm : m ∈ chapterOffsets n k t k') :
    leftChapter n k t m = k' := by
  have ⟨hlo, hhi⟩ := (mem_chapterOffsets_iff n k t k' m hn hle).mp hm
  exact irootN_unique n (k ^ n + t + m) k' hn hlo hhi

/-- First-window offsets are disjoint from every later chapter-offset block. -/
lemma disjoint_window_chapterOffsets (n k t k' : ℕ) (hn : n ≠ 0) (ht : t < gap n k)
    (hlt : k < k') :
    Disjoint (range (gap n k - t)) (chapterOffsets n k t k') := by
  refine disjoint_left.2 ?_
  intro m hmWin hmOff
  have hle := pow_add_t_le_of_lt_chapter n k t k' hn ht hlt
  have hk' : leftChapter n k t m = k' := leftChapter_of_mem_chapterOffsets n k t k' m hn hle hmOff
  have hk : leftChapter n k t m = k := (leftChapter_eq_k_iff n k t m hn ht).mpr (mem_range.mp hmWin)
  omega

/-- Distinct later meeting chapters give disjoint offset blocks. -/
lemma pairwiseDisjoint_chapterOffsets (n k t Δ : ℕ) (hn : n ≠ 0) (ht : t < gap n k) :
    (laterMeetings n k Δ : Set ℕ).PairwiseDisjoint (chapterOffsets n k t) := by
  intro k1 hk1 k2 hk2 hne
  have ⟨hlt1, _, _⟩ := (mem_laterMeetings_iff n k Δ k1).mp (by exact hk1)
  have ⟨hlt2, _, _⟩ := (mem_laterMeetings_iff n k Δ k2).mp (by exact hk2)
  refine disjoint_left.2 ?_
  intro m hm1 hm2
  have hle1 := pow_add_t_le_of_lt_chapter n k t k1 hn ht hlt1
  have hle2 := pow_add_t_le_of_lt_chapter n k t k2 hn ht hlt2
  have h1 := leftChapter_of_mem_chapterOffsets n k t k1 m hn hle1 hm1
  have h2 := leftChapter_of_mem_chapterOffsets n k t k2 m hn hle2 hm2
  exact hne (by omega)

/-- Every first-window offset lies in `range (Δ^n)`. -/
lemma window_lt_delta_pow (n k h t m : ℕ) (hn : 2 ≤ n) (hkh : k < h) (ht : t < gap n k)
    (hm : m < gap n k - t) : m < (h ^ n - k ^ n) ^ n := by
  set Δ := h ^ n - k ^ n
  have hnn : n ≠ 0 := by omega
  have hgap : gap n k ≤ Δ := gap_le_delta n k h hnn hkh
  have hΔ : 0 < Δ := delta_pos n k h hnn hkh
  have hself : Δ ≤ Δ ^ n := Nat.le_self_pow (by omega) Δ
  omega

/-- Offsets of a later meeting chapter `k' < Δ` lie in `range (Δ^n)`. -/
lemma chapterOffset_lt_delta_pow (n k t Δ k' m : ℕ) (hn : n ≠ 0)
    (hle : k ^ n + t ≤ k' ^ n) (hkΔ : k' < Δ)
    (hm : m ∈ chapterOffsets n k t k') : m < Δ ^ n := by
  have ⟨_, hhi⟩ := (mem_chapterOffsets_iff n k t k' m hn hle).mp hm
  have hsucc : k' + 1 ≤ Δ := Nat.succ_le_of_lt hkΔ
  have hpow : (k' + 1) ^ n ≤ Δ ^ n := Nat.pow_le_pow_left hsucc n
  omega

/-- The filtered reencounter set is the first window union the later chapter blocks. -/
lemma reencounter_filter_eq (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h) (ht : t < gap n k) :
    ((Finset.range ((h ^ n - k ^ n) ^ n)).filter
        (fun m => radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m))) =
      Finset.range (gap n k - t) ∪
        (laterMeetings n k (h ^ n - k ^ n)).biUnion (chapterOffsets n k t) := by
  set Δ := h ^ n - k ^ n
  have hnn : n ≠ 0 := by omega
  ext m
  simp only [mem_filter, mem_range, mem_union, mem_biUnion]
  constructor
  · intro ⟨_, heq⟩
    rw [reencounter_iff_window_or_later n k h t m hn hkh ht] at heq
    rcases heq with hwin | hlat
    · exact Or.inl hwin
    · refine Or.inr ⟨leftChapter n k t m, hlat, ?_⟩
      have ⟨hlt, _, _⟩ := (mem_laterMeetings_iff n k Δ _).mp hlat
      have hle := pow_add_t_le_of_lt_chapter n k t _ hnn ht hlt
      refine (mem_chapterOffsets_iff n k t _ m hnn hle).mpr ?_
      exact ⟨irootN_pow_le n (k ^ n + t + m) hnn,
        irootN_lt_succ_pow n (k ^ n + t + m) hnn⟩
  · intro h
    rcases h with hwin | ⟨k', hk'mem, hmoff⟩
    · exact ⟨window_lt_delta_pow n k h t m hn hkh ht hwin,
        reencounter_of_lt_gap_sub n k h t m hn hkh ht hwin⟩
    · have ⟨hlt, hkΔ, _⟩ := (mem_laterMeetings_iff n k Δ k').mp hk'mem
      have hle := pow_add_t_le_of_lt_chapter n k t k' hnn ht hlt
      have hk'eq : leftChapter n k t m = k' :=
        leftChapter_of_mem_chapterOffsets n k t k' m hnn hle hmoff
      refine ⟨chapterOffset_lt_delta_pow n k t Δ k' m hnn hle hkΔ hmoff, ?_⟩
      rw [reencounter_iff_window_or_later n k h t m hn hkh ht]
      exact Or.inr (by rwa [hk'eq])

/-- **Total reencounter time.** The number of offsets at which the translated pair
`k^n + t, h^n + t` is equivalent is `(gap n k − t) + Σ_{k' later meeting} gap n k'`. -/
theorem reencounter_time (n k h t : ℕ) (hn : 2 ≤ n) (hkh : k < h) (ht : t < gap n k) :
    ((Finset.range ((h ^ n - k ^ n) ^ n)).filter
        (fun m => radRem n (k ^ n + t + m) = radRem n (h ^ n + t + m))).card
      = (gap n k - t) + ∑ k' ∈ laterMeetings n k (h ^ n - k ^ n), gap n k' := by
  set Δ := h ^ n - k ^ n
  have hnn : n ≠ 0 := by omega
  rw [reencounter_filter_eq n k h t hn hkh ht]
  have hdisj :
      Disjoint (range (gap n k - t))
        ((laterMeetings n k Δ).biUnion (chapterOffsets n k t)) := by
    refine disjoint_left.2 ?_
    intro m hmWin hmOff
    rcases mem_biUnion.mp hmOff with ⟨k', hk'mem, hmchap⟩
    have ⟨hlt, _, _⟩ := (mem_laterMeetings_iff n k Δ k').mp hk'mem
    exact disjoint_left.1 (disjoint_window_chapterOffsets n k t k' hnn ht hlt) hmWin hmchap
  have hpair := pairwiseDisjoint_chapterOffsets n k t Δ hnn ht
  rw [card_union_of_disjoint hdisj, card_range, card_biUnion hpair]
  congr 1
  refine sum_congr rfl ?_
  intro k' hk'
  have ⟨hlt, _, _⟩ := (mem_laterMeetings_iff n k Δ k').mp hk'
  exact card_chapterOffsets n k t k' (pow_add_t_le_of_lt_chapter n k t k' hnn ht hlt)

/-- Adjacent distance has no later meeting chapters (gaps are strictly monotone). -/
lemma laterMeetings_gap_empty (n k : ℕ) (hn : 2 ≤ n) :
    laterMeetings n k (gap n k) = ∅ := by
  ext k'
  simp only [mem_laterMeetings_iff, notMem_empty, iff_false, not_and]
  intro hlt _hkΔ hpow
  have hnn : n ≠ 0 := by omega
  have hΔ : 0 < gap n k := gap_pos' n k hnn
  have heq : radRem n (k' ^ n) = radRem n (k' ^ n + gap n k) := by
    refine (aodEquiv_add_iff_irootN n (k' ^ n) (gap n k) hn).mpr ?_
    simpa [irootN_perfectPow n k' hnn] using hpow
  have hgaple := gap_le_of_aodEquiv_add n (k' ^ n) (gap n k) hn hΔ heq
  rw [irootN_perfectPow n k' hnn] at hgaple
  have hgaplt := gap_strictMono n hn k k' hlt
  omega

/-- Adjacent chapters: the total reencounter time is the first window alone. -/
theorem reencounter_time_adjacent (n k t : ℕ) (hn : 2 ≤ n) (ht : t < gap n k) :
    ((Finset.range ((gap n k) ^ n)).filter
        (fun m => radRem n (k ^ n + t + m) = radRem n ((k + 1) ^ n + t + m))).card
      = gap n k - t := by
  have hkh : k < k + 1 := Nat.lt_succ_self k
  have hΔ : (k + 1) ^ n - k ^ n = gap n k := by
    simp [gap]
  have hcard := reencounter_time n k (k + 1) t hn hkh ht
  simp only [hΔ] at hcard
  simpa [laterMeetings_gap_empty n k hn] using hcard

end Reencounters
