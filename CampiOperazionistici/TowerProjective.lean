/-
  TowerProjective.lean — Campi Operazionistici
  Projective Structure of the Family (Aod_n)_{n≥2}

  Paper: §19 (Tower Projective Structure)

  Formalizes the results on the projective structure of the family (Aod_n)_{n≥2}
  from the main paper (`main.pdf`):

  §1 — aodProfile: the operationistic profile and its injectivity
  §2 — Separation at logarithmic depth (T.proj.2)
  §3 — Transport formula r_{pn} and vertical stability (T.proj.3–4)
  §4 — Characterization of fibres (T.proj.5)
  §5 — Intersection of fibres and the divisibility lattice (conjecture)

  Dependencies:
  - CampiOperazionistici.SeparationVector (irootN_tower, aodInf_separates,
      tower_separation, aodEquiv_not_preserved_tower, fiberN, fiber_injective_aodInf)
  - CampiOperazionistici.FirstOccurrence (minCap, firstOcc, minCap_spec,
      minCap_minimal — used in §7 Fibre Counting)
-/

import CampiOperazionistici.SeparationVector
import CampiOperazionistici.FirstOccurrence

namespace CampiOperazionistici

/-! ─────────────────────────────────────────────────────────────────────────
    §1 — The Operationistic Profile and its Injectivity
    ─────────────────────────────────────────────────────────────────────────

    def aodProfile x n := radRem n x
    = the projection ι : ℕ → Πₙ≥₂ ℕ, x ↦ (r₂(x), r₃(x), r₄(x), …)

    Theorem T.proj.1: aodProfile is injective on {x | 2 ≤ x}.
    Proof: if aodProfile a = aodProfile b then r_m(a) = r_m(b) for
    every m, in particular for the witness given by aodInf_separates.
    ───────────────────────────────────────────────────────────────────────── -/

section AodProfile

/-- The operationistic profile of x: the sequence of radical remainders. -/
def aodProfile (x : ℕ) : ℕ → ℕ := fun n => radRem n x

/-- **T.proj.1 — Injectivity of the Profile** (§2.2):
    if the profiles of a and b coincide (on ℕ → ℕ), then a = b.
    Proof: aodInf_separates + congr_fun. -/
theorem aodProfile_injective {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : aodProfile a = aodProfile b) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := aodInf_separates a b ha hb hab
  exact hm (congr_fun h m)

/-- Contrapositive: a ≠ b implies that the profiles differ in some component. -/
theorem aodProfile_ne_of_ne {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    ∃ m : ℕ, aodProfile a m ≠ aodProfile b m :=
  aodInf_separates a b ha hb hab

end AodProfile


/-! ─────────────────────────────────────────────────────────────────────────
    §2 — Separation at Logarithmic Depth (T.proj.2)
    ─────────────────────────────────────────────────────────────────────────

    The Tower Theorem (already proved in SeparationVector §7) guarantees
    that separation occurs within level M = ⌊log₂(max a b)⌋ + 1.
    Here we restate it in terms of aodProfile.
    ───────────────────────────────────────────────────────────────────────── -/

section AodProfileSeparation

/-- **T.proj.2 — Separation at Logarithmic Depth**:
    for a ≠ b with a, b ≥ 2, the profiles already differ at the component
    M = ⌊log₂(max a b)⌋ + 1. -/
theorem aodProfile_separates_at_log {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    aodProfile a (Nat.log2 (max a b) + 1) ≠ aodProfile b (Nat.log2 (max a b) + 1) := by
  simp only [aodProfile]
  obtain ⟨n, hn_le, hn_sep⟩ := tower_separation a b ha hb hab
  -- The tower witness satisfies n ≤ M; we use n = M directly
  -- (which is the constructive witness of the tower_separation proof)
  simp only [aodSeparates] at hn_sep
  -- We re-prove the separation at level M = log₂(max a b) + 1
  have hmax_pos : 0 < max a b := by omega
  -- Note: lt_pow_log2_succ is private in SeparationVector; we re-prove it inline.
  have hM_gt : max a b < 2 ^ (Nat.log2 (max a b) + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hMa : 2 ^ (Nat.log2 (max a b) + 1) > a := (Nat.le_max_left a b).trans_lt hM_gt
  have hMb : 2 ^ (Nat.log2 (max a b) + 1) > b := (Nat.le_max_right a b).trans_lt hM_gt
  rw [radRem_large_grade _ a hMa ha, radRem_large_grade _ b hMb hb]
  omega

end AodProfileSeparation


/-! ─────────────────────────────────────────────────────────────────────────
    §3 — Transport Formula r_{pn} and Vertical Stability
    ─────────────────────────────────────────────────────────────────────────

    T.proj.3: r_{pn}(x) = [(j^p + s)^n - j^{pn}] + r_n(x)
    where j = κ_p(κ_n(x)) and s = r_p(κ_n(x)).

    T.proj.4: if κ_n(x) is a perfect p-th power (s = 0),
    then r_{pn}(x) = r_n(x).
    ───────────────────────────────────────────────────────────────────────── -/

section TowerFormula

/-- Auxiliary lemma: (j^p)^n = j^(p*n). -/
private lemma pow_mul_comm (j p n : ℕ) : (j ^ p) ^ n = j ^ (p * n) := by
  rw [← pow_mul]

/-- **T.proj.3 — Transport Formula** (§3.2):
    r_{pn}(x) = (j^p + s)^n - j^(pn) + r_n(x)
    where m = κ_n(x), j = κ_p(m), s = r_p(m).

    Derivation:
      x = m^n + r_n(x)       [definition of κ_n and r_n]
      m = j^p + s             [definition of κ_p and r_p]
      κ_{pn}(x) = j           [Tower Lemma: irootN_tower]
      r_{pn}(x) = x - j^{pn}
                = (m^n + r_n(x)) - j^{pn}
                = ((j^p + s)^n + r_n(x)) - j^{pn}  -/
theorem radRem_tower_formula (p n x : ℕ) (hp : n ≠ 0) (hn : p ≠ 0) :
    let m := irootN n x
    let j := irootN p m
    let s := radRem p m
    radRem (p * n) x = (j ^ p + s) ^ n - j ^ (p * n) + radRem n x := by
  set m := irootN n x with hm_def
  set j := irootN p m with hj_def
  set s := radRem p m with hs_def
  -- κ_{pn}(x) = j via the Tower Lemma
  have htower : irootN (p * n) x = j := irootN_tower p n x hp hn
  have hpn_ne : p * n ≠ 0 := Nat.mul_ne_zero hn hp
  -- r_{pn}(x) = x - j^{pn}
  have hrpn : radRem (p * n) x = x - j ^ (p * n) := by
    rw [radRem_eq_sub (p * n) x hpn_ne, htower]
  -- x = m^n + r_n(x): from radRem_eq_sub + irootN_pow_le
  have hle_mn : m ^ n ≤ x := by
    exact irootN_pow_le n x hp
  have hrn_eq : radRem n x = x - m ^ n := by
    have h := radRem_eq_sub n x hp; exact h
  have hx : x = m ^ n + radRem n x := by omega
  -- m = j^p + s: from radRem_eq_sub + irootN_pow_le
  have hle_jp : j ^ p ≤ m := irootN_pow_le p m hn
  have hs_eq : s = m - j ^ p := by
    have h := radRem_eq_sub p m hn; omega
  have hm_eq : m = j ^ p + s := by omega
  -- Substitute
  have hm_pow : m ^ n = (j ^ p + s) ^ n := by rw [hm_eq]
  -- j^(p*n) = (j^p)^n ≤ (j^p+s)^n
  have hB_le_A : j ^ (p * n) ≤ (j ^ p + s) ^ n := by
    have h1 : j ^ (p * n) = (j ^ p) ^ n := by rw [← pow_mul]
    rw [h1]; exact Nat.pow_le_pow_left (Nat.le_add_right _ _) n
  -- j^(pn) ≤ x
  have hle_jpn : j ^ (p * n) ≤ x := hB_le_A.trans (hm_pow ▸ hle_mn)
  -- We prove the equality by converting everything to ℤ with explicit casts,
  -- avoiding zify which fails to simplify the nat-subtractions with set-abbrev
  have key : (radRem (p * n) x : ℤ) =
      ((j ^ p + s) ^ n : ℤ) - (j ^ (p * n) : ℤ) + (radRem n x : ℤ) := by
    have hrpn_z : (radRem (p * n) x : ℤ) = (x : ℤ) - (j : ℤ) ^ (p * n) := by
      have := hrpn; zify [hle_jpn] at this; exact this
    linarith [hrn_eq.symm.trans (rfl : radRem n x = x - m ^ n),
              show (m : ℤ) ^ n = ((j : ℤ) ^ p + s) ^ n by exact_mod_cast hm_pow]
  exact_mod_cast key

/-- **T.proj.4 — Vertical Stability** (§3.3):
    if κ_n(x) is a perfect p-th power (r_p(κ_n(x)) = 0),
    then r_{pn}(x) = r_n(x). -/
theorem radRem_tower_perfect_chap (p n x : ℕ) (hp : n ≠ 0) (hn : p ≠ 0)
    (hperf : radRem p (irootN n x) = 0) :
    radRem (p * n) x = radRem n x := by
  have h := radRem_tower_formula p n x hp hn
  simp only at h
  -- s = 0, so (j^p + 0)^n - j^{pn} = j^{pn} - j^{pn} = 0
  rw [hperf] at h
  simp only [add_zero] at h
  rw [h]
  rw [← pow_mul]
  omega

end TowerFormula


/-! ─────────────────────────────────────────────────────────────────────────
    §4 — Characterization of Fibres (T.proj.5)
    ─────────────────────────────────────────────────────────────────────────

    The fibre fiberN(n, t) = {x | r_n(x) = t ∧ irootN n x ≥ 1}
    (already defined in SeparationVector §5 as a Set ℕ with explicit witness).

    Note: fiberN n t is defined as {x | ∃ k ≥ 1, t < gap n k ∧ x = k^n+t}.
    The lemma mem_fiberN_iff characterizes this fibre in terms of radRem.
    ───────────────────────────────────────────────────────────────────────── -/

section FiberCharacterization

/-- **T.proj.5 — Characterization of Fibres**:
    x ∈ fiberN n t ↔ radRem n x = t ∧ 1 ≤ irootN n x.
    Proof: direct from the definition + radRem_base_add and sum_in_chapter. -/
theorem mem_fiberN_iff (n t x : ℕ) (hn : 2 ≤ n) :
    x ∈ fiberN n t ↔ radRem n x = t ∧ 1 ≤ irootN n x := by
  have hnn : n ≠ 0 := by omega
  constructor
  · rintro ⟨k, hk, ht, rfl⟩
    refine ⟨radRem_base_add n k t hnn ht, ?_⟩
    -- irootN n (k^n + t) = k, so k ≥ 1 implies irootN ≥ 1
    rw [sum_in_chapter n k t hnn ht]
    exact hk
  · intro ⟨hrr, hkge⟩
    set k := irootN n x
    use k, hkge
    refine ⟨?_, ?_⟩
    · -- t < gap n k: radRem n x < gap n k
      rw [← hrr]
      exact radRem_lt_gap n x hnn
    · -- x = k^n + t
      rw [← hrr]
      have hle : k ^ n ≤ x := irootN_pow_le n x hnn
      have heq : radRem n x = x - k ^ n := radRem_eq_sub n x hnn
      omega

end FiberCharacterization


/-! ─────────────────────────────────────────────────────────────────────────
    §5 — Intersection of Fibres and the Divisibility Lattice
    ─────────────────────────────────────────────────────────────────────────

    **Main result (t = 0, completely proved):**
      fiberN(n, 0) ∩ fiberN(p, 0) = fiberN(lcm(n, p), 0)
    That is: n-th powers ∩ p-th powers = lcm-th powers.
    See `fiberN_zero_inter_eq_lcm`.

    **Why the case t ≥ 1 is more subtle:**
    The statement `fiberN n t ∩ fiberN p t = fiberN (lcm n p) t` is FALSE
    for large t. Counterexample: n=2, p=4, lcm=4, k=1, t=3.
      k^4 + 3 = 4 ∈ fiberN(4,3)?  No: irootN(4,4)=1, radRem(4,4)=3 ✓
      but 4 ∉ fiberN(2,3): irootN(2,4)=2, radRem(2,4)=0 ≠ 3.
    Computationally: gap(n, k^c) ≪ gap(lcm, k) in general (ratio → 0),
    so t < gap(lcm,k) does NOT imply t < gap(n, k^c).

    **Conditional version (formalized below):**
    With the additional hypothesis of compatibility of t with the degree n along
    the tower (ht_compat), the ⊇ direction holds.

    **⊆ direction:** Completely proved (proof via (c^q+1)^n ≤ (c+1)^(nq)).
    ───────────────────────────────────────────────────────────────────────── -/

section FiberIntersection

/-  Helper: if j^n = h^p (with n,p ≥ 2), then ∃ c ≥ 1, c^(lcm n p) = j^n.
    Proof: by Nat.exists_eq_pow_of_pow_eq_pow we get j = c^(p/gcd n p),
    and lcm n p = n * (p / gcd n p), so c^(lcm n p) = (c^(p/gcd))^n = j^n. -/
private lemma pow_eq_pow_lcm {n p j h : ℕ} (hn : n ≠ 0) (hp : p ≠ 0)
    (hj : 1 ≤ j) (heq : j ^ n = h ^ p) :
    ∃ c ≥ 1, c ^ Nat.lcm n p = j ^ n := by
  obtain ⟨c, hj_eq, _⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hn) heq
  -- hj_eq : j = c ^ (p / gcd n p)
  -- c ≥ 1 since j ≥ 1
  have hc_pos : 1 ≤ c := by
    by_contra hlt; push_neg at hlt
    interval_cases c
    -- c = 0: j = 0^(p/gcd) = 0, contradicts hj : 1 ≤ j
    rw [zero_pow] at hj_eq
    · omega
    · -- p / gcd n p ≠ 0 since gcd n p ∣ p and p ≠ 0
      intro h
      rw [Nat.div_eq_zero_iff] at h
      rcases h with h | h
      · exact absurd h (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right hp)).ne'
      · exact absurd (Nat.gcd_dvd_right n p) (Nat.not_dvd_of_pos_of_lt (by omega) h)
  use c, hc_pos
  -- lcm n p = n * (p / gcd n p), so c^(lcm n p) = (c^(p/gcd))^n = j^n
  have hlcm : Nat.lcm n p = n * (p / Nat.gcd n p) := by
    rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right n p)]
  rw [hlcm, hj_eq, ← pow_mul, mul_comm]

/-  Helper: if k ≥ 1, lcm = n*c (with n | lcm(n,p)), and t < gap(n, k^c),
    then k^lcm + t ∈ fiberN n t.

    Note: the relevant hypothesis is t < gap(n, k^c), NOT t < gap(lcm, k).
    Computationally gap(n, k^c) ≪ gap(lcm, k) in general, so
    t < gap(lcm, k) does not imply t < gap(n, k^c).
    The hypothesis ht_n is therefore necessary and not derivable from ht. -/
private lemma fiberN_lcm_sub_n (n p t k : ℕ) (hn : 2 ≤ n) (_hp : 2 ≤ p)
    (hk : 1 ≤ k) (_ht : t < gap (Nat.lcm n p) k)
    (ht_n : t < gap n (k ^ (Nat.lcm n p / n))) :
    k ^ Nat.lcm n p + t ∈ fiberN n t := by
  have hnn : n ≠ 0 := by omega
  -- n | lcm n p
  have hn_dvd : n ∣ Nat.lcm n p := Nat.dvd_lcm_left n p
  obtain ⟨c, hc_eq⟩ := hn_dvd
  -- c = lcm / n
  have hc_val : c = Nat.lcm n p / n := by
    have := Nat.mul_div_cancel_left c (show 0 < n by omega)
    rw [← hc_eq] at this; exact this.symm
  -- k^(lcm) = (k^c)^n
  have hpow : k ^ Nat.lcm n p = (k ^ c) ^ n := by
    rw [hc_eq, ← pow_mul, mul_comm, pow_mul]
  -- k^c ≥ 1
  have hkc : 1 ≤ k ^ c := Nat.one_le_pow c k (by omega)
  -- Rewrite ht_n in terms of c
  have ht_n' : t < gap n (k ^ c) := by rw [hc_val]; exact ht_n
  -- Assemble: k^lcm + t = (k^c)^n + t ∈ fiberN n t
  rw [hpow]
  exact ⟨k ^ c, hkc, ht_n', rfl⟩

/-- Key lemma: (c^q + 1)^n ≤ (c + 1)^(n*q) for c ≥ 1, q ≥ 1, n ≥ 1.
    Proof: (c+1)^q ≥ c^q + 1 (binomial), then raise to the n. -/
private lemma pow_succ_le_succ_pow_mul (c q n : ℕ) (hc : 1 ≤ c) (hq : 1 ≤ q) :
    (c ^ q + 1) ^ n ≤ (c + 1) ^ (n * q) := by
  -- Step 1: (c+1)^q ≥ c^q + 1
  have hbinom : c ^ q + 1 ≤ (c + 1) ^ q := by
    induction q with
    | zero => omega  -- impossible: hq says 1 ≤ 0
    | succ q ih =>
      have hih : c ^ q ≤ (c + 1) ^ q := by
        rcases Nat.eq_zero_or_pos q with rfl | hq'
        · simp
        · linarith [ih (by omega)]
      have hpos : 1 ≤ (c + 1) ^ q := Nat.one_le_pow q (c + 1) (by omega)
      calc c ^ (q + 1) + 1
          = c * c ^ q + 1 := by ring
        _ ≤ c * (c + 1) ^ q + 1 := by linarith [Nat.mul_le_mul_left c hih]
        _ ≤ (c + 1) * (c + 1) ^ q := by linarith
        _ = (c + 1) ^ (q + 1) := by ring
  -- Step 2: (c^q + 1)^n ≤ ((c+1)^q)^n = (c+1)^(n*q)
  have hrw : (c + 1) ^ (n * q) = ((c + 1) ^ q) ^ n := by
    rw [← pow_mul, mul_comm]
  rw [hrw]
  exact Nat.pow_le_pow_left hbinom n

/-- **C.tower.fiber_inter** — Intersection of fibres of different degrees
    (conditional version for t ≥ 1):

    With the compatibility hypothesis `ht_compat` (that t is small enough
    relative to the gaps of degree n along the tower), we have:
      fiberN n t ∩ fiberN p t = fiberN (lcm n p) t.

    The ⊆ direction is proved without additional hypotheses.
    The ⊇ direction requires `ht_compat`, which is in general not derivable
    from t < gap(lcm, k) (computationally: gap(n, k^c) ≪ gap(lcm, k)).

    For the case t = 0 (without additional hypotheses), see `fiberN_zero_inter_eq_lcm`. -/
theorem fiberN_inter_eq_lcm (n p t : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p)
    (ht_compat : ∀ k ≥ 1, t < gap (Nat.lcm n p) k →
        t < gap n (k ^ (Nat.lcm n p / n)) ∧ t < gap p (k ^ (Nat.lcm n p / p))) :
    fiberN n t ∩ fiberN p t = fiberN (Nat.lcm n p) t := by
  have hnn : n ≠ 0 := by omega
  have hpn : p ≠ 0 := by omega
  have hlcm_ne : Nat.lcm n p ≠ 0 := by simp [Nat.lcm_eq_zero_iff]; omega
  ext x
  simp only [Set.mem_inter_iff, fiberN, Set.mem_setOf_eq]
  constructor
  · -- ⊆: x ∈ fiberN n t ∩ fiberN p t → x ∈ fiberN (lcm n p) t
    rintro ⟨⟨j, hj, hjt, rfl⟩, h, hhge, hht, hheq⟩
    have hjn_eq : j ^ n = h ^ p := by omega
    obtain ⟨c, hc, hcpow⟩ := pow_eq_pow_lcm hnn hpn hj hjn_eq
    use c, hc
    refine ⟨?_, ?_⟩
    · -- t < gap (lcm n p) c
      -- From pow_eq_pow_lcm: c^q = j where q = p / gcd(n,p), lcm = n*q
      -- So gap(lcm, c) = (c+1)^(n*q) - c^(n*q)
      --    gap(n, j)   = (j+1)^n - j^n = (c^q+1)^n - c^(n*q)
      -- By pow_succ_le_succ_pow_mul: (c^q+1)^n ≤ (c+1)^(n*q)
      -- So gap(n, j) ≤ gap(lcm, c), and t < gap(n, j) implies t < gap(lcm, c).
      simp only [gap]
      -- lcm n p = n * (p / gcd n p)
      have hq : Nat.lcm n p = n * (p / Nat.gcd n p) := by
        rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right n p)]
      -- From pow_eq_pow_lcm: j = c ^ (p / gcd n p)
      obtain ⟨c', hj_eq, _⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl hnn) hjn_eq
      -- c' = c (uniqueness of the root)
      have hc_eq : c = c' := by
        have hlcm_ge : 2 ≤ Nat.lcm n p :=
          le_trans hn (Nat.le_of_dvd (by omega) (Nat.dvd_lcm_left n p))
        have : c ^ Nat.lcm n p = c' ^ Nat.lcm n p := by
          rw [hcpow, hq, hj_eq, ← pow_mul, mul_comm]
        exact Nat.pow_left_injective (by omega : Nat.lcm n p ≠ 0) this
      subst hc_eq
      set q := p / Nat.gcd n p with hq_def
      -- j = c^q
      have hj_cq : j = c ^ q := hj_eq
      -- lcm = n * q
      have hlcm_nq : Nat.lcm n p = n * q := hq
      -- (c+1)^(n*q) - c^(n*q) > (c^q+1)^n - c^(n*q) ≥ t
      have hc_pos : 1 ≤ c := hc
      have hq_pos : 1 ≤ q := by
        rw [hq_def]
        exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n p)) (Nat.gcd_pos_of_pos_right n (by omega))
      -- (c^q+1)^n ≤ (c+1)^(n*q)
      have hkey : (c ^ q + 1) ^ n ≤ (c + 1) ^ (n * q) :=
        pow_succ_le_succ_pow_mul c q n hc_pos hq_pos
      -- t < (j+1)^n - j^n = (c^q+1)^n - c^(n*q)
      rw [hj_cq] at hjt
      simp only [gap] at hjt
      -- (c^q)^n = c^(n*q)
      have hcqn : (c ^ q) ^ n = c ^ (n * q) := by rw [← pow_mul, mul_comm]
      -- j^n = c^(n*q)
      have hpow_j : j ^ n = c ^ (n * q) := by rw [hj_cq, ← pow_mul, mul_comm]
      -- c^lcm = c^(n*q)
      have hpow_lcm : c ^ Nat.lcm n p = c ^ (n * q) := by rw [hlcm_nq]
      -- t < (c^q+1)^n - c^(n*q) from hjt
      have hhjt : t < (c ^ q + 1) ^ n - c ^ (n * q) := by linarith [hcqn.symm ▸ hjt]
      -- Assemble: t < (c+1)^lcm - c^lcm
      have hgoal_rw : (c + 1) ^ Nat.lcm n p = (c + 1) ^ (n * q) := by rw [hlcm_nq]
      rw [hgoal_rw, hpow_lcm]
      -- Need: t < (c+1)^(n*q) - c^(n*q)
      -- Have: t < (c^q+1)^n - c^(n*q)  and  (c^q+1)^n ≤ (c+1)^(n*q)
      have hle : c ^ (n * q) ≤ (c ^ q + 1) ^ n := by linarith [hcqn ▸ Nat.pow_le_pow_left (by omega : c^q ≤ c^q+1) n]
      omega
    · rw [← hcpow]
  · -- ⊇: x ∈ fiberN (lcm n p) t → x ∈ fiberN n t ∩ fiberN p t
    --   Requires ht_compat to guarantee t < gap(n, k^c) and t < gap(p, k^d).
    rintro ⟨k, hk, hkt, rfl⟩
    obtain ⟨htn, htp⟩ := ht_compat k hk hkt
    have hkt' : t < gap (Nat.lcm p n) k := by rwa [Nat.lcm_comm]
    obtain ⟨htp', _⟩ := ht_compat k hk (by rwa [Nat.lcm_comm])
    have hmem_n : k ^ Nat.lcm n p + t ∈ fiberN n t :=
      fiberN_lcm_sub_n n p t k hn hp hk hkt htn
    have hmem_p : k ^ Nat.lcm p n + t ∈ fiberN p t :=
      fiberN_lcm_sub_n p n t k hp hn hk hkt' (by rwa [Nat.lcm_comm])
    rw [Nat.lcm_comm] at hmem_p
    exact ⟨hmem_n, hmem_p⟩

/-- Lemma: 0 < gap n k for every k ≥ 1 and n ≥ 1. -/
private lemma gap_pos (n k : ℕ) (hn : 1 ≤ n) (_ : 1 ≤ k) : 0 < gap n k := by
  simp only [gap]
  have h : k ^ n < (k + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- **Special case t = 0** (completely proved):
    fiberN n 0 ∩ fiberN p 0 = fiberN (lcm n p) 0.
    That is: n-th powers ∩ p-th powers = lcm(n,p)-th powers. -/
theorem fiberN_zero_inter_eq_lcm (n p : ℕ) (hn : 2 ≤ n) (hp : 2 ≤ p) :
    fiberN n 0 ∩ fiberN p 0 = fiberN (Nat.lcm n p) 0 := by
  have hnn : n ≠ 0 := by omega
  have hpn : p ≠ 0 := by omega
  have hlcm_ne : Nat.lcm n p ≠ 0 := by simp [Nat.lcm_eq_zero_iff]; omega
  have hlcm_ge : 2 ≤ Nat.lcm n p := le_trans hn (Nat.le_of_dvd (by omega) (Nat.dvd_lcm_left n p))
  ext x
  simp only [Set.mem_inter_iff, fiberN, Set.mem_setOf_eq]
  constructor
  · -- ⊆: x = j^n + 0 = h^p + 0 → x = c^lcm + 0
    rintro ⟨⟨j, hj, -, rfl⟩, h, hhge, -, hheq⟩
    simp only [add_zero] at hheq ⊢
    have hjn_eq : j ^ n = h ^ p := by linarith
    obtain ⟨c, hc, hcpow⟩ := pow_eq_pow_lcm hnn hpn hj hjn_eq
    exact ⟨c, hc, gap_pos _ c (by omega) hc, by linarith⟩
  · -- ⊇: x = k^lcm + 0 → x = (k^c)^n + 0 and x = (k^d)^p + 0
    rintro ⟨k, hk, -, rfl⟩
    simp only [add_zero]
    obtain ⟨c, hc_eq⟩ := Nat.dvd_lcm_left n p
    obtain ⟨d, hd_eq⟩ := Nat.dvd_lcm_right n p
    have hpow_n : k ^ Nat.lcm n p = (k ^ c) ^ n := by rw [hc_eq, ← pow_mul, mul_comm, pow_mul]
    have hpow_p : k ^ Nat.lcm n p = (k ^ d) ^ p := by rw [hd_eq, ← pow_mul, mul_comm, pow_mul]
    have hkc : 1 ≤ k ^ c := Nat.one_le_pow c k (by omega)
    have hkd : 1 ≤ k ^ d := Nat.one_le_pow d k (by omega)
    exact ⟨⟨k ^ c, hkc, gap_pos n (k ^ c) (by omega) hkc, by linarith⟩,
           ⟨k ^ d, hkd, gap_pos p (k ^ d) (by omega) hkd, by linarith⟩⟩

end FiberIntersection


/-! ─────────────────────────────────────────────────────────────────────────
    §6 — Non-Preservation and the Correct Projective Structure
    ─────────────────────────────────────────────────────────────────────────

    Restatement of the results of SeparationVector §6 in the terminology
    of the profile: the correct projective structure is the injective embedding
    ι : ℕ → Π_{n≥2} ℕ, x ↦ (r_n(x))_{n≥2}, not a categorical projective
    limit (the transition maps do not exist by §1.2).
    ───────────────────────────────────────────────────────────────────────── -/

section ProjectiveStructure

/-- Reformulation: the profile is the map ι : ℕ → (ℕ → ℕ) that encodes
    the embedding of ℕ into the product. -/
abbrev aodEmbedding : ℕ → (ℕ → ℕ) := aodProfile

/-- The embedding is injective on {x | 2 ≤ x} (direct from T.proj.1). -/
theorem aodEmbedding_injective :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → aodEmbedding a = aodEmbedding b → a = b :=
  fun _ _ ha hb h => aodProfile_injective ha hb h

/-- Non-preservation confirms that the image of ι does not coincide with
    the categorical projective limit (already proved in SeparationVector §6). -/
theorem no_projective_transition_maps :
    ¬ ∀ (p n a b : ℕ), 2 ≤ n → 2 ≤ p →
      a ≡ₒ b [Aod n] → a ≡ₒ b [Aod (p * n)] :=
  aodEquiv_not_preserved_tower

end ProjectiveStructure

/-! ─────────────────────────────────────────────────────────────────────────
    §7 — Fibre Counting in Bounded Intervals
    ─────────────────────────────────────────────────────────────────────────

    Having established the fibre structure (fiberN, mem_fiberN_iff in §4),
    we quantify: how many preimages of r under radRem(n,·) lie in [0,N]?

    Element characterisation: radRem n a = r iff a = k^n + r for some
    k ≥ minCap(n,r). Spacing: consecutive preimages differ by gap(n,k).
    Count: |{a ≤ N : radRem n a = r}| = irootN(n, N-r) − minCap(n,r) + 1
    (for r ≥ 1 and N ≥ firstOcc(n,r)).

    This ties together SeparationVector §5 (fibre definition), FirstOccurrence
    (minCap κ_n(r), firstOcc f_n(r)), and the Tower Projective §4 structure.
    ───────────────────────────────────────────────────────────────────────── -/

section FiberCounting

/-- **Preimage forward**: if minCap(n,r) ≤ k, then radRem(n, k^n+r) = r.
    Consequence of `minCap_spec` + monotonicity `gap_le_of_add` + `radRem_base_add`. -/
theorem preimage_radRem_eq (n r k : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0)
    (hk : minCap n r hn ≤ k) : radRem n (k ^ n + r) = r := by
  have hlt_min : r < gap n (minCap n r hn) := minCap_spec n r hn hr
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  have hlt_k : r < gap n k := by
    rw [hd]; exact lt_of_lt_of_le hlt_min (gap_le_of_add n (minCap n r hn) d hn)
  exact radRem_base_add n k r (by omega) hlt_k

/-- **Element characterisation of the fibre** (r ≠ 0):
    radRem(n, a) = r iff a = k^n + r for some k ≥ minCap(n,r).
    This is Theorem T.proj.5 (fiberN characterization) made quantitative via κ. -/
theorem radRem_eq_iff_exists_k (n r a : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0) :
    radRem n a = r ↔ ∃ k : ℕ, minCap n r hn ≤ k ∧ a = k ^ n + r := by
  constructor
  · intro h
    refine ⟨irootN n a, ?_, ?_⟩
    · -- minCap ≤ irootN n a; need irootN n a ≥ 1 first
      have hroot_pos : 1 ≤ irootN n a := by
        by_contra hcontra
        push_neg at hcontra
        have hroot0 : irootN n a = 0 := by omega
        have hlt_gap : r < gap n (irootN n a) := by
          rw [← h]; exact radRem_lt_gap n a (by omega)
        rw [hroot0] at hlt_gap
        have hgap0 : gap n 0 = 1 := by
          simp [gap, Nat.zero_pow (show 0 < n by omega)]
        rw [hgap0] at hlt_gap
        omega
      have hlt : r < gap n (irootN n a) := by
        rw [← h]; exact radRem_lt_gap n a (by omega)
      exact minCap_minimal n r (irootN n a) hn hr hroot_pos hlt
    · -- a = (irootN n a)^n + r, from radRem n a = a - (irootN n a)^n = r
      have hrr : radRem n a = a - (irootN n a) ^ n := radRem_eq_sub n a (by omega)
      have hle : (irootN n a) ^ n ≤ a := irootN_pow_le n a (by omega)
      omega
  · rintro ⟨k, hk, rfl⟩
    exact preimage_radRem_eq n r k hn hr hk

/-- **Spacing of consecutive preimages**: at chapter k, the next preimage
    is exactly gap(n,k) away. -/
theorem preimage_spacing_at_k (n k r : ℕ) :
    (k + 1) ^ n + r - (k ^ n + r) = gap n k := by
  simp [gap]
  have hle : k ^ n ≤ (k + 1) ^ n := Nat.pow_le_pow_left (by omega) n
  omega

/-- The set of preimages of r in [0, N] parametrised by chapter index:
    {k | minCap(n,r) ≤ k ∧ k^n + r ≤ N} = Icc(minCap, irootN(n, N-r)). -/
def preimageChapterSet (n r N : ℕ) (hn : 2 ≤ n) : Finset ℕ :=
  if r = 0 then ∅
  else if N < r then ∅
  else Finset.Icc (minCap n r hn) (irootN n (N - r))

/-- The set of preimages of r under radRem(n, ·) within [0, N]. -/
def preimageSet (n r N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun a => radRem n a = r)

/-- Forward injection: distinct chapters give distinct preimages, because
    k^n is strictly monotone in k (for n ≥ 1). -/
lemma preimage_chapter_injective (n r : ℕ) (hn : 1 ≤ n) :
    Function.Injective (fun k : ℕ => k ^ n + r) := by
  intro k₁ k₂ hk
  simp at hk
  exact Nat.pow_left_injective (by omega) hk

/-- **Radical Counting Formula**: for r ≠ 0 and N ≥ firstOcc(n, r),
    the number of a ∈ [0, N] with radRem(n, a) = r is exactly
    irootN(n, N − r) − minCap(n, r) + 1.
    This is the bijection
    Icc(minCap(n,r), irootN(n, N−r)) ≃ {a ≤ N | radRem n a = r}
    given by k ↦ k^n + r. -/
theorem radical_count_formula (n r N : ℕ) (hn : 2 ≤ n) (hr : r ≠ 0)
    (hN : firstOcc n r hn ≤ N) :
    (preimageSet n r N).card =
      irootN n (N - r) - minCap n r hn + 1 := by
  -- Step 1: show preimageSet = image of Icc under (k ↦ k^n + r)
  have hNr : r ≤ N := by
    have : (minCap n r hn) ^ n + r = firstOcc n r hn := rfl
    have h1 : r ≤ firstOcc n r hn := by rw [← this]; omega
    omega
  have hmin_le_root : minCap n r hn ≤ irootN n (N - r) := by
    -- minCap n r hn ^ n ≤ N - r, then irootN monotonicity
    have hminpow : (minCap n r hn) ^ n ≤ N - r := by
      have hfo : (minCap n r hn) ^ n + r = firstOcc n r hn := rfl
      omega
    -- irootN is monotone in a for n ≥ 1
    have hmono : minCap n r hn ≤ irootN n ((minCap n r hn) ^ n) := by
      have := irootN_perfectPow n (minCap n r hn) (by omega)
      omega
    have hmono2 : irootN n ((minCap n r hn) ^ n) ≤ irootN n (N - r) :=
      irootN_mono n _ _ (by omega) hminpow
    exact le_trans hmono hmono2
  have himg :
      preimageSet n r N
        = (Finset.Icc (minCap n r hn) (irootN n (N - r))).image (fun k => k ^ n + r) := by
    apply Finset.ext
    intro a
    simp only [preimageSet, Finset.mem_filter, Finset.mem_range, Finset.mem_image,
               Finset.mem_Icc]
    constructor
    · rintro ⟨ha_le, ha_eq⟩
      obtain ⟨k, hk_min, rfl⟩ := (radRem_eq_iff_exists_k n r a hn hr).mp ha_eq
      refine ⟨k, ⟨hk_min, ?_⟩, rfl⟩
      -- k^n + r ≤ N → k^n ≤ N - r → k ≤ irootN n (N - r)
      have hk_pow : k ^ n ≤ N - r := by omega
      have : k ≤ irootN n (k ^ n) := by
        have := irootN_perfectPow n k (by omega); omega
      exact le_trans this (irootN_mono n _ _ (by omega) hk_pow)
    · rintro ⟨k, ⟨hk_min, hk_max⟩, rfl⟩
      refine ⟨?_, preimage_radRem_eq n r k hn hr hk_min⟩
      -- k^n + r ≤ N + 1: need k^n + r < N + 1 i.e. k^n + r ≤ N
      -- k ≤ irootN n (N - r) gives k^n ≤ N - r
      have hk_pow : k ^ n ≤ N - r := by
        have hle := irootN_pow_le n (N - r) (by omega)
        exact le_trans (Nat.pow_le_pow_left hk_max n) hle
      omega
  rw [himg, Finset.card_image_of_injective _ (preimage_chapter_injective n r (by omega))]
  rw [Nat.card_Icc]
  omega

/- Computational check: preimages of r = 5 under radRem(3, ·) in [0, 50]
    are {6, 13, 32} (values k = 1, 2, 3; 4³+5 = 69 > 50). Formula:
    minCap 3 5 = 1 (gap 3 1 = 7 > 5), irootN 3 (50-5) = irootN 3 45 = 3
    (3³ = 27 ≤ 45 < 64 = 4³). Count = 3 − 1 + 1 = 3. ✓ -/
#eval (preimageSet 3 5 50).card          -- expected 3
#eval minCap 3 5 (by omega)              -- expected 1
#eval irootN 3 (50 - 5)                  -- expected 3

end FiberCounting

end CampiOperazionistici
