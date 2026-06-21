# Operationistic Grasslands

**A Radical-Remainder Quotient Structure on ℕ — formally verified in Lean 4 / Mathlib4**

This repository contains the complete Lean 4 formalization accompanying the paper
*Operationistic Grasslands: A Radical-Remainder Quotient Structure on ℕ*.

---

## Overview

An *Operationistic Grassland* is a family of algebraic structures on the natural
numbers ℕ built from idempotent arithmetic projections `φ : ℕ → ℕ`, of which
classical modular arithmetic is the degenerate flat case. The central subclass —
the *Radical Grasslands* (Italian: *Campi Operazionistici*), indexed by a degree
`n ≥ 2` — uses the **radical remainder**

```
rₙ(a) := a − ⌊a^(1/n)⌋ⁿ
```

as its canonical projection. The induced equivalence classes (called *chapters*)
are integer intervals of strictly increasing width, each carrying natural algebraic
operations.

The theory rests on three pillars:

- **Locally** — every chapter carries a commutative ring isomorphic to `ℤ/gap(n,k)ℤ`,
  yielding a Galois field when the chapter width is prime.
- **Between chapters** — a geometry of translations (the *First Jump Theorem*, the
  *Capitolar Groupoid*, and the *Universal Tiling Decomposition*) governs how
  radical-remainder equivalence is created and destroyed.
- **Globally** — the *Tower Separation Theorem* shows that distinct integers
  `a ≠ b ≥ 2` are always separated by some `Aodₙ` at logarithmic depth.

---

## Repository Layout

```
CampiOperazionistici.lean        Root module (re-exports every module below)
Main.lean                        Trivial executable entry point
lakefile.lean                    Lake package definition
lean-toolchain                   Pinned Lean version (v4.29.0-rc2)
lake-manifest.json               Pinned Mathlib + dependency revisions
CampiOperazionistici/            Library source (19 modules)
```

### Modules (dependency order)

| # | Module | Contents |
|---|--------|----------|
| 1 | `CampiOperazionistici.lean` | Foundation: `irootN`, `radRem`, `aodEquiv`, `isPerfectPower`, `gap`, growing frontier |
| 2 | `GroupStructure.lean` | Ring/field structure on each chapter; isomorphism `Fin(gap) ≅ ℤ/gap` |
| 3 | `aoddepth.lean` | Operational depth `δₙ(a)` via iterated `radRem` |
| 4 | `OperationisticGrassland.lean` | The general framework (idempotent projections); base-`B` chapter ring/field |
| 5 | `fiveDirections.lean` | Five arithmetic analogues: Fermat-AOD, totient, Radical CRT, Wilson, Euler |
| 6 | `GrasslandFiveDirections.lean` | General-grassland form of Directions I/II/IV/V via the base map `θ_B` (Dir III stays radical) |
| 7 | `MeadowLocal.lean` | Local meadow structures; M3-good cardinality for composite gaps |
| 8 | `TranslationReencounter.lean` | Translation reencounters and the First Jump Theorem |
| 9 | `CapitolarTranslations.lean` | Capitolar translations `τⱼ`, subtraction shift `σ`, operation invariance |
| 10 | `FirstOccurrence.lean` | First-occurrence map `fₙ`, minCap `κₙ`, the Power Bound |
| 11 | `CapitolarGroupoid.lean` | `CategoryTheory.Groupoid` instance; Universal Tiling Decomposition |
| 12 | `CapitolarTransportStructure.lean` | Transport of group structure along `τⱼ` |
| 13 | `GrasslandFlatLimit.lean` | Global grasslands as gap sequences; deformation functionals (slope/σ/κ), flat/affine hierarchy, Keystone & Synchronization theorems |
| 14 | `AodInfinito.lean` | Infinite Radical Profile Structure Aod∞; Fundamental Theorem |
| 15 | `SeparationVector.lean` | Separation vector and the Tower Separation Theorem |
| 16 | `TowerProjective.lean` | Tower projective structure; Fibre Intersection Theorem |
| 17 | `AodStar.lean` | Universal Radical Quotient Aod★ via max perfect power `mpp` |
| 18 | `AodStarAlgebra.lean` | Radical Star Algebra: impossibility theorem + commutative magma |
| 19 | `AodStarTree.lean` | Radical Star Tree: tree metric on ℕ, LCA and sibling-distance theorems |

---

## Key Definitions

| Symbol | Lean name | Meaning |
|--------|-----------|---------|
| `irootN n a` | `irootN` | ⌊a^(1/n)⌋ (fuel-based integer n-th root) |
| `rₙ(a)` | `radRem` | `a − irootN(n,a)ⁿ` |
| `gap(n,k)` | `gap` / `capGap` | `(k+1)ⁿ − kⁿ` (chapter width) |
| `a ≡ b [Aodₙ]` | `aodEquiv` | `rₙ(a) = rₙ(b)` |
| `δₙ(a)` | `aodDepth` | steps to reach 0 via iterated `rₙ` |
| `mpp a` | `mpp` | largest perfect power of any degree ≥ 2, `≤ a` |
| `r★(a)` | `radRemStar` | `a − mpp(a)` (universal radical remainder) |
| `τⱼ(a)` | `tauJ` | shift `a` by `j` chapters |

---

## Building

This project uses [Lake](https://github.com/leanprover/lake) and Mathlib4.

```bash
lake exe cache get   # fetch prebuilt Mathlib .olean artifacts (recommended; avoids
                     # recompiling Mathlib from source)
lake build           # build the entire library
```

The exact toolchain and dependency revisions are pinned in `lean-toolchain` and
`lake-manifest.json`:

- **Lean 4** — `v4.29.0-rc2`
- **Mathlib4** — pinned revision (see `lake-manifest.json`)

> **Note on the Mathlib cache.** The `.lake/` directory (Mathlib source plus
> compiled `.olean` artifacts) is intentionally **not** committed — it is several
> GB and reproducible. If `.lake/` is already present alongside this checkout,
> `lake build` reuses it directly. Otherwise the first `lake build` will fetch and
> compile Mathlib, which can take a long time. Do not interrupt an in-progress
> build, as that can trigger a full Mathlib re-download.

To check a single file's diagnostics without a full build, open it in VS Code with
the `lean4` extension, or run:

```bash
lake env lean CampiOperazionistici/CampiOperazionistici.lean
```

---

## Formalization Status

All results marked with the symbol **`✓ (lv)`** in the paper are machine-checked.
The codebase contains only **two** intentional `sorry`s, each a classical or deep
result left open by design:

- `weakZero_count_asymptotic` (Aod∞) — asymptotic density of weak zeros `~ √N`
  (classical; Hardy–Wright §18.1).
- `catalan_in_AodStar` (Aod★) — the only consecutive perfect powers `≥ 2` are 8
  and 9 (Catalan–Mihăilescu), awaiting a Mathlib4 port.

Every other module is fully proved.

---

## Citation

If you use this formalization, please cite it via [`CITATION.cff`](CITATION.cff):

> Sgarbi, Alessandro
> ([ORCID 0009-0005-4528-964X](https://orcid.org/0009-0005-4528-964X)).
> *Operationistic Grasslands: A Radical-Remainder Quotient Structure on ℕ.*

---

## License

Released under the **GNU General Public License v3.0** — see [`LICENSE`](LICENSE).
