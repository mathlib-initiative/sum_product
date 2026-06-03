/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.GoldenRatio
import SumProduct.UnitSeparation
import SumProduct.Blichfeldt
import SumProduct.Boxes
import SumProduct.Martinet
import SumProduct.AdditiveCount
import SumProduct.MultiplicativeCount
import SumProduct.EulerBound
import SumProduct.PartialZetaMellin
import SumProduct.RegulatorBound
import SumProduct.Construction

/-!
# The sum-product conjecture is false for real numbers

A Lean 4 / Mathlib formalization of the main results of

> T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov,
> *The sum-product conjecture is false for real numbers*.

The headline result is `SumProduct.sumProduct_false` (**Theorem 1.1**), conditional on
`SumProduct.MartinetTotallyRealTowers`: there is an absolute constant `c > 0` and arbitrarily large
finite sets `A ⊆ ℝ` with
`max (|A + A|) (|A * A|) ≤ |A| ^ (2 - c)`, i.e. the sum-product conjecture fails over `ℝ`.

`#print axioms sumProduct_false` reports only Lean's standard axioms. The single classical input
not yet available in Mathlib is an explicit hypothesis:

* `MartinetTotallyRealTowers` (in `SumProduct.Martinet`) — Theorem 3.2 (Martinet's totally real towers,
  `Δ_K ≤ C^d`), Martinet's theorem on asymptotically good totally real class field towers
  (proved via class field theory and the Golod–Shafarevich criterion).

The development's two analytic inputs are proved theorems, not assumptions:

* the per-ideal residue inequality `partialCompletedZetaResidue_le` — the analytic input to
  Lemma 3.1 `regulator_le_discr` (`R_K ≤ Δ_K`) — is proved in
  `SumProduct.PartialZetaMellin` using the in-repository `DedekindZeta` library (whose analytic
  background broadly follows Neukirch, *Algebraic Number Theory*, Chapter VII §§1 and 3–5) together
  with Mathlib's analytic class number formula; its Euler-product half (`ζ_K(2) ≤ 2^d`) is proved in
  `SumProduct.EulerBound`;
* `hensley_unitBox_volume` — equation (3.1) (Hensley / Ball–Vaaler cube-slice volume bound) — is
  proved in `SumProduct.CubeSectionHensley` via the elementary sinc-power integral bound and Fourier
  inversion (no Vaaler/Ball).

Both geometry-of-numbers lattice-point counts, **Lemma 3.5** (`lattice_count_add`) and **Lemma 3.7**
(`lattice_count_mult`), are proved.

## Module layout

* `SumProduct.GoldenRatio`          — golden-ratio numerics;
* `SumProduct.UnitSeparation`       — Lemma 3.6 (`unit_separation`);
* `SumProduct.Blichfeldt`           — an abstract Blichfeldt integral inequality;
* `SumProduct.Boxes`                — the additive / multiplicative / logarithmic boxes;
* `SumProduct.Martinet`                — the sole explicit classical hypothesis
  (Martinet's Theorem 3.2);
* `SumProduct.PartialZetaMellin`    — residue normalization and `partialCompletedZetaResidue_le`;
* `SumProduct.AdditiveCount`        — Lemma 3.5 (`lattice_count_add`);
* `SumProduct.MultiplicativeCount`  — Lemma 3.7 (`lattice_count_mult`);
* `SumProduct.CubeSectionHensley`   — eq. (3.1) as the theorem `hensley_unitBox_volume`;
* `SumProduct.EulerBound`           — the Euler-product bound `ζ_K(2) ≤ 2^d`;
* `SumProduct.RegulatorBound`       — Lemma 3.1 (`regulator_le_discr`);
* `SumProduct.Construction`         — §4 (Lemma 4.1) and Theorem 1.1 (`sumProduct_false`).
-/
