# The sum-product conjecture is false for real numbers

A Lean 4 / Mathlib formalization of the main result of

> T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov,
> *The sum-product conjecture is false for real numbers*.

Formalization by Formal Frontier Team members Matthew Ballard, Fabian Glöckle, Bhavik Mehta, and
Adam Topaz, with support from others on the Formal Frontier Team.

> [!IMPORTANT]
> **This is a formalization conditional on one explicit classical hypothesis.** The headline
> theorem `sumProduct_false` takes a proof of `MartinetTotallyRealTowers` (Martinet's
> asymptotically-good totally real towers, `Δ_K ≤ C^d`) as an argument. This statement rests on
> Martinet's class-field-tower construction — class field theory plus the Golod–Shafarevich
> criterion for infinite `p`-class field towers — not yet in Mathlib. For the full picture
> (statement-to-declaration alignment, fidelity/divergences, review status, which explicit hypotheses
> are used, and exactly which axioms `#print axioms sumProduct_false` reports), see the
> machine-readable [`formalization.yaml`](formalization.yaml) at the repository root.

## Main result

`SumProduct.sumProduct_false` (**Theorem 1.1**), from the hypothesis
`hMartinet : SumProduct.MartinetTotallyRealTowers`: there is an absolute constant `c > 0` such that
there are arbitrarily large finite sets `A ⊆ ℝ` with

```
max (|A + A|) (|A * A|) ≤ |A| ^ (2 - c).
```

In other words, the sum-product conjecture `max(|A+A|, |A·A|) ≥ |A|^{2-o(1)}` is **false** over `ℝ`.

The challenge statement, as given to comparator ([`Challenge.lean`](Challenge.lean), imports only
Mathlib), can also be viewed in the
[live Lean playground](https://live.lean-lang.org/#codez=PQWgUAwg9gDgngJwJYHMAWAXABACgMYCUWATAAzEBsWAYlAgLYCGANjQlAHYZICmCWAFR6N6AOiwBBZq2ToMAZywIe8vgDceAE1FgASj2bDVmrAFcOmvpJiM8aHiVGkszJHh4dVWRosvy8yABGWlhIHFgY9lgAZkiGWAAyAJIQAKIAcgDKqToSppF08gBcNHRMrNTsXLz8QiIANJJJkvLySPIYjFxgIMBgSPQwdNgAsoyRroFgYKAAhGAAxFjQg4wI43RYdiyGHCgO0ZuRDvaMmq4cDsd0PPTTAmjtoYrHEQimHSHb0h77WG2WGKbAAGhi6MHYGgQwDwUFW6wwdGB4iwSWwAyGCAUWE4zDgWDGEyQgUaHXGKgi9jAbT28TwzB8bTwLCwaDgQ2ObUUPAAHjBXHgkBg8Y0uiYUEgNC8oso1LwAO4ha7Kej%2FToYW4ebDyoVobxYfm2HhoKDMSwIMAQqBQaI6XrTWAef6wmAhdKmejBBDUXhmsCO8IABSgYQwOtU01AICwACoYw8eDdVQBmUTEOO4MZYsI8DAEUWKLpYXn8txC1nsqCc9o6MAJ5TPbzhRiBeSm%2FIOWGeTpcLDAiBYAB8WFIwP%2BpjslPGQP4YViHCFBnxTA4%2BMsKGUFOBmjHxwbT0YYERnWk%2BOULI4Hq9MV9JmBAGkxzasOvN32dzioX3AFiEY%2FlJq8TR2gCAYwi6bB5HGdpYi3QAU4AAfXvLBABMiZYAD0d1rAAiJIOHnRc8SwFd8W3YEsMbEtlFaEIfBKQ5%2BB4KESPSXd7H3QsXx4DceAcbcsEAUyIsBYqdtToABreRxHtSxogJNZuEuDABCrHY4H0FhlMVBBFBKQN2BgLAigAXjALAzKwQBgImWQysEAXEJGmcAAeazAHIiLBAAAiISbMAVEJGiskwSl8rzUJMFzTPMsyrJwJCSgEdkeCIHB4Jsn0DBMe9EuSkp3U9PhUrNLAMtwLKhKvPLb1EJJ5GUk88XU1gMvqcKIrMkYoE0UxDFEed1g4MSsG%2FQqsCMl8sDcgAfHAcq9fLtCA%2Fx%2BBiuyCHGlDrLQl9IxAaMBHeT4TFheENn4b5dj%2BMkNXoLUZ0pE5hHOHNbqTKS%2BmVW5x3oPT2onDB4OiFgvBwNAswU3MbJBnMlJU096s0vh5CIIpmssrYbPskcsGcvAxo8rzAr8yQUrCVRsHR9I1okURmQQULkbMnAcCYHlcAkLAAGpJAIKm1hMHBWZjTnuZpnzEeWta%2BaFgKxY2nBiCwaNCEMkbAjgcK2wQBA4CAA).

`#print axioms sumProduct_false` reports only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). The single classical input that is not (yet) available in Mathlib
is `MartinetTotallyRealTowers` (paper Theorem 3.2): Martinet's asymptotically good totally real
class field towers, `Δ_K ≤ C^d` (bounded root discriminant; class field theory +
Golod–Shafarevich). It is stated faithfully as an explicit proposition in `SumProduct.Martinet` and
passed as a theorem hypothesis.

The main formalized ingredients behind the construction are:

* `partialCompletedZetaResidue_le` (the per-ideal residue inequality: for each ideal class,
  `(2^rR/w) ≤ s(s−1)·completedPartialZeta_C(s)`) in `SumProduct.PartialZetaMellin`, using the
  in-repository `DedekindZeta` library (Hecke theta–Mellin theory and the theta inversion law)
  together with Mathlib's analytic class number formula `NumberField.dedekindZeta_residue` (used to
  pin the pole residue to `2^rR/w` with no geometric volume computation). `SumProduct.RegulatorBound`
  sums these partial inequalities over `ClassGroup (𝓞 K)` and obtains
  `dedekindZeta_completed_ge_residue` (`ρ ≤ s(s−1)Z_K(s)`). Specializing to totally real `K`
  (`r₂ = 0`) and dividing by `√|Δ_K|` gives `dedekindZeta_completed_residue_le`
  (`κ_K ≤ s(s-1)|Δ_K|^{(s-1)/2}π^{-ds/2}Γ(s/2)^d·ζ_K(s)`).
* `dedekindZeta_two_re_le` (`ζ_K(2) ≤ 2^d`) in `SumProduct.EulerBound`: the ideal-counting function
  `a_n = #{ideals of norm n}` is multiplicative and bounded by the `d`-fold divisor function `d_d`,
  so `ζ_K(2) = ∑ a_n/n² ≤ ∑ d_d(n)/n² = ζ(2)^d = (π²/6)^d ≤ 2^d`.
* `dedekind_residue_le` (`κ_K ≤ 2(2/π)^d √|Δ_K|`) and `regulator_le_discr` (`R_K ≤ Δ_K`,
  **Lemma 3.1**) in `SumProduct.RegulatorBound`, combining the completed-zeta residue bound,
  `dedekindZeta_two_re_le`, Mathlib's analytic class number formula, `h_K ≥ 1`, and `4 ≤ π^d`
  (for `d ≥ 2`).
* Equation (3.1) (`hensley_unitBox_volume`, the Hensley / Ball–Vaaler cube-slice volume bound) in
  `SumProduct.CubeSectionHensley`: it identifies `unitBox K r` with a sum-constrained cube, reduces
  its volume to the law of a sum of `d-1` independent uniforms on `[-1,1]`, identifies that law's
  interval probability with `(1/π)∫ (sin t/t)^d` by Fourier inversion, and bounds it with the
  elementary estimate `π/√d ≤ ∫ (sin t/t)^d ≤ 5π/√d` (constants `1` and `5` exactly the paper's; no
  appeal to Vaaler/Ball).
* The two geometry-of-numbers lattice-point counts: **Lemma 3.5** (`lattice_count_add`) and
  **Lemma 3.7** (`lattice_count_mult`).

Removing the one remaining hypothesis would require formalizing Martinet's class-field-tower
construction (class field theory plus the Golod–Shafarevich criterion for infinite `p`-class field
towers, yielding asymptotically good totally real towers), not currently in Mathlib. Until
then the development is **conditional on that single input**. The per-statement status is recorded
in [`formalization.yaml`](formalization.yaml).

## Module layout

| module | contents |
|--------|----------|
| `SumProduct.GoldenRatio`         | golden-ratio numerics |
| `SumProduct.UnitSeparation`      | Lemma 3.6 (`unit_separation`) |
| `SumProduct.Blichfeldt`          | an abstract Blichfeldt integral inequality |
| `SumProduct.Boxes`               | the additive / multiplicative / logarithmic boxes |
| `SumProduct.Martinet`               | the sole explicit classical hypothesis — Martinet's Theorem 3.2 (`MartinetTotallyRealTowers`) |
| `SumProduct.PartialZetaMellin`      | residue normalization and the per-ideal inequality `partialCompletedZetaResidue_le`, using the in-repository `DedekindZeta` library + Mathlib's class number formula |
| `SumProduct.AdditiveCount`       | Lemma 3.5 (`lattice_count_add`) |
| `SumProduct.MultiplicativeCount` | Lemma 3.7 (`lattice_count_mult`) |
| `SumProduct.SincIntegral`        | elementary sinc-power bound `π/√N ≤ ∫ (sin t/t)^N ≤ 5π/√N` |
| `SumProduct.CubeSection`         | `unitBox = cubeSection` identity, volume homogeneity, `Fin n ↔ ι` transport |
| `SumProduct.CubeSectionCore`     | sum-of-uniforms law, `charFun = sinc^n`, the Fourier-inversion bridge |
| `SumProduct.CubeSectionHensley`  | eq. (3.1) as the theorem `hensley_unitBox_volume` |
| `SumProduct.EulerBound`          | the Euler-product bound `ζ_K(2) ≤ 2^d` (`dedekindZeta_two_re_le`) |
| `SumProduct.RegulatorBound`      | `dedekind_residue_le` and Lemma 3.1 (`regulator_le_discr`), from the residue inequality + ACNF |
| `SumProduct.Construction`        | §4 (Lemma 4.1) and Theorem 1.1 (`sumProduct_false`) |

The root file `SumProduct.lean` imports all modules. The Dedekind-zeta analytic input is implemented
in the in-repository `DedekindZeta` library (under `DedekindZeta/`, declared as a `lean_lib` in
`lakefile.toml`): completed partial zetas, the per-class Mellin machinery, and the theta inversion
law. It builds as part of this package, so the repository is self-contained — no external path/git
dependency.

## Statistics

- **Lean source**: ≈ 18,500 lines — ≈ 5,800 in `SumProduct/` and ≈ 12,700 in the
  `DedekindZeta` support library (`DedekindZeta/`);
  ≈ 230 declarations.
- **Toolchain**: Lean 4 / Mathlib `v4.30.0`; the proof is conditional on one explicit classical
  hypothesis (Martinet's Theorem 3.2).
- **Production**: built by AI agents in five recorded phases between 2026-05-30 and 2026-06-03; see
  [`formalization.yaml`](formalization.yaml) for the per-phase tooling, models, wall-time, and cost.
  Most phases used subscription-metered access or separately recorded API usage; the externally
  metered asynchronous `DedekindZeta` production run cost ≈ $603.

## Building

```sh
lake exe cache get   # fetch the Mathlib build cache
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain` and Mathlib `v4.30.0` (see `lakefile.toml`).
The in-repository `DedekindZeta` library builds as part of this package; no external dependency is
needed.

## Comparator verification

The repository includes comparator-facing wrapper files for the headline theorem:

* trusted challenge file/module: `Challenge.lean` / `Challenge` (imports only Mathlib) — also viewable in the [live Lean playground](https://live.lean-lang.org/#codez=PQWgUAwg9gDgngJwJYHMAWAXABACgMYCUWATAAzEBsWAYlAgLYCGANjQlAHYZICmCWAFR6N6AOiwBBZq2ToMAZywIe8vgDceAE1FgASj2bDVmrAFcOmvpJiM8aHiVGkszJHh4dVWRosvy8yABGWlhIHFgY9lgAZkiGWAAyAJIQAKIAcgDKqToSppF08gBcNHRMrNTsXLz8QiIANJJJkvLySPIYjFxgIMBgSPQwdNgAsoyRroFgYKAAhGAAxFjQg4wI43RYdiyGHCgO0ZuRDvaMmq4cDsd0PPTTAmjtoYrHEQimHSHb0h77WG2WGKbAAGhi6MHYGgQwDwUFW6wwdGB4iwSWwAyGCAUWE4zDgWDGEyQgUaHXGKgi9jAbT28TwzB8bTwLCwaDgQ2ObUUPAAHjBXHgkBg8Y0uiYUEgNC8oso1LwAO4ha7Kej%2FToYW4ebDyoVobxYfm2HhoKDMSwIMAQqBQaI6XrTWAef6wmAhdKmejBBDUXhmsCO8IABSgYQwOtU01AICwACoYw8eDdVQBmUTEOO4MZYsI8DAEUWKLpYXn8txC1nsqCc9o6MAJ5TPbzhRiBeSm%2FIOWGeTpcLDAiBYAB8WFIwP%2BpjslPGQP4YViHCFBnxTA4%2BMsKGUFOBmjHxwbT0YYERnWk%2BOULI4Hq9MV9JmBAGkxzasOvN32dzioX3AFiEY%2FlJq8TR2gCAYwi6bB5HGdpYi3QAU4AAfXvLBABMiZYAD0d1rAAiJIOHnRc8SwFd8W3YEsMbEtlFaEIfBKQ5%2BB4KESPSXd7H3QsXx4DceAcbcsEAUyIsBYqdtToABreRxHtSxogJNZuEuDABCrHY4H0FhlMVBBFBKQN2BgLAigAXjALAzKwQBgImWQysEAXEJGmcAAeazAHIiLBAAAiISbMAVEJGiskwSl8rzUJMFzTPMsyrJwJCSgEdkeCIHB4Jsn0DBMe9EuSkp3U9PhUrNLAMtwLKhKvPLb1EJJ5GUk88XU1gMvqcKIrMkYoE0UxDFEed1g4MSsG%2FQqsCMl8sDcgAfHAcq9fLtCA%2Fx%2BBiuyCHGlDrLQl9IxAaMBHeT4TFheENn4b5dj%2BMkNXoLUZ0pE5hHOHNbqTKS%2BmVW5x3oPT2onDB4OiFgvBwNAswU3MbJBnMlJU096s0vh5CIIpmssrYbPskcsGcvAxo8rzAr8yQUrCVRsHR9I1okURmQQULkbMnAcCYHlcAkLAAGpJAIKm1hMHBWZjTnuZpnzEeWta%2BaFgKxY2nBiCwaNCEMkbAjgcK2wQBA4CAA) (challenge file in the Lean web editor)
* solution wrapper file/module: `Solution.lean` / `Solution`
* config: `comparator/sum_product_false.json`

Both `Challenge.lean` and `Solution.lean` state the Martinet-towers hypothesis explicitly.  The
solution theorem delegates to the project theorem `SumProduct.sumProduct_false`.

Use a `leanprover/comparator` checkout whose toolchain matches this project (currently the
`v4.30.0` tag), plus `landrun` on `PATH`:

```sh
COMPARATOR_DIR=$(mktemp -d /tmp/comparator.XXXXXX)
git clone https://github.com/leanprover/comparator "$COMPARATOR_DIR"
git -C "$COMPARATOR_DIR" checkout v4.30.0
scripts/verify-sum-product-with-comparator.sh "$COMPARATOR_DIR"
```

For the additional `systemd-run` hardening recommended by comparator, run the script from inside the
`systemd-run` wrapper described in comparator's README.
