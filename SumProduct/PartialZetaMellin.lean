/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DedekindZeta.PerClass
import DedekindZeta.ConeMellinBridge

/-!
# The partial-zeta residue inequality

This module proves the analytic input that Lemma 3.1 actually consumes: the per-ideal inequality

```lean
partialCompletedZetaResidue K ≤
  s * (s - 1) * (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
```

for real `s > 1` (`partialCompletedZetaResidue_le`). It is derived using the in-repository
`DedekindZeta` library (completed partial zetas, the archimedean factor `Z_∞`, the per-class Mellin
evaluation, the agreement `Z_K = Z_∞ · ζ_K` on `Re s > 1`, and the theta inversion law) together
with Mathlib's analytic class number formula.

The `DedekindZeta` library supplies the per-class Hecke theta–Mellin machinery, following Neukirch,
*Algebraic Number Theory*, Chapter VII §§1 and 3–5. Identifiers use
`dedekind`/`partialCompletedZeta`-flavored names.

## Why the direct inequality still needs the reflection step

`DedekindZeta`'s exposed pole+tail decomposition
(`completedPartialZeta_eq_conePolarCorrection_add_tail`) carries an `s`-dependent prefactor
`pf = (1/w)·𝔑(𝔞)^s·|d|^{s/2} = a·X^s` (`X = covolume = 𝔑(𝔞)√|d|`). Taken literally, its polar
part alone is not always at least the clean pole. The theta inversion law `radialTheta_inversion`
reflects the bounded dual tail and cancels the polar deficit, rewriting the decomposition as
`ρ/(s*(s-1))` plus two nonnegative `u`-tails. We stop there, instead of constructing the older
faithful existential with explicit `Φ, Ψ` densities and a `t = u²` change of variables. The pole
coefficient `ρ` is pinned to `surfaceVolume K / w` by `surfaceVolume_re_eq_residue_mul_torsion`,
which in turn equals `2^r R / w` via Mathlib's `dedekindZeta_residue` and dedekind's
`completedDedekindZeta_eq` (the class-number-formula route — no geometric volume computation).
-/

open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units

namespace SumProduct

variable (K : Type*) [Field K] [NumberField K]

/-- The residue of one completed **partial** zeta function:
`2^r R / w`, where `r = r₁ + r₂` is the number of infinite places. Summing this over the `h` ideal
classes gives the residue of the completed Dedekind zeta. -/
noncomputable def partialCompletedZetaResidue (K : Type*) [Field K] [NumberField K] : ℝ :=
  (2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K / torsionOrder K

/-! ## Archimedean normalization -/

/-- **Realness of the archimedean factor.** For real `s`, `DedekindZeta.ZInfty K (s : ℂ)` is the
`ofReal` of sum_product's real prefactor
`|d|^{s/2} · (π^{-s/2}Γ(s/2))^{r₁} · (2(2π)^{-s}Γ(s))^{r₂}`.

PROOF PLAN (moderate): unfold `DedekindZeta.ZInfty`, `DedekindZeta.LReal`, `DedekindZeta.LComplex`.
Push `Complex.ofReal` through `Complex.ofReal_cpow` (bases `|d| ≥ 0`, `π ≥ 0`, `2π ≥ 0`), the real
exponents `-(s/2)`, `-s`, `s/2`, and `Complex.Gamma_ofReal` (`Complex.Gamma (s:ℂ) = (Real.Gamma s : ℂ)`,
valid since the arguments `s/2, s > 0`). The `(|discr K| : ℤ : ℂ) ^ (s/2)` matches sum_product's
`|(discr K : ℝ)| ^ (s/2)` via `Int.cast_abs`/`Complex.ofReal_intCast`. Note `-s/2 = -(s/2)`. -/
lemma zInfty_ofReal (s : ℝ) :
    DedekindZeta.ZInfty K (s : ℂ)
      = ((|(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ NumberField.InfinitePlace.nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
              ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hdisc : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| := abs_nonneg _
  -- LReal
  have hLReal : DedekindZeta.LReal (s : ℂ)
      = ((Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
    rw [DedekindZeta.LReal]
    rw [show (-(s : ℂ) / 2) = ((-(s / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpi]
    rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  -- LComplex
  have hLComplex : DedekindZeta.LComplex (s : ℂ)
      = ((2 * (2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) := by
    rw [DedekindZeta.LComplex]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h2pi, Complex.Gamma_ofReal]
    push_cast; ring
  -- discriminant factor
  have hDR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [Int.cast_abs]
  have hDisc : (((|NumberField.discr K| : ℤ) : ℂ)) ^ ((s : ℂ) / 2)
      = ((|(NumberField.discr K : ℝ)| ^ (s / 2) : ℝ) : ℂ) := by
    rw [show (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
        rw [← hDR]; norm_cast,
      show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hdisc]
  rw [DedekindZeta.ZInfty, hLReal, hLComplex, hDisc]
  push_cast
  ring

/-! ## Residue value via Mathlib's analytic class number formula

The per-class residue at `s = 1` is class-independent and equals `partialCompletedZetaResidue K`
(= `2^{r₁+r₂} R / w`). It comes from Mathlib's `dedekindZeta_residue` through
`completedDedekindZeta_eq` + `Z_∞(1) = √|d|/π^{r₂}` (since `LReal 1 = π^{-1/2}Γ(1/2) = 1`,
`LComplex 1 = 2(2π)^{-1}Γ(1) = 1/π`), NOT from the geometric `surfaceVolume`/`covolume`. -/

/-- **`Z_∞` at `s = 1`.** `DedekindZeta.ZInfty K 1 = (√|d| / π^{r₂} : ℂ)`.

PROOF PLAN (moderate): unfold `ZInfty`/`LReal`/`LComplex` at `s = 1`.
`(|d| : ℂ)^(1/2) = √|d|` (`Complex.ofReal_cpow` + `Real.rpow_half`/`Real.sqrt_eq_rpow`).
`LReal 1 = π^{-1/2} Γ(1/2) = 1`: use `Complex.Gamma_one_half_eq` (`Γ(1/2) = √π`) and
`π^{-1/2} = (√π)⁻¹`. `LComplex 1 = 2·(2π)^{-1}·Γ 1 = 2/(2π) = 1/π`: `Complex.Gamma_one = 1`.
So `ZInfty 1 = √|d| · 1^{r₁} · (1/π)^{r₂} = √|d| / π^{r₂}`. -/
lemma zInfty_one :
    DedekindZeta.ZInfty K (1 : ℂ)
      = ((Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Use the realness lemma at `s = 1`.
  have h1 : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  rw [← h1, zInfty_ofReal K 1]
  congr 1
  -- Simplify the real prefactor at `s = 1`.
  -- `|d|^(1/2) = √|d|`.
  have hsqrt : |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2)
      = Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.sqrt_eq_rpow]
  -- `LReal` factor `= 1`.
  have hLR : (Real.pi ^ (-((1 : ℝ) / 2)) * Real.Gamma ((1 : ℝ) / 2)) = 1 := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow, ← Real.rpow_add hpi]
    norm_num
  -- `LComplex` factor `= 1/π`.
  have hLC : (2 * (2 * Real.pi) ^ (-(1 : ℝ)) * Real.Gamma 1) = 1 / Real.pi := by
    rw [Real.Gamma_one, Real.rpow_neg_one]
    field_simp
  rw [hsqrt, hLR, hLC, one_pow, mul_one, div_pow, one_pow, mul_one_div]

/-! ## Tail nonnegativity and the final inequality (target B)

The genuine, proved structural content below: dedekind's per-ideal completed zeta admits the
explicit real decomposition

    `(DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re = pf(s) · (conePolarRe(s) + tailRe(s))`,

where `pf(s) = (1/w)·𝔑(𝔞)^s·|d|^{s/2} > 0` is dedekind's prefactor (real for real `s`),
`conePolarRe(s) = −V/s + (V/X)/(s−1)` is the real part of `conePolarCorrection`
(`V = (surfaceVolume K).re ≥ 0`, `X = covolume K 𝔞 = 𝔑(𝔞)√|d| > 1`), and
`tailRe(s) = (mellinTail …).re ≥ 0` is the genuine theta tail. These are established from
the exposed dedekind machinery (`completedPartialZeta_eq_conePolarCorrection_add_tail`,
`mixedGaussian_nonneg`); see `orbitTheta_re_nonneg` and
`completedPartialZeta_real_decomp`. -/

open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors

variable {K} in
/-- A complex number with vanishing imaginary part equals the `ofReal` of its real part. -/
private theorem ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (Complex.ofReal_re _).symm (h.trans (Complex.ofReal_im _).symm)

variable {K} in
/-- **`orbitTheta` is real and nonnegative.** The orbit-integrated theta `orbitTheta K 𝔞 r` is the
surface integral of `Theta.idealThetaKernel`, which is `Complex.ofReal` of a `tsum` of the
nonnegative Minkowski Gaussian (`DedekindZeta.mixedGaussian_nonneg`); hence it is real with
nonnegative real part. -/
theorem orbitTheta_re_nonneg (𝔞 : Ideal (𝓞 K)) (r : ℝ) :
    (orbitTheta K 𝔞 r).im = 0 ∧ 0 ≤ (orbitTheta K 𝔞 r).re := by
  have h : orbitTheta K 𝔞 r
      = ((∫ σ in normEqOneSurface K,
          (∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)))
          ∂(surfaceMeasure K)) : ℝ) := by
    rw [orbitTheta, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
    rw [Theta.idealThetaKernel, Complex.ofReal_tsum]
  rw [h]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg (fun σ => tsum_nonneg (fun a => mixedGaussian_nonneg _))

variable {K} in
/-- **`orbitThetaFrac` is real and nonnegative** (dual-ideal analogue of `orbitTheta_re_nonneg`). -/
theorem orbitThetaFrac_re_nonneg (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) :
    (orbitThetaFrac K I r).im = 0 ∧ 0 ≤ (orbitThetaFrac K I r).re := by
  have h : orbitThetaFrac K I r
      = ((∫ σ in normEqOneSurface K,
          (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
            Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K (a : K)))
          ∂(surfaceMeasure K)) : ℝ) := by
    rw [orbitThetaFrac, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
    rw [Theta.mixedThetaKernel, Complex.ofReal_tsum]
  rw [h]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg (fun σ => tsum_nonneg (fun a => mixedGaussian_nonneg _))

variable {K} in
/-- **The dedekind prefactor is `ofReal` of a positive real for real `s`.**
`(1/w)·(𝔑 𝔞)^s·|d|^{s/2} = ((1/w)·𝔑(𝔞)^s·|d|^{s/2} : ℝ)`, with the real value positive for `𝔞 ≠ 0`. -/
theorem partialZetaPrefactor_ofReal (𝔞 : Ideal (𝓞 K)) (s : ℝ) :
    (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ (s : ℂ)
        * (((|NumberField.discr K| : ℤ) : ℂ) ^ ((s : ℂ) / 2))
      = (((1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
          * (|(NumberField.discr K : ℝ)|) ^ (s / 2) : ℝ) : ℂ) := by
  have hN : (Ideal.absNorm 𝔞 : ℂ) = (((Ideal.absNorm 𝔞 : ℝ)) : ℂ) := by push_cast; ring
  have hDR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [Int.cast_abs]
  have hD : (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) := by
    rw [← hDR]; norm_cast
  rw [hN, hD, show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

variable {K} in
/-- **The cone polar correction is real for real `s`,** with explicit real value
`−V/s + (1/X)·V/(s−1)` (`V = (surfaceVolume K).re`, `X = covolume K 𝔞`). -/
theorem conePolarCorrection_ofReal (𝔞 : Ideal (𝓞 K)) (s : ℝ) :
    conePolarCorrection K 𝔞 (s : ℂ)
      = ((- (surfaceVolume K).re / s
          + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1) : ℝ) : ℂ) := by
  have hVre : (surfaceVolume K) = ((surfaceVolume K).re : ℂ) := by
    rw [surfaceVolume]; simp
  have hcov : (Theta.covolume K 𝔞 : ℂ)⁻¹ = ((1 / Theta.covolume K 𝔞 : ℝ) : ℂ) := by
    push_cast; ring
  rw [conePolarCorrection, hcov]
  conv_lhs => rw [hVre]
  push_cast
  ring

variable {K} in
/-- **The clean real decomposition of dedekind's per-ideal completed zeta.** For real `s > 1`,

    `(completedPartialZeta K 𝔞 (s:ℂ)).re = pf · (conePolarRe + tailRe)`,

with `pf = (1/w)·𝔑(𝔞)^s·|d|^{s/2}`, `conePolarRe = −V/s + (V/X)/(s−1)`,
and `tailRe = (mellinTail …).re`. Assembled from dedekind's
`completedPartialZeta_eq_conePolarCorrection_add_tail` and the realness lemmas above. -/
theorem completedPartialZeta_real_decomp (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
      = ((1 / (Units.torsionOrder K : ℝ))
            * (Ideal.absNorm 𝔞 : ℝ) ^ s
            * (|(NumberField.discr K : ℝ)|) ^ (s / 2))
        * ((- (surfaceVolume K).re / s
            + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1))
          + (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K)
              ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)).re) := by
  have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  rw [completedPartialZeta_eq_conePolarCorrection_add_tail 𝔞 hne hsre,
    partialZetaPrefactor_ofReal 𝔞 s, conePolarCorrection_ofReal 𝔞 s]
  -- the bracket `(ofReal cone + tail)`: pull out the tail's real part
  set T := mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
      (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ) with hT
  set cp : ℝ := - (surfaceVolume K).re / s
      + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1) with hcp
  set pf : ℝ := (1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
      * (|(NumberField.discr K : ℝ)|) ^ (s / 2) with hpf
  -- `(ofReal pf * (ofReal cp + T)).re = pf * (cp + T.re)`
  rw [show ((pf : ℝ) : ℂ) * (((cp : ℝ) : ℂ) + T)
      = ((pf : ℂ) * (cp : ℂ)) + (pf : ℂ) * T by ring]
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  ring

/-! ## The per-ideal residue `V/w` and the residue identity `V/w = ρ`

The completed partial zeta of *any* nonzero ideal `𝔞` has, at `s = 1`, the class-independent
residue `(surfaceVolume K).re / torsionOrder K`. Assembled from dedekind's prefactor continuity,
`conePolarCorrection_residue_one`, and `mellinTail` continuity (regularity). Summing this over the
class group and matching it against Mathlib's analytic class number formula
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) through `completedDedekindZeta_eq` +
`zInfty_one` yields the surface-volume ↔ regulator identity `V/w = ρ`. -/

/-- **Per-ideal completed-zeta residue at `s = 1` is `V/w`.** For any nonzero ideal `𝔞`,
`(s−1)·completedPartialZeta K 𝔞 (s:ℂ) → (surfaceVolume K)/(torsionOrder K)` as real `s → 1⁺`.
The prefactor `pf(s)=(1/w)·𝔑(𝔞)^s·|d|^{s/2}` is continuous with `pf(1)·(covolume K 𝔞)⁻¹ = 1/w`,
the cone correction contributes residue `(covolume)⁻¹·V` (`conePolarCorrection_residue_one`), and
the analytic `mellinTail` contributes `0`. -/
theorem completedPartialZeta_residue_perIdeal (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (surfaceVolume K / (Units.torsionOrder K : ℂ))) := by
  classical
  -- The Mellin pair, for `mellinTail` continuity at `s = 1`.
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  set pf : ℂ → ℂ := fun s => (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ s
      * (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) with hpfdef
  set T : ℂ → ℂ := fun s => mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
      (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 s with hTdef
  -- `ofReal : 𝓝[>]1 (real) → 𝓝[≠]1 (complex)`, continuous and avoiding 1.
  have hmap : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhds 1) (nhds ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      have h1 : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
          (nhds ((1 : ℝ) : ℂ)) :=
        h0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
      simpa using h1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hs1 : (s : ℝ) = 1 := by exact_mod_cast h
      have : (1 : ℝ) < 1 := by rw [hs1] at hs; exact hs
      exact absurd this (lt_irrefl 1)
  -- `(s-1)·completedPartialZeta = pf(s)·((s-1)·conePolar + (s-1)·T)`, eventually on `𝓝[>]1`.
  have hrw : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ => pf (s : ℂ)
        * (((s : ℂ) - 1) * conePolarCorrection K 𝔞 (s : ℂ) + ((s : ℂ) - 1) * T (s : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
    rw [completedPartialZeta_eq_conePolarCorrection_add_tail 𝔞 hne hsre]
    ring
  rw [Filter.tendsto_congr' hrw]
  -- Limit of the bracket (along complex `𝓝[≠]1`, then composed with `ofReal`).
  have hcone := conePolarCorrection_residue_one K 𝔞
  have hTail : Filter.Tendsto (fun s : ℂ => (s - 1) * T s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have hTcont : ContinuousAt T 1 := (mellinTail_analyticOn hpair 1 (Set.mem_univ 1)).continuousAt
    have h1 : Filter.Tendsto (fun s : ℂ => (s - 1) * T s) (nhds 1) (nhds ((1 - 1) * T 1)) :=
      ((continuous_id.sub continuous_const).continuousAt.mul hTcont).tendsto
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hbracketC : Filter.Tendsto
      (fun s : ℂ => (s - 1) * conePolarCorrection K 𝔞 s + (s - 1) * T s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)) := hcone.add hTail
  have hbracket : Filter.Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * conePolarCorrection K 𝔞 (s : ℂ) + ((s : ℂ) - 1) * T (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)) := hbracketC.comp hmap
  -- Limit of `pf` at `1`.
  have hNne : (Ideal.absNorm 𝔞 : ℂ) ≠ 0 := by
    have : Ideal.absNorm 𝔞 ≠ 0 :=
      fun h => hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  have hDne : (((|NumberField.discr K| : ℤ) : ℂ)) ≠ 0 := by
    have : (|NumberField.discr K| : ℤ) ≠ 0 := by
      simpa using NumberField.discr_ne_zero K
    exact_mod_cast this
  have hpfcont : ContinuousAt pf 1 := by
    rw [hpfdef]
    refine (continuousAt_const.mul ?_).mul ?_
    · exact continuousAt_id.const_cpow (Or.inl hNne)
    · exact (continuousAt_id.div_const 2).const_cpow (Or.inl hDne)
  have hpfC : Filter.Tendsto pf (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (pf 1)) :=
    hpfcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpf1 : Filter.Tendsto (fun s : ℝ => pf (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (pf 1)) :=
    hpfC.comp hmap
  have hprod := hpf1.mul hbracket
  -- Identify the value `pf(1)·(covolume⁻¹·V) = V/w`.
  have hval : pf 1 * ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K + 0)
      = surfaceVolume K / (Units.torsionOrder K : ℂ) := by
    rw [add_zero, hpfdef]
    show (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ (1 : ℂ)
        * (((|NumberField.discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2))
        * ((Theta.covolume K 𝔞 : ℂ)⁻¹ * surfaceVolume K)
      = surfaceVolume K / (Units.torsionOrder K : ℂ)
    -- pf(1) = (1/w)·𝔑𝔞·|d|^{1/2}; covolume = 𝔑𝔞·√|d|.
    have hN : (Ideal.absNorm 𝔞 : ℂ) ^ (1 : ℂ) = (Ideal.absNorm 𝔞 : ℂ) := by
      rw [Complex.cpow_one]
    have hD : (((|NumberField.discr K| : ℤ) : ℂ)) ^ ((1 : ℂ) / 2)
        = ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) := by
      have hdR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
        rw [Int.cast_abs]
      rw [show (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
            rw [← hdR]; norm_cast,
        show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (abs_nonneg _), Real.sqrt_eq_rpow]
    rw [hN, hD, Theta.covolume]
    have hNne : (Ideal.absNorm 𝔞 : ℝ) ≠ 0 := by
      have : Ideal.absNorm 𝔞 ≠ 0 :=
        fun h => hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast this
    have hsne : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 :=
      (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))).ne'
    have hwne : (Units.torsionOrder K : ℂ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    rw [show ((((Ideal.absNorm 𝔞 : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| : ℝ)) : ℂ)
        = ((Ideal.absNorm 𝔞 : ℝ) : ℂ) * ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
      push_cast; ring]
    rw [mul_inv]
    have hNC : ((Ideal.absNorm 𝔞 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNne
    have hsC : ((Real.sqrt |(NumberField.discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsne
    field_simp
    push_cast
    ring
  rw [hval] at hprod
  exact hprod

/-- **Geometric total residue.** Summing the per-ideal residue over the class group:
`(s−1)·completedDedekindZeta K (s:ℂ) → (classNumber K)·V/w` as real `s → 1⁺`. -/
theorem completedDedekindZeta_residue_geometric :
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((Fintype.card (ClassGroup (𝓞 K)) : ℂ) * (surfaceVolume K / (Units.torsionOrder K : ℂ))))
      := by
  classical
  -- `(s-1)·completedDedekindZeta = ∑_c (s-1)·completedPartialZeta (rep c)`.
  have hrw : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      = (fun s : ℝ => ∑ c : ClassGroup (𝓞 K),
          ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K c) (s : ℂ))
      := by
    funext s
    rw [DedekindZeta.completedDedekindZeta, Finset.mul_sum]
  rw [hrw]
  -- Each summand tends to `V/w` (per-ideal residue applied to the representative `≠ 0`).
  have hsummand : ∀ c : ClassGroup (𝓞 K),
      Filter.Tendsto (fun s : ℝ =>
        ((s : ℂ) - 1) * DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K c) (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (surfaceVolume K / (Units.torsionOrder K : ℂ))) := by
    intro c
    refine completedPartialZeta_residue_perIdeal K (DedekindZeta.idealClassRep K c) ?_
    exact mem_nonZeroDivisors_iff_ne_zero.mp (Function.surjInv ClassGroup.mk0_surjective c).2
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ClassGroup (𝓞 K)))
    (fun c _ => hsummand c)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact hsum

/-- **The surface-volume ↔ regulator identity** (class-number-formula linchpin), in `.re` form:
`(surfaceVolume K).re = partialCompletedZetaResidue K · torsionOrder K`, equivalently `V = ρ·w`.

Proved by computing the residue of `completedDedekindZeta` at `s = 1` two ways and equating: the
geometric sum `classNumber · V/w` (`completedDedekindZeta_residue_geometric`) versus Mathlib's
analytic class number formula `Z_∞(1)·κ = (√|d|/π^{r₂})·dedekindZeta_residue`
(`completedDedekindZeta_eq` + `zInfty_one` + `tendsto_sub_one_mul_dedekindZeta_nhdsGT`), then the
elementary residue identity `(√|d|/π^{r₂})·κ = classNumber·ρ`; cancel `classNumber > 0`. -/
theorem surfaceVolume_re_eq_residue_mul_torsion :
    (surfaceVolume K).re = partialCompletedZetaResidue K * (Units.torsionOrder K : ℝ) := by
  classical
  set h : ℕ := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hhcn : (h : ℝ) = (NumberField.classNumber K : ℝ) := by rw [hh, NumberField.classNumber]
  -- Mathlib analytic residue: `(s-1)·completedDedekindZeta → ZInfty(1)·κ = (√|d|/π^{r₂})·κ`.
  have hZeq : (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ) * (((s : ℂ) - 1) * NumberField.dedekindZeta K s))
      := by
    have hmem : {s : ℝ | (1 : ℝ) < s} ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
    rw [DedekindZeta.completedDedekindZeta_eq K hsre]
    ring
  -- The Mathlib pieces: `ZInfty (s:ℂ) → ZInfty 1` (continuity) and `(s-1)·ζ_K → κ`.
  have hzinf : Filter.Tendsto (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (DedekindZeta.ZInfty K (1 : ℂ))) := by
    -- Use the explicit real form `zInfty_ofReal`: continuity of the real prefactor for `s > 0`.
    set F : ℝ → ℝ := fun s => |(NumberField.discr K : ℝ)| ^ (s / 2)
        * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ NumberField.InfinitePlace.nrRealPlaces K
        * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
            ^ NumberField.InfinitePlace.nrComplexPlaces K with hF
    have hrwF : (fun s : ℝ => DedekindZeta.ZInfty K (s : ℂ)) = (fun s : ℝ => ((F s : ℝ) : ℂ)) := by
      funext s; rw [zInfty_ofReal K s]
    have h1F : DedekindZeta.ZInfty K (1 : ℂ) = ((F 1 : ℝ) : ℂ) := by
      have : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num
      rw [← this, zInfty_ofReal K 1]
    rw [hrwF, h1F]
    -- `F` is continuous at `1` (all factors continuous for `s` near `1 > 0`).
    have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have hFcont : ContinuousAt F 1 := by
      rw [hF]
      have hc1 : ContinuousAt (fun s : ℝ => |(NumberField.discr K : ℝ)| ^ (s / 2)) 1 :=
        (Real.continuousAt_const_rpow hd.ne').comp (continuousAt_id.div_const 2)
      have hc2 : ContinuousAt
          (fun s : ℝ => (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2))
            ^ NumberField.InfinitePlace.nrRealPlaces K) 1 := by
        refine ContinuousAt.pow ?_ _
        refine ContinuousAt.mul ?_ ?_
        · exact (Real.continuousAt_const_rpow Real.pi_ne_zero).comp
            ((continuousAt_id.div_const 2).neg)
        · have hG : ContinuousAt Real.Gamma ((1 : ℝ) / 2) :=
            (Real.differentiableAt_Gamma (s := (1 : ℝ) / 2) (fun m => by
              have hm : (-(m : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
              norm_num; linarith)).continuousAt
          have hinner : ContinuousAt (fun s : ℝ => s / 2) 1 := continuousAt_id.div_const 2
          exact ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => s / 2)
            (by simpa using hG) hinner
      have hc3 : ContinuousAt
          (fun s : ℝ => (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
            ^ NumberField.InfinitePlace.nrComplexPlaces K) 1 := by
        refine ContinuousAt.pow ?_ _
        refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
        · exact (Real.continuousAt_const_rpow (by positivity)).comp continuousAt_id.neg
        · exact (Real.differentiableAt_Gamma (s := (1 : ℝ)) (fun m => by
            have hm : (-(m : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
            norm_num; linarith)).continuousAt
      exact (hc1.mul hc2).mul hc3
    have hco : ContinuousAt (fun s : ℝ => ((F s : ℝ) : ℂ)) 1 :=
      Complex.continuous_ofReal.continuousAt.comp hFcont
    exact hco.tendsto.mono_left nhdsWithin_le_nhds
  have hzeta := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hzeta' : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)) := by
    refine hzeta.congr (fun s => ?_)
    ring
  have hmathlib : Filter.Tendsto
      (fun s : ℝ => ((s : ℂ) - 1) * DedekindZeta.completedDedekindZeta K (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (DedekindZeta.ZInfty K (1 : ℂ) * ((NumberField.dedekindZeta_residue K : ℝ) : ℂ))) := by
    rw [Filter.tendsto_congr' hZeq]
    exact hzinf.mul hzeta'
  -- Geometric residue.
  have hgeom := completedDedekindZeta_residue_geometric K
  -- The two limits agree (uniqueness of limits along a nontrivial filter).
  have hbot : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot (le_refl 1)
  have heq := tendsto_nhds_unique hgeom hmathlib
  -- `ZInfty 1 = √|d|/π^{r₂}` and rearrange to a real identity.
  rw [zInfty_one K] at heq
  -- Take real parts: everything is `ofReal`.
  have hsurf : surfaceVolume K = ((surfaceVolume K).re : ℂ) := by rw [surfaceVolume]; simp
  have hwne : (Units.torsionOrder K : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
  -- Convert `heq` (complex) into a real equation between residues.
  have hcomplex : (h : ℝ) * ((surfaceVolume K).re / (Units.torsionOrder K : ℝ))
      = (Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
        * NumberField.dedekindZeta_residue K := by
    have h0 := heq
    rw [hsurf] at h0
    -- both sides are `ofReal`s; strip.
    have hlhs : (h : ℂ) * (((surfaceVolume K).re : ℂ) / (Units.torsionOrder K : ℂ))
        = (((h : ℝ) * ((surfaceVolume K).re / (Units.torsionOrder K : ℝ)) : ℝ) : ℂ) := by
      push_cast; ring
    have hrhs : ((Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ)
          * ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)
        = (((Real.sqrt |(NumberField.discr K : ℝ)|
            / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
            * NumberField.dedekindZeta_residue K : ℝ) : ℂ) := by
      push_cast; ring
    rw [hlhs, hrhs] at h0
    exact Complex.ofReal_injective h0
  -- Elementary residue identity: `(√|d|/π^{r₂})·κ = classNumber·ρ`.
  have hcnf : (Real.sqrt |(NumberField.discr K : ℝ)|
        / Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K)
        * NumberField.dedekindZeta_residue K
      = (NumberField.classNumber K : ℝ) * partialCompletedZetaResidue K := by
    have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
    have hpi : Real.pi ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
      pow_ne_zero _ Real.pi_ne_zero
    have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    rw [NumberField.dedekindZeta_residue_def]
    unfold partialCompletedZetaResidue
    field_simp
    rw [pow_add, mul_pow]
    ring
  -- Combine and cancel `classNumber > 0`.
  rw [hcnf, ← hhcn] at hcomplex
  have hhpos : (0 : ℝ) < (h : ℝ) := by
    rw [hh]; exact_mod_cast Fintype.card_pos
  have hcancel : (surfaceVolume K).re / (Units.torsionOrder K : ℝ) = partialCompletedZetaResidue K :=
    mul_left_cancel₀ (ne_of_gt hhpos) hcomplex
  have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
  field_simp [hw] at hcancel
  linarith [hcancel]

/-! ## Direct per-ideal inequality from the local Mellin decomposition

The consumer `RegulatorBound` only needs the inequality

    `partialCompletedZetaResidue K ≤ s * (s - 1) * (completedPartialZeta K 𝔞 (s:ℂ)).re`

for real `s > 1`. We therefore avoid constructing the old faithful existential
`partialCompletedZeta_mellin_formula` with explicit `Φ, Ψ` densities and the auxiliary `t = u²`
change of variables. The remaining bridge uses the local `DedekindZeta` decomposition directly:
`completedPartialZeta_real_decomp` gives the raw cone-polar term plus nonnegative theta tails, and
`reflectionCore_main` reflects the bounded dual slice via `radialTheta_inversion` to rewrite it as the
clean pole `ρ/(s*(s-1))` plus two nonnegative `u`-tails. -/

/-! ### The abstract real reflection core

The remaining analytic reflection step is a purely real identity between integrals of two functions
`OT`, `OTD : ℝ → ℝ` (the real parts of `orbitTheta` and `orbitThetaFrac (dualIdeal …)`), under the
inversion law `OTD (1/r) = X·r·(OT r + V) − V`. We isolate it here as a self-contained lemma over
abstract `OT`, `OTD`, which lets the proof avoid the heavy `DedekindZeta` definitions and reason with
plain real analysis.
-/

/-- **Change of variables `u = X·y` on the head tail.** For the integrand `OT(u/X)·u^{s−1}`,
restricting to `Ioi X` and rescaling by `u = X·y` gives `X^s·∫_{y>1} OT(y)·y^{s−1}`. -/
private theorem reflectionCore_head_cov (X s : ℝ) (hX : 0 < X) (OT : ℝ → ℝ) :
    (∫ u in Set.Ioi X, OT (u / X) * u ^ (s - 1))
      = X ^ s * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
  have hcov := integral_comp_mul_left_Ioi
    (fun x : ℝ => OT (x / X) * x ^ (s - 1)) 1 hX
  simp only [mul_one, smul_eq_mul] at hcov
  -- LHS of `hcov` : `∫_{x>1} OT(X·x/X)·(X·x)^{s-1} = X^{s-1}·∫_{x>1} OT(x)·x^{s-1}`.
  have hlhs : (∫ x in Set.Ioi (1 : ℝ), OT (X * x / X) * (X * x) ^ (s - 1))
      = X ^ (s - 1) * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [mul_div_cancel_left₀ y hX.ne', Real.mul_rpow hX.le hy0.le]
    ring
  rw [hlhs] at hcov
  -- `hcov : X^{s-1}·I1 = X⁻¹·H` with `H = ∫_{u>X} OT(u/X)·u^{s-1}`.  So `H = X·X^{s-1}·I1 = X^s·I1`.
  have hXs : X ^ s = X * X ^ (s - 1) := by
    rw [show s = 1 + (s - 1) by ring, Real.rpow_add hX, Real.rpow_one]
    ring_nf
  rw [hXs, mul_assoc, hcov, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]

/-- **Change of variables `u = y/X` on the dual tail.** For the integrand `OTD(X·u)·u^{−s}`,
rescaling by `u = y/X` gives `X^{s−1}·∫_{y>X} OTD(y)·y^{−s}`. -/
private theorem reflectionCore_dual_cov (X s : ℝ) (hX : 0 < X) (OTD : ℝ → ℝ) :
    (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
  have hcov := integral_comp_mul_left_Ioi
    (fun x : ℝ => OTD x * (x / X) ^ (-s)) 1 hX
  simp only [mul_one, smul_eq_mul] at hcov
  -- LHS of `hcov`: `∫_{x>1} OTD(X·x)·(X·x/X)^{-s} = ∫_{x>1} OTD(X·x)·x^{-s}`.
  have hlhs : (∫ x in Set.Ioi (1 : ℝ), OTD (X * x) * (X * x / X) ^ (-s))
      = ∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [mul_div_cancel_left₀ y hX.ne']
  -- RHS of `hcov`: `X⁻¹·∫_{y>X} OTD(y)·(y/X)^{-s} = X⁻¹·X^s·∫_{y>X} OTD(y)·y^{-s}`.
  have hrhs : (X⁻¹ * ∫ y in Set.Ioi X, OTD y * (y / X) ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans hX hy
    have hdr : (y / X) ^ (-s) = y ^ (-s) * X ^ s := by
      rw [Real.div_rpow hy0.le hX.le, Real.rpow_neg hX.le s, div_inv_eq_mul]
    rw [hdr, show s - 1 = s + (-1) by ring, Real.rpow_add hX, Real.rpow_neg_one]
    ring
  rw [hlhs, hrhs] at hcov
  exact hcov

/-- **The reflection change of variables `y = 1/r`** on the bounded slice `Ioo 1 X` (`1 < X`). For
any continuous `H : ℝ → ℝ`, `∫_{y∈(1,X)} H y = ∫_{r∈(1/X,1)} (1/r²)·H (1/r)`. -/
private theorem reflectionCore_inv_cov (X : ℝ) (hX : 1 < X) (H : ℝ → ℝ) :
    (∫ y in Set.Ioo (1 : ℝ) X, H y)
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * H (1 / r) := by
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX
  -- The reflection `f r = 1/r` is an injective `C¹` bijection `Ioo (1/X) 1 → Ioo 1 X`,
  -- with derivative `f' r = -1/r²`.
  have hderiv : ∀ r ∈ Set.Ioo (1 / X) (1 : ℝ),
      HasDerivWithinAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) (Set.Ioo (1 / X) (1 : ℝ)) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr.1
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr0.ne'
    have h2 : HasDerivAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) r := by
      simp only [one_div]
      exact h1.congr_deriv (by rw [neg_div, one_div])
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => 1 / r) (Set.Ioo (1 / X) (1 : ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0 : ℝ) < a := lt_trans (by positivity) ha.1
    have hb0 : (0 : ℝ) < b := lt_trans (by positivity) hb.1
    field_simp at hab
    linarith
  have himg : (fun r : ℝ => 1 / r) '' (Set.Ioo (1 / X) (1 : ℝ)) = Set.Ioo (1 : ℝ) X := by
    ext z
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
      have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr1
      constructor
      · rw [lt_div_iff₀ hr0, one_mul]; exact hr2
      · rw [div_lt_iff₀ hr0]
        rw [div_lt_iff₀ hX0] at hr1; linarith [hr1]
    · rintro ⟨hz1, hz2⟩
      have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
      refine ⟨1 / z, ⟨?_, ?_⟩, by rw [one_div_one_div]⟩
      · rw [div_lt_div_iff₀ hX0 hz0, one_mul, one_mul]; exact hz2
      · rw [div_lt_one hz0]; exact hz1
  have key := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj H
  rw [himg] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := lt_trans (by positivity) hr.1
  have habs : |(-1 : ℝ) / r ^ 2| = 1 / r ^ 2 := by
    rw [abs_div, abs_neg, abs_one, abs_of_nonneg (by positivity : (0:ℝ) ≤ r^2)]
  rw [habs, smul_eq_mul]

/-- Integrability of the rescaled head integrand `OT(u/X)·u^{s−1}` on `Ioi X`, from the tail
integrability `hI1` of `OT(y)·y^{s−1}` on `Ioi 1`. -/
private theorem reflectionCore_head_integrable (X s : ℝ) (hX : 0 < X) (OT : ℝ → ℝ)
    (hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ))) :
    IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioi X) := by
  rw [show X = X * 1 by ring, ← integrableOn_Ioi_comp_mul_left_iff _ 1 hX]
  have hc : IntegrableOn (fun y => X ^ (s - 1) * (OT y * y ^ (s - 1))) (Set.Ioi (1 : ℝ)) :=
    Integrable.const_mul hI1 (X ^ (s - 1))
  refine hc.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  show X ^ (s - 1) * (OT y * y ^ (s - 1)) = OT (X * y / (X * 1)) * (X * y) ^ (s - 1)
  rw [mul_one, mul_div_cancel_left₀ y hX.ne', Real.mul_rpow hX.le hy0.le]
  ring

/-- Integrability of the rescaled dual integrand `OTD(X·u)·u^{−s}` on `Ioi 1`, from the tail
integrability `hI2` of `OTD(y)·y^{−s}` on `Ioi 1` (note `X ≥ 1`, so `Ioi X ⊆ Ioi 1`). -/
private theorem reflectionCore_dual_integrable (X s : ℝ) (hX : 0 < X) (OTD : ℝ → ℝ)
    (hI2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi (1 : ℝ))) (hX1 : 1 ≤ X) :
    IntegrableOn (fun u => OTD (X * u) * u ^ (-s)) (Set.Ioi (1 : ℝ)) := by
  -- `f y := OTD y · (y/X)^{-s} = X^s · (OTD y · y^{-s})`; integrable on `Ioi X ⊆ Ioi 1`.
  have hf : IntegrableOn (fun y => OTD y * (y / X) ^ (-s)) (Set.Ioi X) := by
    have hsub : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi X) :=
      hI2.mono_set (Set.Ioi_subset_Ioi hX1)
    have hcm : IntegrableOn (fun y => X ^ s * (OTD y * y ^ (-s))) (Set.Ioi X) :=
      Integrable.const_mul hsub (X ^ s)
    refine hcm.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans hX hy
    show X ^ s * (OTD y * y ^ (-s)) = OTD y * (y / X) ^ (-s)
    rw [Real.div_rpow hy0.le hX.le, Real.rpow_neg hX.le s, div_inv_eq_mul]
    ring
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun y => OTD y * (y / X) ^ (-s)) 1 hX).mpr (by rwa [mul_one])
  refine hcomp.congr_fun (fun u _ => ?_) measurableSet_Ioi
  show OTD (X * u) * (X * u / X) ^ (-s) = OTD (X * u) * u ^ (-s)
  rw [mul_div_cancel_left₀ u hX.ne']
/-- **The reflection identity on the bounded slice `Ioo 1 X`** (`1 < X`), the analytic heart.
Reflecting `∫_{(1,X)} OTD(y)·y^{−s}` via `y = 1/r` and applying the inversion law
`OTD(1/r) = X·r·(OT r + V) − V` produces three integrals: the `OT`-piece (which will cancel against
the `OT`-piece of `∫_{(1,X)} OT(u/X)·u^{s−1}`), and the two pure-power integrals over `(1/X,1)`. -/
private theorem reflectionCore_slice (X V s : ℝ) (hX1 : 1 < X) (hs : 1 < s) (OT OTD : ℝ → ℝ)
    (hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V)
    (hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ))) :
    X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        - (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * V * ((1 - (1 / X) ^ s) / s)
        - X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1)) := by
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  have hXinv1 : 1 / X < 1 := by rw [div_lt_one hX0]; exact hX1
  -- Integrabilities on the bounded slices (continuity on compacts away from 0).
  have hcont_pow1 : ContinuousOn (fun r : ℝ => r ^ (s - 1)) (Set.Icc (1 / X) 1) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro r hr; left
    have : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1
    exact this.ne'
  have hcont_pow2 : ContinuousOn (fun r : ℝ => r ^ (s - 2)) (Set.Icc (1 / X) 1) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro r hr; left
    have : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1
    exact this.ne'
  have hOT_icc : ContinuousOn (fun r : ℝ => OT r * r ^ (s - 1)) (Set.Icc (1 / X) 1) := by
    refine (hOTcont.mono ?_).mul hcont_pow1
    intro r hr; exact lt_of_lt_of_le hXinv hr.1
  have hint_pow1 : IntegrableOn (fun r : ℝ => r ^ (s - 1)) (Set.Ioo (1 / X) 1) :=
    (hcont_pow1.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_pow2 : IntegrableOn (fun r : ℝ => r ^ (s - 2)) (Set.Ioo (1 / X) 1) :=
    (hcont_pow2.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_OT : IntegrableOn (fun r : ℝ => OT r * r ^ (s - 1)) (Set.Ioo (1 / X) 1) :=
    (hOT_icc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- Reflect the dual slice integral.
  have hP2 : (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * (OTD (1 / r) * (1 / r) ^ (-s)) :=
    reflectionCore_inv_cov X hX1 (fun y => OTD y * y ^ (-s))
  -- Rewrite the reflected integrand to `X·OT(r)·r^{s-1} + X·V·r^{s-1} − V·r^{s-2}`.
  have hP2' : (∫ r in Set.Ioo (1 / X) (1 : ℝ), (1 / r ^ 2) * (OTD (1 / r) * (1 / r) ^ (-s)))
      = ∫ r in Set.Ioo (1 / X) (1 : ℝ),
          (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1) - V * r ^ (s - 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1.le
    rw [hinv r hr0]
    -- `(1/r)^{-s} = r^s`
    have hpr : (1 / r) ^ (-s) = r ^ s := by
      rw [one_div, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le, neg_neg]
    rw [hpr]
    -- `1/r^2 = r^{-2}`, then collect powers
    have e1 : (1 / r ^ 2) * r ^ s = r ^ (s - 2) := by
      have h2 : (r : ℝ) ^ (2 : ℕ) = r ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast r 2]; norm_num
      rw [div_mul_eq_mul_div, one_mul, show (r ^ 2 : ℝ) = r ^ (2 : ℕ) by norm_num, h2,
        ← Real.rpow_sub hr0]
    have e2 : r ^ (s - 2) * r = r ^ (s - 1) := by
      rw [show (s - 1) = (s - 2) + 1 by ring, Real.rpow_add hr0, Real.rpow_one]
    -- expand
    have : (1 / r ^ 2) * ((X * r * (OT r + V) - V) * r ^ s)
        = X * (r ^ (s - 2) * r) * (OT r + V) - V * (r ^ (s - 2)) := by
      rw [show (X * r * (OT r + V) - V) * r ^ s
          = X * r * (OT r + V) * r ^ s - V * r ^ s by ring]
      rw [mul_sub]
      congr 1
      · rw [show (1 / r ^ 2) * (X * r * (OT r + V) * r ^ s)
            = X * r * (OT r + V) * ((1 / r ^ 2) * r ^ s) by ring, e1]; ring
      · rw [show (1 / r ^ 2) * (V * r ^ s) = V * ((1 / r ^ 2) * r ^ s) by ring, e1]
    rw [this, e2]; ring
  -- Reflect the `OT(u/X)·u^{s-1}` slice via `u = X·r` to `X^s·∫_{(1/X,1)} OT(r)·r^{s-1}`.
  have hP1 : (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * ∫ r in Set.Ioo (1 / X) (1 : ℝ), OT r * r ^ (s - 1) := by
    -- `u = X·r` maps `(1/X,1) → (1,X)` with derivative `X`.
    have hderiv : ∀ r ∈ Set.Ioo (1 / X) (1 : ℝ),
        HasDerivWithinAt (fun r : ℝ => X * r) X (Set.Ioo (1 / X) (1 : ℝ)) r := by
      intro r _
      simpa using ((hasDerivAt_id r).const_mul X).hasDerivWithinAt
    have hinj : Set.InjOn (fun r : ℝ => X * r) (Set.Ioo (1 / X) (1 : ℝ)) := by
      intro a _ b _ hab; exact mul_left_cancel₀ hX0.ne' hab
    have himg : (fun r : ℝ => X * r) '' (Set.Ioo (1 / X) (1 : ℝ)) = Set.Ioo (1 : ℝ) X := by
      ext z
      simp only [Set.mem_image, Set.mem_Ioo]
      constructor
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        have hr0 : (0 : ℝ) < r := lt_trans hXinv hr1
        rw [div_lt_iff₀ hX0] at hr1
        constructor
        · nlinarith [hr1]
        · nlinarith [hr2]
      · rintro ⟨hz1, hz2⟩
        have hz0 : (0 : ℝ) < z := lt_trans one_pos hz1
        refine ⟨z / X, ⟨?_, ?_⟩, by rw [mul_div_cancel₀ z hX0.ne']⟩
        · rw [lt_div_iff₀ hX0, div_mul_cancel₀ 1 hX0.ne']; exact hz1
        · rw [div_lt_one hX0]; exact hz2
    have key := integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo hderiv hinj (fun u => OT (u / X) * u ^ (s - 1))
    rw [himg] at key
    rw [key, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hXinv hr.1.le
    have hXs : X * X ^ (s - 1) = X ^ s := by
      have : X ^ (1 : ℝ) * X ^ (s - 1) = X ^ (1 + (s - 1)) := (Real.rpow_add hX0 _ _).symm
      rw [Real.rpow_one] at this; rw [this]; congr 1; ring
    rw [abs_of_pos hX0, smul_eq_mul, mul_div_cancel_left₀ r hX0.ne',
      Real.mul_rpow hX0.le hr0.le]
    rw [show X * (OT r * (X ^ (s - 1) * r ^ (s - 1)))
        = (X * X ^ (s - 1)) * (OT r * r ^ (s - 1)) by ring, hXs]
  -- Pure-power interval integrals over `(1/X, 1)`.
  have hA : (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 1)) = (1 - (1 / X) ^ s) / s := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hXinv1.le,
      integral_rpow (Or.inl (by linarith))]
    rw [show s - 1 + 1 = s by ring, Real.one_rpow]
  have hB : (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 2)) = (1 - (1 / X) ^ (s - 1)) / (s - 1) := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hXinv1.le,
      integral_rpow (Or.inl (by linarith))]
    rw [show s - 2 + 1 = s - 1 by ring, Real.one_rpow]
  -- Assemble: split the reflected integral by linearity, substitute, and cancel the `OT`-piece.
  have hsplit : (∫ r in Set.Ioo (1 / X) (1 : ℝ),
        (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1) - V * r ^ (s - 2)))
      = X * (∫ r in Set.Ioo (1 / X) (1 : ℝ), OT r * r ^ (s - 1))
        + X * V * (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 1))
        - V * (∫ r in Set.Ioo (1 / X) (1 : ℝ), r ^ (s - 2)) := by
    have hsub : (∫ r in Set.Ioo (1 / X) (1 : ℝ),
          ((X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)) - V * r ^ (s - 2)))
        = (∫ r in Set.Ioo (1 / X) (1 : ℝ), (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)))
          - ∫ r in Set.Ioo (1 / X) (1 : ℝ), V * r ^ (s - 2) :=
      MeasureTheory.integral_sub
        ((hint_OT.const_mul X).add (hint_pow1.const_mul (X * V))) (hint_pow2.const_mul V)
    have hadd : (∫ r in Set.Ioo (1 / X) (1 : ℝ), (X * (OT r * r ^ (s - 1)) + X * V * r ^ (s - 1)))
        = (∫ r in Set.Ioo (1 / X) (1 : ℝ), X * (OT r * r ^ (s - 1)))
          + ∫ r in Set.Ioo (1 / X) (1 : ℝ), X * V * r ^ (s - 1) :=
      MeasureTheory.integral_add (hint_OT.const_mul X) (hint_pow1.const_mul (X * V))
    rw [hsub, hadd, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hP2, hP2', hsplit, hP1, hA, hB]
  -- Now everything is in closed form; the `X^s·∫OT` pieces cancel after `X^{s-1}·X = X^s`.
  have hXpow : X ^ s = X ^ (s - 1) * X := by
    have : X ^ (s - 1) * X ^ (1 : ℝ) = X ^ (s - 1 + 1) := (Real.rpow_add hX0 _ _).symm
    rw [Real.rpow_one] at this
    rw [this]; congr 1; ring
  rw [hXpow]
  ring

/-- **The full real reflection identity** assembling the head/dual changes of variables and the
slice reflection: the raw real decomposition equals the clean pole plus the two scaled target tails.
For `1 < X`, `1 < s`, with the inversion law and tail integrabilities and continuity of `OT`, `OTD`
on `Ioi 0`. -/
private theorem reflectionCore_main (X V a s : ℝ) (hX1le : 1 ≤ X) (hs : 1 < s) (OT OTD : ℝ → ℝ)
    (hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V)
    (hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ)))
    (hI2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi (1 : ℝ)))
    (hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ)))
    (hOTDcont : ContinuousOn OTD (Set.Ioi (0 : ℝ))) :
    a * X ^ s * (-V / s + (V / X) / (s - 1))
        + a * X ^ s * (∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1))
        + a * X ^ (s - 1) * (∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s))
      = a * V / (s * (s - 1))
        + a * (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
        + a * (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s)) := by
  rcases eq_or_lt_of_le hX1le with hXeq | hX1
  · -- `X = 1`: the slice integrals are over the empty interval; pure pole algebra.
    subst hXeq
    have hs0 : s ≠ 0 := by linarith
    have hs10 : s - 1 ≠ 0 := by linarith
    simp only [Real.one_rpow, one_mul, div_one, mul_one]
    field_simp
    ring
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hXinv : (0 : ℝ) < 1 / X := by positivity
  -- Bounded-slice integrabilities (continuity on `[1,X] ⊂ Ioi 0`).
  have hcont_pow1 : ContinuousOn (fun u : ℝ => u ^ (s - 1)) (Set.Icc (1 : ℝ) X) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro u hu; left; exact (lt_of_lt_of_le one_pos hu.1).ne'
  have hcont_pownegs : ContinuousOn (fun u : ℝ => u ^ (-s)) (Set.Icc (1 : ℝ) X) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro u hu; left; exact (lt_of_lt_of_le one_pos hu.1).ne'
  have hOTcomp : ContinuousOn (fun u : ℝ => OT (u / X)) (Set.Icc (1 : ℝ) X) := by
    apply hOTcont.comp (continuousOn_id.div_const X)
    intro u hu
    have : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
    simp only [Set.mem_Ioi]; positivity
  have hint_P1 : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioo (1 : ℝ) X) :=
    ((hOTcomp.mul hcont_pow1).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hint_P2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioo (1 : ℝ) X) :=
    (((hOTDcont.mono (fun u hu => lt_of_lt_of_le one_pos hu.1)).mul
      hcont_pownegs).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  -- Split `J1` and `I2` at `X`:  `Ioi 1 = Ioo 1 X ∪ Ici X`.
  have hunion : Set.Ioo (1 : ℝ) X ∪ Set.Ici X = Set.Ioi (1 : ℝ) := Set.Ioo_union_Ici_eq_Ioi hX1
  have hdisj : Disjoint (Set.Ioo (1 : ℝ) X) (Set.Ici X) := by
    rw [Set.disjoint_left]
    rintro u hu hu'
    exact absurd hu.2 (not_lt.mpr hu')
  -- `∫_{Ici X} = ∫_{Ioi X}` (the single point `X` is null).
  have hIciX_OT : (∫ u in Set.Ici X, OT (u / X) * u ^ (s - 1))
      = ∫ u in Set.Ioi X, OT (u / X) * u ^ (s - 1) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici).symm
  have hIciX_OTD : (∫ y in Set.Ici X, OTD y * y ^ (-s))
      = ∫ y in Set.Ioi X, OTD y * y ^ (-s) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici).symm
  -- `J1 = ∫_{Ioo 1 X} + ∫_{Ioi X}`, and `∫_{Ioi X} OT(u/X)u^{s-1} = X^s·I1`.
  have hint_headX : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ioi X) :=
    reflectionCore_head_integrable X s hX0 OT hI1
  have hint_headXci : IntegrableOn (fun u => OT (u / X) * u ^ (s - 1)) (Set.Ici X) :=
    hint_headX.congr_set_ae (Ioi_ae_eq_Ici).symm
  have hint_I2Xci : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ici X) :=
    (hI2.mono_set (Set.Ioi_subset_Ioi hX1.le)).congr_set_ae (Ioi_ae_eq_Ici).symm
  have hJ1 : (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
      = (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
        + X ^ s * ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) := by
    have hu : (∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1))
        = (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
          + ∫ u in Set.Ici X, OT (u / X) * u ^ (s - 1) := by
      rw [← setIntegral_union hdisj measurableSet_Ici hint_P1 hint_headXci, hunion]
    rw [hu, hIciX_OT, reflectionCore_head_cov X s hX0 OT]
  -- `I2 = ∫_{Ioo 1 X} OTD y^{-s} + ∫_{Ioi X} OTD y^{-s}`, and `J2 = X^{s-1}·∫_{Ioi X} OTD y^{-s}`.
  have hI2split : (∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s))
      = (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        + ∫ y in Set.Ioi X, OTD y * y ^ (-s) := by
    rw [← hIciX_OTD, ← setIntegral_union hdisj measurableSet_Ici hint_P2 hint_I2Xci, hunion]
  have hJ2 : (∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s))
      = X ^ (s - 1) * ∫ y in Set.Ioi X, OTD y * y ^ (-s) :=
    reflectionCore_dual_cov X s hX0 OTD
  -- The slice identity.
  have hslice := reflectionCore_slice X V s hX1 hs OT OTD hinv hOTcont
  -- `X^s·(1/X)^s = 1` and `X^{s-1}·(1/X)^{s-1} = 1` (clears the pole bookkeeping).
  have hpow_s : X ^ s * (1 / X) ^ s = 1 := by
    rw [one_div, Real.inv_rpow hX0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hX0 s).ne']
  have hpow_s1 : X ^ (s - 1) * (1 / X) ^ (s - 1) = 1 := by
    rw [one_div, Real.inv_rpow hX0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hX0 (s - 1)).ne']
  -- Assemble: substitute `J1`, `I2`-split, `J2` into the goal, then use `hslice`.
  rw [hJ1, hI2split, hJ2]
  -- The remaining identity is purely algebraic given `hslice`, `hpow_s`, `hpow_s1`.
  -- `hslice : X^{s-1}·P2 − P1 = X^s·V·A − X^{s-1}·V·B` with `A = (1−(1/X)^s)/s`, `B = ...`.
  have key : X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
      - (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ s * V * ((1 - (1 / X) ^ s) / s)
        - X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1)) := hslice
  -- Now everything is closed-form.  Expand `(1/X)^s`, `(1/X)^{s-1}` via the cancellation facts.
  have hXspos : (0 : ℝ) < X ^ s := Real.rpow_pos_of_pos hX0 s
  have hXs1pos : (0 : ℝ) < X ^ (s - 1) := Real.rpow_pos_of_pos hX0 (s - 1)
  have hinvA : (1 / X) ^ s = (X ^ s)⁻¹ := by
    rw [eq_comm, inv_eq_of_mul_eq_one_left]; rw [mul_comm]; exact hpow_s
  have hinvB : (1 / X) ^ (s - 1) = (X ^ (s - 1))⁻¹ := by
    rw [eq_comm, inv_eq_of_mul_eq_one_left]; rw [mul_comm]; exact hpow_s1
  have hAexp : X ^ s * V * ((1 - (1 / X) ^ s) / s) = V * (X ^ s - 1) / s := by
    rw [hinvA]; field_simp
  have hBexp : X ^ (s - 1) * V * ((1 - (1 / X) ^ (s - 1)) / (s - 1))
      = V * (X ^ (s - 1) - 1) / (s - 1) := by
    rw [hinvB]; field_simp
  rw [hAexp, hBexp] at key
  -- Final algebra:  use `key` to eliminate the slice integrals; `s ≠ 0`, `s − 1 ≠ 0`.
  have hs0 : s ≠ 0 := by linarith
  have hs10 : s - 1 ≠ 0 := by linarith
  -- Substitute the slice integrals via `key` (treated as `A_int = B_int + closed`).
  have hP1eq : (∫ u in Set.Ioo (1 : ℝ) X, OT (u / X) * u ^ (s - 1))
      = X ^ (s - 1) * (∫ y in Set.Ioo (1 : ℝ) X, OTD y * y ^ (-s))
        - (V * (X ^ s - 1) / s - V * (X ^ (s - 1) - 1) / (s - 1)) := by
    linarith [key]
  rw [hP1eq]
  have hXpow : X ^ s = X ^ (s - 1) * X := by
    have h := (Real.rpow_add hX0 (s - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; congr 1; ring
  rw [hXpow]
  field_simp
  ring

variable {K} in
/-- **Per-ideal residue inequality, proved directly from the local decomposition.** For real
`s > 1`, dedekind's completed partial zeta dominates its pole residue after multiplying by
`s*(s-1)`: `partialCompletedZetaResidue K ≤ s*(s-1)*(completedPartialZeta K 𝔞 (s:ℂ)).re`.

This is the exact analytic fact used downstream. Compared with the former bridge through the full
existential `partialCompletedZeta_mellin_formula`, this proof stops at the `u`-tail form supplied by
the reflection identity and drops the explicit `Φ, Ψ` density packaging. -/
theorem partialCompletedZetaResidue_le (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    partialCompletedZetaResidue K ≤
      s * (s - 1) * (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re := by
  set X : ℝ := Theta.covolume K 𝔞 with hX
  set a : ℝ := 1 / (Units.torsionOrder K : ℝ) with ha
  set ρ : ℝ := partialCompletedZetaResidue K with hρ
  set OT : ℝ → ℝ := fun u => (orbitTheta K 𝔞 u).re with hOT
  set OTD : ℝ → ℝ := fun u => (orbitThetaFrac K (Theta.dualIdeal K 𝔞) u).re with hOTD
  -- Positivity facts on `X` (covolume = 𝔑(𝔞)·√|d| > 0).
  have hXpos : 0 < X := by
    rw [hX, Theta.covolume]
    have hNpos : (0 : ℝ) < (Ideal.absNorm 𝔞 : ℝ) := by
      have : Ideal.absNorm 𝔞 ≠ 0 := fun h =>
        hne (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
      positivity
    have hd : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    have : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| := Real.sqrt_pos.mpr hd
    positivity
  set V : ℝ := (surfaceVolume K).re with hV
  -- `ρ = a·V` (residue identity `V = ρ·w` and `a = 1/w`).
  have hρaV : ρ = a * V := by
    rw [hρ, hV, ha, surfaceVolume_re_eq_residue_mul_torsion K]
    have hw : (Units.torsionOrder K : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.Units.torsionOrder_ne_zero K
    field_simp
  -- The `IsMellinPair` packaging (continuity, decay/integrability, inversion).
  obtain ⟨_c, _α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 hne
  -- Real inversion law: `OTD (1/r) = X·r·(OT r + V) − V`.
  have hsurf : surfaceVolume K = ((surfaceVolume K).re : ℂ) := by rw [surfaceVolume]; simp
  have hcovC : (Theta.covolume K 𝔞 : ℂ)⁻¹ = ((1 / X : ℝ) : ℂ) := by
    rw [hX]; push_cast; ring
  have hinv : ∀ r, 0 < r → OTD (1 / r) = X * r * (OT r + V) - V := by
    intro r hr
    have hrinv : (0 : ℝ) < 1 / r := by positivity
    -- Apply the complex inversion at `1/r` (so `1/(1/r) = r`).
    have hI := radialTheta_inversion (K := K) 𝔞 hne (1 / r) hrinv
    rw [one_div_one_div] at hI
    obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 r
    obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) (1 / r)
    -- Express both sides of `hI` as `ofReal`s, then strip via injectivity.
    have hOTr : orbitTheta K 𝔞 r = ((OT r : ℝ) : ℂ) := by
      rw [hOT]; exact ofReal_re_of_im_zero ho1
    have hOTDr : orbitThetaFrac K (Theta.dualIdeal K 𝔞) (1 / r) = ((OTD (1 / r) : ℝ) : ℂ) := by
      rw [hOTD]; exact ofReal_re_of_im_zero ho2
    have hRT : radialTheta K 𝔞 r = ((OT r + V : ℝ) : ℂ) := by
      rw [radialTheta, hOTr, hsurf, ← Complex.ofReal_add]
    have hRTD : radialThetaDual K 𝔞 (1 / r) = ((OTD (1 / r) + V : ℝ) : ℂ) := by
      rw [radialThetaDual, hOTDr, hsurf, ← Complex.ofReal_add]
    rw [hRT, hRTD, hcovC, Real.rpow_one] at hI
    -- `hI : (OT r + V : ℂ) = (1/X : ℂ)·(1/r : ℂ)·(OTD(1/r) + V : ℂ)`
    have hIr : (OT r + V) = (1 / X) * (1 / r) * (OTD (1 / r) + V) := by
      have h := hI
      push_cast at h
      exact_mod_cast h
    -- Solve for `OTD (1/r)`:  multiply by `X·r` and rearrange.
    have hmul : X * r * (OT r + V) = OTD (1 / r) + V := by
      rw [hIr]; field_simp
    linarith [hmul]
  -- Real tail integrabilities, from the complex `mellinTail_integrable_left/right` via `.re`.
  have hI1 : IntegrableOn (fun y => OT y * y ^ (s - 1)) (Set.Ioi (1 : ℝ)) := by
    have hC := mellinTail_integrable_left hpair (s := (s : ℂ))
    have hre : IntegrableOn (fun y => (((radialTheta K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) := hC.re
    refine hre.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 y
    have hfa : radialTheta K 𝔞 y - surfaceVolume K = ((OT y : ℝ) : ℂ) := by
      rw [radialTheta, add_sub_cancel_right, hOT]; exact ofReal_re_of_im_zero ho1
    have hpw : (y : ℂ) ^ ((s : ℂ) - 1) = ((y ^ (s - 1) : ℝ) : ℂ) := by
      rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hy0.le]
    show (((radialTheta K 𝔞 y - surfaceVolume K) * (y : ℂ) ^ ((s : ℂ) - 1)).re) = OT y * y ^ (s - 1)
    rw [hfa, hpw, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hI2 : IntegrableOn (fun y => OTD y * y ^ (-s)) (Set.Ioi (1 : ℝ)) := by
    have hC := mellinTail_integrable_right hpair (s := (s : ℂ))
    have hre : IntegrableOn (fun y => (((Theta.covolume K 𝔞 : ℂ)⁻¹
        * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) := hC.re
    -- `hre` is integrability of `(1/X)·OTD y·y^{-s}`; scale by `X`.
    have hreX : IntegrableOn (fun y => X * (((Theta.covolume K 𝔞 : ℂ)⁻¹
        * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re)) (Set.Ioi (1 : ℝ)) :=
      Integrable.const_mul hre X
    refine hreX.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) y
    have hga : radialThetaDual K 𝔞 y - surfaceVolume K = ((OTD y : ℝ) : ℂ) := by
      rw [radialThetaDual, add_sub_cancel_right, hOTD]; exact ofReal_re_of_im_zero ho2
    have hpw : (y : ℂ) ^ (((1 : ℝ) : ℂ) - (s : ℂ) - 1) = ((y ^ (-s) : ℝ) : ℂ) := by
      rw [show ((1 : ℝ) : ℂ) - (s : ℂ) - 1 = ((-s : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hy0.le]
    show X * (((Theta.covolume K 𝔞 : ℂ)⁻¹ * (radialThetaDual K 𝔞 y - surfaceVolume K)
        * (y : ℂ) ^ ((1 : ℂ) - (s : ℂ) - 1)).re) = OTD y * y ^ (-s)
    rw [show ((1 : ℂ) - (s : ℂ) - 1) = (((1 : ℝ) : ℂ) - (s : ℂ) - 1) by push_cast; ring,
      hga, hpw, hcovC]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, hX]
    have hcovne : Theta.covolume K 𝔞 ≠ 0 := by rw [← hX]; exact hXpos.ne'
    field_simp [hcovne]
  -- Continuity of `OT`, `OTD` on `Ioi 0`, from the continuity of `orbitTheta`/`orbitThetaFrac`.
  have hOTcont : ContinuousOn OT (Set.Ioi (0 : ℝ)) := by
    rw [hOT]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_orbitTheta K 𝔞)
  have hOTDcont : ContinuousOn OTD (Set.Ioi (0 : ℝ)) := by
    rw [hOTD]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orbitThetaFrac K (Theta.dualIdeal K 𝔞))
  -- `X ≥ 1`:  `X = 𝔑(𝔞)·√|d|`, both factors `≥ 1`.
  have hX1le : (1 : ℝ) ≤ X := by
    rw [hX, Theta.covolume]
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔞 : ℝ) := by
      have hpos : 0 < Ideal.absNorm 𝔞 := by
        rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔞) with h0 | hp
        · exact absurd (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h0) hne
        · exact hp
      exact_mod_cast hpos
    have hd1 : (1 : ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      apply Real.sqrt_le_sqrt
      have hz : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
      have hr : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast hz
      rw [Int.cast_abs] at hr; simpa using hr
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| :=
          mul_le_mul hN1 hd1 (by norm_num) (by positivity)
  -- Assemble a clean `u`-tail decomposition, but do not package the tails as `Φ, Ψ`.
  set I1 : ℝ := ∫ y in Set.Ioi (1 : ℝ), OT y * y ^ (s - 1) with hI1def
  set I2 : ℝ := ∫ y in Set.Ioi (1 : ℝ), OTD y * y ^ (-s) with hI2def
  set J1 : ℝ := ∫ u in Set.Ioi (1 : ℝ), OT (u / X) * u ^ (s - 1) with hJ1def
  set J2 : ℝ := ∫ u in Set.Ioi (1 : ℝ), OTD (X * u) * u ^ (-s) with hJ2def
  -- `pf = a·X^s` (the prefactor matches, using `X = 𝔑·√|d|`, `a = 1/w`).
  have hpf : (1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
      * (|(NumberField.discr K : ℝ)|) ^ (s / 2) = a * X ^ s := by
    rw [ha, hX, Theta.covolume, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
    have hsqrt : (Real.sqrt |(NumberField.discr K : ℝ)|) ^ s = |(NumberField.discr K : ℝ)| ^ (s / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
      congr 1; ring
    rw [hsqrt]; ring
  -- `T.re = I1 + (1/X)·I2` (the real tail form of `mellinTail`).
  have hTre : (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)).re
      = I1 + (1 / X) * I2 := by
    have htailReal : mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)
        = ((∫ y in Set.Ioi (1 : ℝ),
            ((orbitTheta K 𝔞 y).re * y ^ (s - 1)
              + (1 / Theta.covolume K 𝔞)
                * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s))) : ℝ) := by
      rw [mellinTail, ← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
      obtain ⟨ho1, _⟩ := orbitTheta_re_nonneg 𝔞 y
      obtain ⟨ho2, _⟩ := orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) y
      have hfa : radialTheta K 𝔞 y - surfaceVolume K = ((orbitTheta K 𝔞 y).re : ℂ) := by
        rw [radialTheta, add_sub_cancel_right]; exact ofReal_re_of_im_zero ho1
      have hga : radialThetaDual K 𝔞 y - surfaceVolume K
          = ((orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re : ℂ) := by
        rw [radialThetaDual, add_sub_cancel_right]; exact ofReal_re_of_im_zero ho2
      rw [hfa, hga]
      have hpow1 : (y : ℂ) ^ ((s : ℂ) - 1) = ((y ^ (s - 1) : ℝ) : ℂ) := by
        rw [show ((s : ℂ) - 1) = (((s - 1 : ℝ)) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hy0.le]
      have hpow2 : (y : ℂ) ^ (((1 : ℝ) : ℂ) - (s : ℂ) - 1) = ((y ^ (-s) : ℝ) : ℂ) := by
        rw [show ((1 : ℝ) : ℂ) - (s : ℂ) - 1 = ((-s : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hy0.le]
      rw [hpow1, hpow2, hcovC]
      push_cast; ring
    rw [htailReal, Complex.ofReal_re]
    -- Split the integral by linearity into `I1 + (1/X)·I2`.
    have hsplit : (∫ y in Set.Ioi (1 : ℝ),
          ((orbitTheta K 𝔞 y).re * y ^ (s - 1)
            + (1 / Theta.covolume K 𝔞)
              * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s)))
        = I1 + (1 / X) * I2 := by
      rw [hI1def, hI2def, hX]
      have hint_a : IntegrableOn (fun y => (orbitTheta K 𝔞 y).re * y ^ (s - 1))
          (Set.Ioi (1 : ℝ)) :=
        IntegrableOn.congr_fun hI1 (fun y _ => by rw [hOT]) measurableSet_Ioi
      have hint_b : IntegrableOn (fun y => 1 / Theta.covolume K 𝔞
          * (orbitThetaFrac K (Theta.dualIdeal K 𝔞) y).re * y ^ (-s)) (Set.Ioi (1 : ℝ)) := by
        have : IntegrableOn (fun y => (1 / Theta.covolume K 𝔞) * (OTD y * y ^ (-s)))
            (Set.Ioi (1 : ℝ)) := Integrable.const_mul hI2 _
        exact IntegrableOn.congr_fun this (fun y _ => by rw [hOTD]; ring) measurableSet_Ioi
      rw [MeasureTheory.integral_add hint_a hint_b]
      congr 1
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      rw [hOTD]; ring
    rw [hsplit]
  have hclean : (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
      = a * V / (s * (s - 1)) + a * J1 + a * J2 := by
    have hmain := reflectionCore_main X V a s hX1le hs OT OTD hinv hI1 hI2 hOTcont hOTDcont
    rw [completedPartialZeta_real_decomp 𝔞 hne hs, hpf, hTre]
    rw [← hV, ← hX]
    rw [show a * X ^ s * ((-V / s + 1 / X * V / (s - 1)) + (I1 + 1 / X * I2))
        = a * X ^ s * (-V / s + (V / X) / (s - 1)) + a * X ^ s * I1
          + a * X ^ s * (1 / X) * I2 by ring]
    rw [show a * X ^ s * (1 / X) = a * X ^ (s - 1) by
      rw [show X ^ s = X ^ (s - 1) * X by
        have h := (Real.rpow_add hXpos (s - 1) 1).symm
        rw [Real.rpow_one] at h; rw [h]; congr 1; ring]
      field_simp]
    rw [hI1def, hI2def, hJ1def, hJ2def]
    exact hmain
  -- The clean `u`-tails are nonnegative, so multiplying the clean decomposition by `s*(s-1)`
  -- dominates the residue.
  have ha_nonneg : 0 ≤ a := by rw [ha]; positivity
  have hJ1_nonneg : 0 ≤ J1 := by
    rw [hJ1def]
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans one_pos hu)
    have hOTnn : 0 ≤ OT (u / X) := by
      rw [hOT]
      exact (orbitTheta_re_nonneg 𝔞 (u / X)).2
    exact mul_nonneg hOTnn (Real.rpow_nonneg hu0 _)
  have hJ2_nonneg : 0 ≤ J2 := by
    rw [hJ2def]
    refine setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans one_pos hu)
    have hOTDnn : 0 ≤ OTD (X * u) := by
      rw [hOTD]
      exact (orbitThetaFrac_re_nonneg (Theta.dualIdeal K 𝔞) (X * u)).2
    exact mul_nonneg hOTDnn (Real.rpow_nonneg hu0 _)
  have htail_nonneg : 0 ≤ a * J1 + a * J2 :=
    add_nonneg (mul_nonneg ha_nonneg hJ1_nonneg) (mul_nonneg ha_nonneg hJ2_nonneg)
  rw [hclean]
  change ρ ≤ s * (s - 1) * (a * V / (s * (s - 1)) + a * J1 + a * J2)
  rw [hρaV]
  have hssne : s * (s - 1) ≠ 0 := by positivity
  have hss_nonneg : 0 ≤ s * (s - 1) := by positivity
  have htail_scaled : 0 ≤ s * (s - 1) * (a * J1 + a * J2) :=
    mul_nonneg hss_nonneg htail_nonneg
  have heq : s * (s - 1) * (a * V / (s * (s - 1)) + a * J1 + a * J2)
      = a * V + s * (s - 1) * (a * J1 + a * J2) := by
    rw [show a * V / (s * (s - 1)) + a * J1 + a * J2
        = a * V / (s * (s - 1)) + (a * J1 + a * J2) by ring,
      mul_add, mul_div_cancel₀ _ hssne]
  rw [heq]
  linarith

end SumProduct
