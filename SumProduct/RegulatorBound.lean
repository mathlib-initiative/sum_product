/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.PartialZetaMellin
import SumProduct.MultiplicativeCount
import SumProduct.EulerBound

/-!
# Lemma 3.1 — regulator ≤ discriminant, via the functional equation

The analytic input about `ζ_K` is the per-ideal residue inequality
`partialCompletedZetaResidue_le`, proved in `SumProduct.PartialZetaMellin` using the in-repository
`DedekindZeta` support library (broadly following Neukirch, *Algebraic Number Theory*, Chapter VII
§§1 and 3–5). Applying it to ideal-class representatives and summing gives
`dedekindZeta_completed_ge_residue`
(`κ_K√|Δ_K| ≤ s(s-1)Z_K(s)`), which yields the residue bound `dedekindZeta_completed_residue_le`
(totally real, one division by `√|Δ_K|`). The Euler-product input `ζ_K(2) ≤ 2^d` is *proved* (not
assumed) in `SumProduct.EulerBound` (`dedekindZeta_two_re_le`). We also use Mathlib's analytic class
number formula `NumberField.dedekindZeta_residue`.

* `dedekind_residue_le` : `κ_K ≤ 2 (2/π)^d √|Δ_K|` (for `d ≥ 2`) — the residue bound at `s = 2`
  (`s(s-1) = 2`, `Γ(1) = 1`) combined with the Euler bound `ζ_K(2) ≤ 2^d`.
* `regulator_le_discr` (Lemma 3.1) : `R_K ≤ |Δ_K|`.  From `dedekind_residue_le`, the class
  number formula `κ_K = 2^{d-1} R_K h_K / √|Δ_K|`, `h_K ≥ 1`, and `4 ≤ π^d` (for `d ≥ 2`).
-/

open scoped NumberField
open Pointwise

namespace SumProduct

/-- `4 ≤ π^d` for `d ≥ 2` (since `π > 3`, already `π^2 > 9`). -/
private lemma four_le_pi_pow {d : ℕ} (hd : 2 ≤ d) : (4 : ℝ) ≤ Real.pi ^ d :=
  calc (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    _ ≤ Real.pi ^ d := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hd

open NumberField NumberField.InfinitePlace NumberField.Units in
/-- Summing the per-class residue `2^rR/w` over all ideal classes gives the residue of the
completed Dedekind zeta in Mathlib's normalization. -/
private lemma completedResidue_eq_classNumber_mul_partialResidue (K : Type*) [Field K]
    [NumberField K] :
    NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
        / Real.pi ^ nrComplexPlaces K
      = (classNumber K : ℝ) * partialCompletedZetaResidue K := by
  have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
  have hpi : Real.pi ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hw : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero K
  rw [NumberField.dedekindZeta_residue_def, partialCompletedZetaResidue]
  field_simp [hsq, hpi, hw]
  rw [pow_add, mul_pow]
  ring

open NumberField MeasureTheory NumberField.InfinitePlace in
/-- **Completed-zeta residue inequality**: summing the per-class residue inequality over ideal
classes gives, for real `s > 1`, that the completed zeta
times `s(s-1)` is at least its residue:
`κ_K√|Δ_K|/π^{r₂} ≤ s(s-1)·Z_K(s)`. -/
theorem dedekindZeta_completed_ge_residue (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ nrComplexPlaces K
      ≤ s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K
          * (NumberField.dedekindZeta K (s : ℂ)).re := by
  have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  set ρ := partialCompletedZetaResidue K with hρdef
  have hpartial : ∀ C : ClassGroup (𝓞 K),
      ρ ≤ s * (s - 1)
          * (DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K C) (s : ℂ)).re := by
    intro C
    rw [hρdef]
    refine partialCompletedZetaResidue_le (K := K) (DedekindZeta.idealClassRep K C) ?_ hs
    exact mem_nonZeroDivisors_iff_ne_zero.mp (Function.surjInv ClassGroup.mk0_surjective C).2
  have hsumineq :
      (classNumber K : ℝ) * ρ
        ≤ s * (s - 1) * (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := by
    have h := Finset.sum_le_sum
      (s := (Finset.univ : Finset (ClassGroup (𝓞 K)))) (fun C _ => hpartial C)
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h
    have hsumRe : (∑ C : ClassGroup (𝓞 K),
          (DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K C) (s : ℂ)).re)
        = (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := by
      rw [DedekindZeta.completedDedekindZeta, Complex.re_sum]
    rw [hsumRe] at h
    rw [NumberField.classNumber]
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hcompRe : (DedekindZeta.completedDedekindZeta K (s : ℂ)).re
      = (|(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K)
        * (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [DedekindZeta.completedDedekindZeta_eq K hsre, zInfty_ofReal K s, Complex.re_ofReal_mul]
  calc NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ nrComplexPlaces K
      = (classNumber K : ℝ) * ρ := by
          rw [hρdef, completedResidue_eq_classNumber_mul_partialResidue]
    _ ≤ s * (s - 1) * (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := hsumineq
    _ = s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K
          * (NumberField.dedekindZeta K (s : ℂ)).re := by rw [hcompRe]; ring

open NumberField NumberField.InfinitePlace in
/-- **Functional-equation residue bound** for totally real `K`: the **specialization** of Hecke's
functional equation `dedekindZeta_completed_ge_residue` to the totally real case (`nrComplexPlaces
K = 0`, so the complex Γ-factor drops out and `nrRealPlaces K = d`), divided by `√|Δ_K|`.  For
`s > 1`, `κ_K ≤ s(s-1)|Δ_K|^{(s-1)/2}π^{-ds/2}Γ(s/2)^d ζ_K(s)`.

For totally real `K` the residue is `ρ = κ_K√|Δ_K|` (the `1/π^{r₂}` is `1`), so
`dedekindZeta_completed_ge_residue` reads
`κ_K√|Δ_K| ≤ s(s-1)|Δ_K|^{s/2}(π^{-s/2}Γ(s/2))^d ζ_K(s)`; since
`(π^{-s/2}Γ(s/2))^d = π^{-ds/2}Γ(s/2)^d` and `|Δ_K|^{s/2} = |Δ_K|^{(s-1)/2}√|Δ_K|`, dividing by
`√|Δ_K| > 0` gives the claim. -/
theorem dedekindZeta_completed_residue_le (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K ≤
      s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
        * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
        * Real.Gamma (s / 2) ^ Module.finrank ℚ K
        * (NumberField.dedekindZeta K (s : ℂ)).re := by
  have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hsqΔ : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| := Real.sqrt_pos.mpr hΔ0
  -- Specialize the general theorem to the totally real case.
  have hc : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero K
  have hr : nrRealPlaces K = Module.finrank ℚ K := (IsTotallyReal.finrank K).symm
  have h := dedekindZeta_completed_ge_residue K s hs
  rw [hc, hr] at h
  simp only [pow_zero, div_one, mul_one] at h
  -- `(π^{-s/2}Γ(s/2))^d = π^{-ds/2}·Γ(s/2)^d`.
  have hG : (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ Module.finrank ℚ K
      = Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
        * Real.Gamma (s / 2) ^ Module.finrank ℚ K := by
    rw [mul_pow]; congr 1
    rw [← Real.rpow_natCast (Real.pi ^ (-(s / 2))) (Module.finrank ℚ K),
      ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  -- `|Δ|^{(s-1)/2}·√|Δ| = |Δ|^{s/2}`.
  have hAA : |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2) * Real.sqrt |(NumberField.discr K : ℝ)|
      = |(NumberField.discr K : ℝ)| ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hΔ0]; congr 1; ring
  have hge' : NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
      ≤ (s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
          * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
          * Real.Gamma (s / 2) ^ Module.finrank ℚ K
          * (NumberField.dedekindZeta K (s : ℂ)).re)
        * Real.sqrt |(NumberField.discr K : ℝ)| := by
    calc NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
        ≤ s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
            * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ Module.finrank ℚ K
            * (NumberField.dedekindZeta K (s : ℂ)).re := h
      _ = (s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
            * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
            * Real.Gamma (s / 2) ^ Module.finrank ℚ K
            * (NumberField.dedekindZeta K (s : ℂ)).re)
          * Real.sqrt |(NumberField.discr K : ℝ)| := by rw [hG, ← hAA]; ring
  exact le_of_mul_le_mul_right hge' hsqΔ

open NumberField in
/-- **Louboutin-type residue bound.** For a totally real number field `K` of degree `d ≥ 2`,
`κ_K ≤ 2 (2/π)^d √|Δ_K|`.  The residue bound `dedekindZeta_completed_residue_le` (from
the per-ideal residue inequality) at `s = 2` gives `κ_K ≤ 2 √|Δ_K| π^{-d} ζ_K(2)`; the *proved* Euler bound
`dedekindZeta_two_re_le` (`ζ_K(2) ≤ 2^d`) then yields the claim (`s(s-1) = 2`, `Γ(1) = 1`). -/
theorem dedekind_residue_le (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (_hd : 2 ≤ Module.finrank ℚ K) :
    NumberField.dedekindZeta_residue K
      ≤ 2 * (2 / Real.pi) ^ Module.finrank ℚ K * Real.sqrt |(NumberField.discr K : ℝ)| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `ζ_K(2) ≤ 2^d = (2/(2-1))^d`, the proved Euler-product bound.
  have hζ : (NumberField.dedekindZeta K (2 : ℂ)).re ≤ (2 / (2 - 1)) ^ Module.finrank ℚ K :=
    dedekindZeta_two_re_le.trans_eq (by rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num])
  refine ((dedekindZeta_completed_residue_le K 2 one_lt_two).trans
    (mul_le_mul_of_nonneg_left hζ ?_)).trans_eq ?_
  · -- the prefactor `2(2-1)|Δ|^{1/2}π^{-d}Γ(1)^d` is nonnegative
    have hb : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| ^ (((2 : ℝ) - 1) / 2) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hc : (0 : ℝ) ≤ Real.pi ^ (-(Module.finrank ℚ K : ℝ) * 2 / 2) :=
      (Real.rpow_pos_of_pos hpi _).le
    have hg : (0 : ℝ) ≤ Real.Gamma ((2 : ℝ) / 2) ^ Module.finrank ℚ K :=
      pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) hb) hc) hg
  set d := Module.finrank ℚ K with hddef
  have e1 : ((2 : ℝ) - 1) = 1 := by norm_num
  have eΓ : Real.Gamma ((2 : ℝ) / 2) = 1 := by
    rw [show (2 : ℝ) / 2 = 1 by norm_num]; exact Real.Gamma_one
  have esqrt : |(NumberField.discr K : ℝ)| ^ (((2 : ℝ) - 1) / 2)
      = Real.sqrt |(NumberField.discr K : ℝ)| := by rw [e1, ← Real.sqrt_eq_rpow]
  have epi : Real.pi ^ (-(d : ℝ) * 2 / 2) = (Real.pi ^ d)⁻¹ := by
    rw [show -(d : ℝ) * 2 / 2 = -(d : ℝ) by ring, Real.rpow_neg hpi.le, Real.rpow_natCast]
  rw [esqrt, epi, eΓ, e1, one_pow, div_one, div_pow]
  ring

open scoped Classical in
open NumberField NumberField.Units NumberField.InfinitePlace in
/-- **Lemma 3.1** (regulator ≤ discriminant), PROVED. For a totally real number field `K` of
degree `d ≥ 2`, `R_K ≤ |Δ_K|`. From `dedekind_residue_le` (the functional-equation residue bound
at `s = 2`), the analytic class number formula, and `h_K ≥ 1`. -/
theorem regulator_le_discr (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hd : 2 ≤ Module.finrank ℚ K) :
    NumberField.Units.regulator K ≤ |(NumberField.discr K : ℝ)| := by
  set d := Module.finrank ℚ K with hddef
  set Δ : ℝ := |(NumberField.discr K : ℝ)| with hΔdef
  have hd1 : 1 < d := hd
  set m : ℕ := d - 1 with hmdef
  have hΔ2 : (2 : ℝ) < Δ := by rw [hΔdef]; exact_mod_cast abs_discr_gt_two hd1
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hRpos : 0 < regulator K := regulator_pos K
  have hsqΔ : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ0
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hh1 : (1 : ℝ) ≤ (classNumber K : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (classNumber_ne_zero K)
  -- Analytic class number formula specialised to totally real K: κ = 2^{d-1} R h / √Δ.
  have hnrc : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hnrr : nrRealPlaces K = d := by
    have h := card_add_two_mul_card_eq_rank K
    rw [hnrc] at h; omega
  have htor : torsionOrder K = 2 := torsionOrder_eq_two_of_totallyReal
  have h2d : (2 : ℝ) ^ d = 2 ^ m * 2 := by rw [show d = m + 1 by omega, pow_succ]
  have hACNF : dedekindZeta_residue K
      = 2 ^ m * regulator K * (classNumber K : ℝ) / Real.sqrt Δ := by
    rw [dedekindZeta_residue_def, hnrc, hnrr, htor, pow_zero, mul_one, ← hΔdef, h2d]
    field_simp
    ring
  -- The functional-equation residue bound at s = 2.
  have hres := dedekind_residue_le K hd
  rw [← hddef, ← hΔdef, hACNF] at hres
  -- 2^m R h / √Δ ≤ 2 (2/π)^d √Δ ⟹ 2^m R h ≤ 2 (2/π)^d Δ
  have hstep : 2 ^ m * regulator K * (classNumber K : ℝ) ≤ 2 * (2 / Real.pi) ^ d * Δ := by
    have h2 := (div_le_iff₀ hsqΔ).mp hres
    calc 2 ^ m * regulator K * (classNumber K : ℝ)
        ≤ 2 * (2 / Real.pi) ^ d * Real.sqrt Δ * Real.sqrt Δ := h2
      _ = 2 * (2 / Real.pi) ^ d * Δ := by rw [mul_assoc, Real.mul_self_sqrt hΔ0.le]
  -- 2 (2/π)^d ≤ 2^{d-1}  (⟺ 4 ≤ π^d).
  have hnum : 2 * (2 / Real.pi) ^ d ≤ (2 : ℝ) ^ m := by
    have hpd : (0 : ℝ) < Real.pi ^ d := by positivity
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ hpd]
    have hpow : (2 : ℝ) * 2 ^ d = 2 ^ m * 4 := by rw [show d = m + 1 by omega, pow_succ]; ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (four_le_pi_pow hd) h2pos.le
  -- Combine and cancel.
  have hfin : 2 ^ m * regulator K * (classNumber K : ℝ) ≤ 2 ^ m * Δ :=
    hstep.trans (mul_le_mul_of_nonneg_right hnum hΔ0.le)
  have hRh : regulator K * (classNumber K : ℝ) ≤ Δ :=
    le_of_mul_le_mul_left (by rw [← mul_assoc]; exact hfin) h2pos
  calc regulator K = regulator K * 1 := (mul_one _).symm
    _ ≤ regulator K * (classNumber K : ℝ) := mul_le_mul_of_nonneg_left hh1 hRpos.le
    _ ≤ Δ := hRh

end SumProduct
