/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.CubeSection
import SumProduct.SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Core analytic reduction for the sum-constrained cube

This file reduces the `cubeSection (Fin n) 1` volume estimate to the one-dimensional law of the
sum of `n` independent uniform variables on `[-1, 1]`.  The remaining estimate is isolated in
`cubeSumLaw_Icc_bounds`.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform

namespace SumProduct

noncomputable section

/-- The closed cube `[-1,1]^n` in `(Fin n → ℝ)`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))

/-- The coordinate-sum map `(x_i) ↦ ∑ i, x_i`. -/
def coordSum (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

/-- Normalized Lebesgue measure on the cube `[-1,1]^n`. -/
def uniformCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  (volume (unitCube n))⁻¹ • volume.restrict (unitCube n)

/-- The normalized uniform probability measure on `[-1, 1]`. -/
def uniformIntervalMeasure : Measure ℝ :=
  ((2 : NNReal)⁻¹) • volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- The one-dimensional law of the sum of the coordinates under normalized cube measure. -/
def cubeSumLaw (n : ℕ) : Measure ℝ :=
  (uniformCubeMeasure n).map (coordSum n)

theorem measurableSet_unitCube (n : ℕ) : MeasurableSet (unitCube n) := by
  exact isClosed_Icc.measurableSet

theorem measurable_coordSum (n : ℕ) : Measurable (coordSum n) := by
  simpa [coordSum] using Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i

theorem cubeSection_one_eq_unitCube_inter_sum (n : ℕ) :
    cubeSection (Fin n) 1 =
      unitCube n ∩ (coordSum n) ⁻¹' Set.Icc (-1 : ℝ) 1 := by
  ext x
  simp [cubeSection, unitCube, coordSum, abs_le, Pi.le_def, forall_and]

theorem volume_unitCube (n : ℕ) :
    volume (unitCube n) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
  rw [unitCube, Real.volume_Icc_pi]
  norm_num

instance instIsProbabilityMeasure_uniformIntervalMeasure :
    IsProbabilityMeasure uniformIntervalMeasure where
  measure_univ := by
    simp [uniformIntervalMeasure, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul]
    rw [show ENNReal.ofReal (1 + 1 : ℝ) = (2 : ℝ≥0∞) by norm_num]
    exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem Measure.pi_const_smul {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (c : NNReal) (μ : (i : ι) → Measure (α i))
    [∀ i, IsFiniteMeasure (μ i)] :
    Measure.pi (fun i => c • μ i) = (c ^ Fintype.card ι) • Measure.pi μ := by
  classical
  refine Measure.pi_eq (μ := fun i => c • μ i) (μ' := (c ^ Fintype.card ι) • Measure.pi μ)
    fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul]
  simp [Measure.smul_apply, Finset.prod_mul_distrib, Finset.prod_const, ENNReal.coe_pow]

theorem uniformCubeMeasure_eq_pi_uniformIntervalMeasure (n : ℕ) :
    uniformCubeMeasure n = Measure.pi fun _ : Fin n => uniformIntervalMeasure := by
  rw [uniformCubeMeasure, volume_unitCube, unitCube, ← Set.pi_univ_Icc]
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [uniformIntervalMeasure]
  rw [Measure.pi_const_smul]
  simp [ENNReal.smul_def, ENNReal.ofReal_pow, ENNReal.inv_pow, ENNReal.coe_pow,
    ENNReal.coe_inv]

theorem cubeSumLaw_eq_map_pi_sum (n : ℕ) :
    cubeSumLaw n =
      (Measure.pi fun _ : Fin n => uniformIntervalMeasure).map (fun x => ∑ i, x i) := by
  rw [cubeSumLaw, uniformCubeMeasure_eq_pi_uniformIntervalMeasure]
  rfl

/-- Characteristic function of the one-dimensional uniform law on `[-1, 1]`.

This is the elementary calculation
`(1 / 2) * ∫ x in [-1,1], exp (t * x * I) = sinc t`.
-/
theorem charFun_uniformIntervalMeasure (t : ℝ) :
    charFun uniformIntervalMeasure t = (Real.sinc t : ℂ) := by
  rw [uniformIntervalMeasure, charFun_apply_real]
  simp
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  by_cases ht : t = 0
  · subst t
    simp [Real.sinc_zero]
    norm_num [NNReal.smul_def]
  · have hsubst :
        (∫ x in (-1 : ℝ)..1, Complex.exp (↑t * ↑x * Complex.I)) =
          t⁻¹ • ∫ y in (-t)..t, Complex.exp (↑y * Complex.I) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (intervalIntegral.integral_comp_mul_left
          (f := fun y : ℝ => Complex.exp (↑y * Complex.I))
          (a := (-1 : ℝ)) (b := 1) (c := t) ht)
    rw [hsubst, integral_exp_mul_I_eq_sinc]
    norm_num [NNReal.smul_def]
    field_simp [ht]

theorem charFun_cubeSumLaw_eq_sinc_pow (n : ℕ) (t : ℝ) :
    charFun (cubeSumLaw n) t = (Real.sinc t : ℂ) ^ n := by
  rw [cubeSumLaw_eq_map_pi_sum]
  change charFun ((Measure.pi fun _ : Fin n => uniformIntervalMeasure).map
    (fun p : Fin n → ℝ => ∑ i, p i)) t = (Real.sinc t : ℂ) ^ n
  rw [ProbabilityTheory.charFun_map_sum_pi_eq_prod]
  simp [charFun_uniformIntervalMeasure, Finset.prod_const]

instance instIsProbabilityMeasure_uniformCubeMeasure (n : ℕ) :
    IsProbabilityMeasure (uniformCubeMeasure n) := by
  rw [uniformCubeMeasure_eq_pi_uniformIntervalMeasure]
  infer_instance

instance instIsProbabilityMeasure_cubeSumLaw (n : ℕ) :
    IsProbabilityMeasure (cubeSumLaw n) := by
  rw [cubeSumLaw]
  exact Measure.isProbabilityMeasure_map (measurable_coordSum n).aemeasurable

theorem cubeSumLaw_succ_eq_conv (n : ℕ) :
    cubeSumLaw (n + 1) = cubeSumLaw n ∗ uniformIntervalMeasure := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_cubeSumLaw_eq_sinc_pow, charFun_conv, charFun_cubeSumLaw_eq_sinc_pow,
    charFun_uniformIntervalMeasure, pow_succ]

theorem uniformIntervalMeasure_eq_withDensity :
    uniformIntervalMeasure =
      volume.withDensity
        (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x) := by
  rw [uniformIntervalMeasure]
  calc
    ((2 : NNReal)⁻¹) • volume.restrict (Set.Icc (-1 : ℝ) 1)
        = (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
          ext s hs
          rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, ENNReal.coe_inv_two, smul_eq_mul]
    _ = (volume.restrict (Set.Icc (-1 : ℝ) 1)).withDensity
          ((2 : ℝ≥0∞)⁻¹ • (1 : ℝ → ℝ≥0∞)) := by
          symm
          rw [withDensity_smul]
          rw [withDensity_one]
          fun_prop
    _ = volume.withDensity
          (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x) := by
          rw [withDensity_indicator measurableSet_Icc]
          congr 1
          ext x
          simp [Pi.smul_apply]

theorem conv_withDensity_right_eq
    (μ : Measure ℝ) [SFinite μ] {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    μ ∗ volume.withDensity f =
      volume.withDensity (fun z : ℝ => ∫⁻ x : ℝ, f (z - x) ∂μ) := by
  refine Measure.ext_of_lintegral _ ?_
  intro φ hφ
  rw [Measure.lintegral_conv hφ]
  rw [lintegral_withDensity_eq_lintegral_mul]
  · have hinner : ∀ x : ℝ,
        (∫⁻ y : ℝ, φ (x + y) ∂volume.withDensity f) =
          ∫⁻ y : ℝ, f y * φ (x + y) := by
      intro x
      rw [lintegral_withDensity_eq_lintegral_mul]
      · rfl
      · exact hf
      · exact hφ.comp (by fun_prop)
    simp_rw [hinner]
    have htranslate : ∀ x : ℝ,
        (∫⁻ y : ℝ, f y * φ (x + y)) =
          ∫⁻ a : ℝ, f (a - x) * φ a := by
      intro x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (MeasureTheory.lintegral_add_left_eq_self
          (μ := (volume : Measure ℝ)) (f := fun a : ℝ => f (a - x) * φ a) x)
    simp_rw [htranslate]
    rw [lintegral_lintegral_swap]
    · have hfactor : ∀ y : ℝ,
          (∫⁻ x : ℝ, f (y - x) * φ y ∂μ) =
            (∫⁻ x : ℝ, f (y - x) ∂μ) * φ y := by
        intro y
        rw [lintegral_mul_const'' (φ y)]
        exact (hf.comp (by fun_prop)).aemeasurable
      simp_rw [hfactor]
      rfl
    · fun_prop
  · fun_prop
  · exact hφ

noncomputable def cubeSumLawSuccDensity (n : ℕ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x) ∂cubeSumLaw n

theorem cubeSumLaw_succ_eq_withDensity (n : ℕ) :
    cubeSumLaw (n + 1) = volume.withDensity (cubeSumLawSuccDensity n) := by
  rw [cubeSumLaw_succ_eq_conv, uniformIntervalMeasure_eq_withDensity]
  exact conv_withDensity_right_eq (cubeSumLaw n) (measurable_const.indicator measurableSet_Icc)

theorem cubeSumLawSuccDensity_zero (n : ℕ) :
    cubeSumLawSuccDensity n 0 =
      (2 : ℝ≥0∞)⁻¹ * cubeSumLaw n (Set.Icc (-1 : ℝ) 1) := by
  rw [cubeSumLawSuccDensity]
  have hfun : (fun x : ℝ =>
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (0 - x)) =
      fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x := by
    ext x
    have hmem : 0 - x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · intro h
        constructor <;> linarith [h.1, h.2]
      · intro h
        constructor <;> linarith [h.1, h.2]
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem hx]
  rw [hfun]
  rw [lintegral_indicator measurableSet_Icc]
  rw [setLIntegral_const]

theorem cubeSumLawSuccDensity_zero_toReal (n : ℕ) :
    (cubeSumLawSuccDensity n 0).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal := by
  rw [cubeSumLawSuccDensity_zero]
  rw [ENNReal.toReal_mul]
  norm_num

theorem measurable_cubeSumLawSuccDensity (n : ℕ) :
    Measurable (cubeSumLawSuccDensity n) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun z x =>
    (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x)
  have hF : Measurable (Function.uncurry F) := by
    simpa [F, Function.uncurry] using
      ((measurable_const.indicator measurableSet_Icc).comp
        (measurable_fst.sub measurable_snd))
  simpa [cubeSumLawSuccDensity, F] using hF.lintegral_prod_right

theorem cubeSumLawSuccDensity_lintegral_ne_top (n : ℕ) :
    (∫⁻ x : ℝ, cubeSumLawSuccDensity n x) ≠ ∞ := by
  have hfin : (volume.withDensity (cubeSumLawSuccDensity n)) Set.univ ≠ ∞ := by
    rw [← cubeSumLaw_succ_eq_withDensity n]
    simp
  rw [withDensity_apply _ MeasurableSet.univ] at hfin
  simpa using hfin

theorem cubeSumLawSuccDensity_ae_lt_top (n : ℕ) :
    ∀ᵐ x : ℝ ∂volume, cubeSumLawSuccDensity n x < ∞ := by
  exact ae_lt_top (measurable_cubeSumLawSuccDensity n)
    (cubeSumLawSuccDensity_lintegral_ne_top n)

theorem integrable_cubeSumLawSuccDensity_toReal (n : ℕ) :
    Integrable (fun x : ℝ => (cubeSumLawSuccDensity n x).toReal) := by
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_cubeSumLawSuccDensity n).aemeasurable
    (cubeSumLawSuccDensity_lintegral_ne_top n)

theorem integrable_cubeSumLawSuccDensity_complex (n : ℕ) :
    Integrable (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ)) := by
  exact (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp
    (integrable_cubeSumLawSuccDensity_toReal n)

theorem cubeSumLaw_measure_Icc_toReal_eq_integral_density (m : ℕ) (a b : ℝ) :
    (cubeSumLaw (m + 1) (Set.Icc a b)).toReal =
      ∫ x in Set.Icc a b, (cubeSumLawSuccDensity m x).toReal := by
  let s := Set.Icc a b
  have hs : MeasurableSet s := measurableSet_Icc
  have htop : ∀ᵐ x ∂volume.restrict s, cubeSumLawSuccDensity m x < ∞ := by
    exact ae_restrict_of_ae (cubeSumLawSuccDensity_ae_lt_top m)
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := volume) (f := cubeSumLawSuccDensity m) (s := s)
      (measurable_cubeSumLawSuccDensity m) htop (fun _ : ℝ => (1 : ℝ)) hs
  have h' : ((volume.withDensity (cubeSumLawSuccDensity m)) s).toReal =
      ∫ x in s, (cubeSumLawSuccDensity m x).toReal := by
    simpa [measureReal_def] using h
  rw [cubeSumLaw_succ_eq_withDensity m]
  simpa [s] using h'

theorem cubeSumLawSuccDensity_eq_half_measure_Icc (n : ℕ) (z : ℝ) :
    cubeSumLawSuccDensity n z =
      (2 : ℝ≥0∞)⁻¹ * cubeSumLaw n (Set.Icc (z - 1) (z + 1)) := by
  rw [cubeSumLawSuccDensity]
  have hfun : (fun x : ℝ =>
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) (z - x)) =
      fun x : ℝ => (Set.Icc (z - 1) (z + 1)).indicator (fun _ =>
        (2 : ℝ≥0∞)⁻¹) x := by
    ext x
    have hmem : z - x ∈ Set.Icc (-1 : ℝ) 1 ↔ x ∈ Set.Icc (z - 1) (z + 1) := by
      constructor
      · intro h
        constructor <;> linarith [h.1, h.2]
      · intro h
        constructor <;> linarith [h.1, h.2]
    by_cases hx : x ∈ Set.Icc (z - 1) (z + 1)
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (mt hmem.mp hx), Set.indicator_of_notMem hx]
  rw [hfun]
  rw [lintegral_indicator measurableSet_Icc]
  rw [setLIntegral_const]

theorem cubeSumLawSuccDensity_toReal_eq_half_measure_Icc (n : ℕ) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (z - 1) (z + 1))).toReal := by
  rw [cubeSumLawSuccDensity_eq_half_measure_Icc]
  rw [ENNReal.toReal_mul]
  norm_num

theorem cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * ∫ x in (z - 1)..(z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
  rw [cubeSumLawSuccDensity_toReal_eq_half_measure_Icc]
  congr 1
  have hn' : (n - 1) + 1 = n := by omega
  calc
    (cubeSumLaw n (Set.Icc (z - 1) (z + 1))).toReal =
        (cubeSumLaw ((n - 1) + 1) (Set.Icc (z - 1) (z + 1))).toReal := by rw [hn']
    _ = ∫ x in Set.Icc (z - 1) (z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
      rw [cubeSumLaw_measure_Icc_toReal_eq_integral_density]
    _ = ∫ x in (z - 1)..(z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
      have hle : z - 1 ≤ z + 1 := by linarith
      rw [intervalIntegral.integral_of_le hle]
      rw [← integral_Icc_eq_integral_Ioc]

theorem continuousAt_cubeSumLawSuccDensity_toReal
    (n : ℕ) (hn : 1 ≤ n) :
    ContinuousAt (fun z : ℝ => (cubeSumLawSuccDensity n z).toReal) 0 := by
  let g : ℝ → ℝ := fun x => (cubeSumLawSuccDensity (n - 1) x).toReal
  have hg : Integrable g := by
    simpa [g] using integrable_cubeSumLawSuccDensity_toReal (n - 1)
  have hprim : Continuous (fun b : ℝ => ∫ x in (-1 : ℝ)..b, g x) :=
    hg.continuous_primitive (-1)
  have hcont : Continuous (fun z : ℝ =>
      (1 / 2 : ℝ) *
        ((∫ x in (-1 : ℝ)..(z + 1), g x) - ∫ x in (-1 : ℝ)..(z - 1), g x)) := by
    exact continuous_const.mul
      ((hprim.comp (continuous_id.add continuous_const)).sub
        (hprim.comp (continuous_id.sub continuous_const)))
  have heq : (fun z : ℝ => (cubeSumLawSuccDensity n z).toReal) =
      fun z : ℝ => (1 / 2 : ℝ) *
        ((∫ x in (-1 : ℝ)..(z + 1), g x) - ∫ x in (-1 : ℝ)..(z - 1), g x) := by
    ext z
    rw [cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral n hn z]
    have h1 : IntervalIntegrable g volume (-1 : ℝ) (z + 1) := hg.intervalIntegrable
    have h2 : IntervalIntegrable g volume (-1 : ℝ) (z - 1) := hg.intervalIntegrable
    rw [← intervalIntegral.integral_interval_sub_left h1 h2]
  rw [heq]
  exact hcont.continuousAt

theorem fourier_cubeSumLawSuccDensity_eq_charFun_scaled (n : ℕ) (w : ℝ) :
    𝓕 (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ)) w =
      charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w) := by
  rw [Real.fourier_eq]
  rw [charFun_apply_real]
  rw [cubeSumLaw_succ_eq_withDensity n]
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_cubeSumLawSuccDensity n)
      (cubeSumLawSuccDensity_ae_lt_top n)]
  simp [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc]

theorem integrable_fourier_cubeSumLawSuccDensity (n : ℕ) (hn : 1 ≤ n) :
    Integrable (𝓕 (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ))) := by
  have hsinc : Integrable (fun t : ℝ => (Real.sinc t) ^ (n + 1)) := by
    exact integrable_sinc_pow (Nat.succ_le_succ hn)
  have hscale_ne : (-2 * Real.pi) ≠ (0 : ℝ) := by
    nlinarith [Real.pi_pos]
  have hsinc_scaled :
      Integrable (fun w : ℝ => (Real.sinc ((-2 * Real.pi) * w)) ^ (n + 1)) :=
    hsinc.comp_mul_left' hscale_ne
  have hcomplex_scaled : Integrable
      (fun w : ℝ => ((Real.sinc ((-2 * Real.pi) * w) : ℂ) ^ (n + 1))) := by
    simpa using (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).integrable_comp hsinc_scaled
  have hchar_scaled : Integrable
      (fun w : ℝ => charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)) := by
    refine hcomplex_scaled.congr ?_
    filter_upwards with w
    rw [charFun_cubeSumLaw_eq_sinc_pow]
  refine hchar_scaled.congr ?_
  filter_upwards with w
  exact (fourier_cubeSumLawSuccDensity_eq_charFun_scaled n w).symm

/-- Fourier inversion at zero for the explicit density of `cubeSumLaw (n+1)`.

This is the remaining Route A analytic statement: use `cubeSumLaw_succ_eq_withDensity`, show the
real density `x ↦ (cubeSumLawSuccDensity n x).toReal` is continuous at `0`, identify its Fourier
transform with `charFun (cubeSumLaw (n+1))` under the `-2π` scaling, and apply
`MeasureTheory.Integrable.fourierInv_fourier_eq`.
-/
theorem cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun
    (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLawSuccDensity n 0).toReal =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
  let f : ℝ → ℂ := fun x => ((cubeSumLawSuccDensity n x).toReal : ℂ)
  have hf : Integrable f := by
    simpa [f] using integrable_cubeSumLawSuccDensity_complex n
  have hFint : Integrable (𝓕 f) := by
    simpa [f] using integrable_fourier_cubeSumLawSuccDensity n _hn
  have hv : ContinuousAt f 0 := by
    simpa [f, Function.comp_def] using
      ContinuousAt.comp
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).continuous.continuousAt)
        (continuousAt_cubeSumLawSuccDensity_toReal n _hn)
  have hinv : 𝓕⁻ (𝓕 f) 0 = f 0 := hf.fourierInv_fourier_eq hFint hv
  have hinvInt : ∫ w : ℝ, 𝓕 f w = f 0 := by
    simpa [Real.fourierInv_eq, f] using hinv
  have hinvRe : (cubeSumLawSuccDensity n 0).toReal = ∫ w : ℝ, (𝓕 f w).re := by
    have h := congrArg Complex.re hinvInt
    have h_re : ∫ w : ℝ, (𝓕 f w).re = (∫ w : ℝ, 𝓕 f w).re := by
      simpa [RCLike.re_eq_complex_re] using
        (integral_re (μ := volume) (f := fun w : ℝ => 𝓕 f w) hFint)
    rw [← h_re] at h
    simpa [f] using h.symm
  have hfour_re : (∫ w : ℝ, (𝓕 f w).re) =
      ∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re := by
    apply integral_congr_ae
    filter_upwards with w
    rw [fourier_cubeSumLawSuccDensity_eq_charFun_scaled]
  have hscale :
      (∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re) =
        (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
    have h := Measure.integral_comp_mul_left
      (fun t : ℝ => (charFun (cubeSumLaw (n + 1)) t).re) (-2 * Real.pi)
    have habs : |((-2 * Real.pi)⁻¹ : ℝ)| = (2 * Real.pi)⁻¹ := by
      rw [abs_inv]
      have hneg : (-2 * Real.pi : ℝ) < 0 := by nlinarith [Real.pi_pos]
      rw [abs_of_neg hneg]
      ring
    simpa [habs, smul_eq_mul, abs_of_pos Real.pi_pos, mul_comm, mul_left_comm, mul_assoc]
      using h
  calc
    (cubeSumLawSuccDensity n 0).toReal = ∫ w : ℝ, (𝓕 f w).re := hinvRe
    _ = ∫ w : ℝ, (charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w)).re := hfour_re
    _ = (2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := hscale

/-- Route A bridge, in the form needed for the cube law.

For `n ≥ 1`, add one independent uniform variable.  The law `cubeSumLaw (n + 1)` is then the
convolution of `cubeSumLaw n` with the uniform law on `[-1,1]`; its continuous density at `0` is
`(1 / 2) * cubeSumLaw n ([-1,1])`.  Fourier inversion at `0`, applied to this absolutely
continuous law whose characteristic function is integrable, gives the stated identity.
-/
theorem cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
  have hden := cubeSumLawSuccDensity_zero_toReal n
  have hfour := cubeSumLawSuccDensity_zero_eq_inv_two_pi_integral_re_charFun n _hn
  rw [hden] at hfour
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
        2 * ((1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal) := by ring
    _ = 2 * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re) := by
        rw [hfour]
    _ = (Real.pi)⁻¹ * ∫ t : ℝ, (charFun (cubeSumLaw (n + 1)) t).re := by
        field_simp [hπ]

/-- Route B analytic input: Fourier inversion of the interval indicator, integrated against the
sum law.

This is the missing Mathlib-facing fact behind the Parseval bridge.  It should follow from
`1_{[-1,1]}(x) = π⁻¹ ∫ t, sinc t * cos (t * x)` away from the two boundary points, plus Fubini and
`∫ cos (t*x) ∂μ = Re (charFun μ t)`.  The hypothesis `1 ≤ n` is used analytically to remove atoms
at `±1` and to get the integrability needed for Fubini.
-/
theorem cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun (n : ℕ) (_hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, Real.sinc t * (charFun (cubeSumLaw n) t).re := by
  rw [cubeSumLaw_Icc_eq_inv_pi_integral_re_charFun_succ n _hn]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [charFun_cubeSumLaw_eq_sinc_pow (n + 1) t, charFun_cubeSumLaw_eq_sinc_pow n t]
  have hre : ∀ m : ℕ, ((Real.sinc t : ℂ) ^ m).re = (Real.sinc t) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ, Complex.mul_re, ih]
        simp
  rw [hre (n + 1), hre n]
  rw [pow_succ]
  ring

/-- The Fourier inversion/Parseval bridge for the interval probability.

Using `charFun_cubeSumLaw_eq_sinc_pow` and the Fourier transform of `1_{[-1,1]}`, this should
identify `ℙ(|S_n| ≤ 1)` with the sinc-power integral. This is the main Mathlib API gap: current
Fourier inversion lemmas are stated for functions, while this statement needs the interval
probability of a finite measure.
-/
theorem cubeSumLaw_Icc_eq_sinc_integral (n : ℕ) (hn : 1 ≤ n) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (Real.pi)⁻¹ * ∫ t : ℝ, (Real.sinc t) ^ (n + 1) := by
  rw [cubeSumLaw_Icc_eq_inv_pi_integral_sinc_mul_re_charFun n hn]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [charFun_cubeSumLaw_eq_sinc_pow n t]
  have hre : ∀ m : ℕ, ((Real.sinc t : ℂ) ^ m).re = (Real.sinc t) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, pow_succ, Complex.mul_re, ih]
        simp
  rw [hre n]
  rw [pow_succ]
  ring

theorem cubeSumLaw_Icc_toReal_eq (n : ℕ) :
    (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal =
      (volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n := by
  change (cubeSumLaw n).real (Set.Icc (-1 : ℝ) 1) =
    volume.real (cubeSection (Fin n) 1) / (2 : ℝ) ^ n
  rw [cubeSumLaw, map_measureReal_apply (measurable_coordSum n) measurableSet_Icc]
  rw [uniformCubeMeasure, measureReal_ennreal_smul_apply]
  rw [measureReal_restrict_apply ((measurable_coordSum n) measurableSet_Icc)]
  rw [Set.inter_comm, ← cubeSection_one_eq_unitCube_inter_sum n, volume_unitCube]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (pow_nonneg zero_le_two n)]
  rw [div_eq_mul_inv, mul_comm]

/-- The remaining one-dimensional analytic estimate for the sum of independent uniforms on
`[-1,1]`.  This is the intended endpoint for either a B-spline/convolution proof or a Fourier proof.
-/
theorem cubeSumLaw_Icc_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n + 1 : ℝ) ≤ (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ∧
      (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ≤
        5 / Real.sqrt (n + 1 : ℝ) := by
  have hN : 2 ≤ n + 1 := Nat.succ_le_succ hn
  have hEq := cubeSumLaw_Icc_eq_sinc_integral n hn
  have hBounds := sinc_power_integral_bounds (n + 1) hN
  have hLower :
      Real.pi / Real.sqrt (n + 1 : ℝ) ≤ ∫ t : ℝ, (Real.sinc t) ^ (n + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using hBounds.1
  have hUpper :
      ∫ t : ℝ, (Real.sinc t) ^ (n + 1) ≤
        5 * Real.pi / Real.sqrt (n + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hBounds.2
  have hπnonneg : 0 ≤ (Real.pi)⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  rw [hEq]
  constructor
  · calc
      1 / Real.sqrt (n + 1 : ℝ)
          = (Real.pi)⁻¹ * (Real.pi / Real.sqrt (n + 1 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi)⁻¹ * ∫ t : ℝ, (Real.sinc t) ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left hLower hπnonneg
  · calc
      (Real.pi)⁻¹ * ∫ t : ℝ, (Real.sinc t) ^ (n + 1)
          ≤ (Real.pi)⁻¹ * (5 * Real.pi / Real.sqrt (n + 1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hUpper hπnonneg
      _ = 5 / Real.sqrt (n + 1 : ℝ) := by
        field_simp [Real.pi_ne_zero]

/-- The target two-sided bound for the unit cube section in dimension `n ≥ 1`. -/
theorem cubeSection_fin_one_volume_bounds (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) ≤
        (volume (cubeSection (Fin n) 1)).toReal ∧
      (volume (cubeSection (Fin n) 1)).toReal ≤
        5 * (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) := by
  have hP := cubeSumLaw_Icc_bounds n hn
  have hEq := cubeSumLaw_Icc_toReal_eq n
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  constructor
  · calc
      (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ)
          = (2 : ℝ) ^ n * (1 / Real.sqrt (n + 1 : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ n *
          ((volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left (by simpa [hEq] using hP.1) hpow.le
      _ = (volume (cubeSection (Fin n) 1)).toReal := by
        field_simp [hpow.ne']
  · calc
      (volume (cubeSection (Fin n) 1)).toReal
          = (2 : ℝ) ^ n *
          ((volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n) := by
        field_simp [hpow.ne']
      _ ≤ (2 : ℝ) ^ n * (5 / Real.sqrt (n + 1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [hEq] using hP.2) hpow.le
      _ = 5 * (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) := by ring

end

end SumProduct
