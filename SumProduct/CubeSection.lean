/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.Boxes

/-!
# The sum-constrained cube section and its volume

Development vehicle for removing the `hensley_unitBox_volume` axiom (eq. (3.1)).

For a `Fintype` index `ι` with `n = Fintype.card ι`, the *sum-constrained cube*
`cubeSection ι r = {y : ι → ℝ | (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r}` is, for the index
`{w : InfinitePlace K // w ≠ w₀}`, **definitionally** equal to `unitBox K r` (same predicate on
the same pi type `logSpace K`); see `unitBox_eq_cubeSection`. The target is the sharp two-sided
bound `(2r)^n / √(n+1) ≤ volume (cubeSection ι r) ≤ 5 (2r)^n / √(n+1)`, which transports verbatim to
`hensley_unitBox_volume` with `n = d - 1`, `n + 1 = d`. No Jacobian enters because `unitBox` is
already the intrinsic box on `logSpace`, not an embedded hyperplane slice.

This file builds the elementary scaffolding (definition, measurability, identification with
`unitBox`, the index cardinality). The analytic core (a `√n` central-density estimate) is developed
separately (`CubeSectionCore`, `CubeSectionHensley`).
-/

open MeasureTheory
open scoped Pointwise

namespace SumProduct

/-- The sum-constrained cube `{y : ι → ℝ | (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r}`. For the index
`{w : InfinitePlace K // w ≠ w₀}` this is definitionally `unitBox K r`. -/
def cubeSection (ι : Type*) [Fintype ι] (r : ℝ) : Set (ι → ℝ) :=
  {y | (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r}

variable {ι : Type*} [Fintype ι]

@[simp] theorem mem_cubeSection {r : ℝ} {y : ι → ℝ} :
    y ∈ cubeSection ι r ↔ (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r := Iff.rfl

theorem isClosed_cubeSection (r : ℝ) : IsClosed (cubeSection ι r) := by
  rw [cubeSection, Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  · exact isClosed_le (by fun_prop) continuous_const

theorem measurableSet_cubeSection (r : ℝ) : MeasurableSet (cubeSection ι r) :=
  (isClosed_cubeSection r).measurableSet

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- `unitBox K r` is, on the nose, the sum-constrained cube over the index `{w ≠ w₀}` of
`logSpace K`. This is the (Jacobian-free) transport identity for the volume. -/
theorem unitBox_eq_cubeSection (K : Type*) [Field K] [NumberField K] (r : ℝ) :
    unitBox K r = cubeSection {w : InfinitePlace K // w ≠ w₀} r := rfl

open scoped Classical in
open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem in
/-- For a totally real field of degree `d`, the index type of `logSpace K` (i.e. `{w ≠ w₀}`) has
cardinality `d - 1`. -/
theorem card_index_eq {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) :
    Fintype.card {w : InfinitePlace K // w ≠ w₀} = d - 1 := by
  classical
  have hcard : Fintype.card (InfinitePlace K) = d := by
    have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
    have hc := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hr := card_add_two_mul_card_eq_rank K
    rw [hd] at hr; omega
  rw [← hcard]
  exact Set.card_ne_eq w₀

/-- Homogeneity of the box: `cubeSection ι r = r • cubeSection ι 1` for `r ≥ 0`. -/
theorem cubeSection_smul (r : ℝ) (hr : 0 ≤ r) :
    cubeSection ι r = r • cubeSection ι 1 := by
  rcases hr.eq_or_lt with rfl | hr0
  · -- `r = 0`: both sides are `{0}`.
    have hne : (cubeSection ι 1).Nonempty := ⟨0, by simp [mem_cubeSection]⟩
    rw [Set.zero_smul_set hne]
    ext y
    simp only [mem_cubeSection, Set.mem_zero]
    constructor
    · rintro ⟨h1, -⟩
      funext i
      exact abs_eq_zero.mp (le_antisymm (h1 i) (abs_nonneg _))
    · rintro rfl
      refine ⟨fun i => ?_, ?_⟩ <;> simp
  · -- `0 < r`: rescale each coordinate by `r⁻¹`.
    have hr0' : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
    have key : ∀ a : ℝ, |r⁻¹ * a| ≤ 1 ↔ |a| ≤ r := fun a => by
      rw [abs_mul, abs_of_pos hr0', inv_mul_eq_div, div_le_one hr0]
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr0.ne', mem_cubeSection, mem_cubeSection]
    have hsum : (∑ i, (r⁻¹ • y) i) = r⁻¹ * ∑ i, y i := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]; exact h1 i
      · rw [hsum, key]; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · have hi := h1 i; rw [Pi.smul_apply, smul_eq_mul, key] at hi; exact hi
      · rw [hsum, key] at h2; exact h2

/-- The volume scales by `r ^ n` where `n = card ι` (homogeneity of degree `n`). -/
theorem volume_cubeSection (r : ℝ) (hr : 0 ≤ r) :
    volume (cubeSection ι r)
      = ENNReal.ofReal (r ^ Fintype.card ι) * volume (cubeSection ι 1) := by
  have hfin : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_pi ℝ
  rw [cubeSection_smul r hr,
    Measure.addHaar_smul_of_nonneg (μ := volume) (s := cubeSection ι 1) hr, hfin]

/-- `cubeSection ι r` has finite volume (it sits inside a sup-ball of radius `|r|`). -/
theorem volume_cubeSection_ne_top (r : ℝ) : volume (cubeSection ι r) ≠ ⊤ :=
  ne_top_of_le_ne_top (isCompact_closedBall (0 : ι → ℝ) |r|).measure_lt_top.ne
    (measure_mono fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
      intro i
      rw [Real.norm_eq_abs]
      exact le_trans (hy.1 i) (le_abs_self r))

/-- Real-valued homogeneity: `vol(cubeSection ι r).toReal = r ^ n · vol(cubeSection ι 1).toReal`. -/
theorem volume_cubeSection_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (cubeSection ι r)).toReal
      = r ^ Fintype.card ι * (volume (cubeSection ι 1)).toReal := by
  rw [volume_cubeSection r hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]

open scoped Classical in
/-- The unit cube-section volume depends only on `Fintype.card ι`: reindexing the coordinates by an
equivalence `Fin n ≃ ι` is measure-preserving and carries one box to the other. This lets the
analytic core be proved over `Fin n` and transported to `{w ≠ w₀}`. -/
theorem volume_cubeSection_one_congr (ι : Type*) [Fintype ι] :
    volume (cubeSection ι 1) = volume (cubeSection (Fin (Fintype.card ι)) 1) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have happ : ∀ (x : Fin (Fintype.card ι) → ℝ) (a), T x (e a) = x a :=
    fun x a => MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e x a
  have hmp : MeasurePreserving T volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have hpre : T ⁻¹' (cubeSection ι 1) = cubeSection (Fin (Fintype.card ι)) 1 := by
    ext x
    simp only [Set.mem_preimage, mem_cubeSection]
    have hsum : ∑ i, T x i = ∑ a, x a :=
      (Fintype.sum_equiv e (fun a => x a) (fun i => T x i) (fun a => (happ x a).symm)).symm
    refine ⟨fun h => ⟨fun a => ?_, ?_⟩, fun h => ⟨fun i => ?_, ?_⟩⟩
    · have hi := h.1 (e a); rwa [happ] at hi
    · rw [← hsum]; exact h.2
    · have hi := h.1 (e.symm i); rwa [← happ x (e.symm i), e.apply_symm_apply] at hi
    · rw [hsum]; exact h.2
  rw [← hmp.measure_preimage (measurableSet_cubeSection (ι := ι) 1).nullMeasurableSet, hpre]

end SumProduct
