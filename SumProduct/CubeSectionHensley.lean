/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.CubeSectionCore

/-!
# Assembly: `unitBox` volume bound from the cube-section core

Combines the reduction (`SumProduct.CubeSection`) with the analytic core
(`cubeSection_fin_one_volume_bounds`) to prove the exact statement
`hensley_unitBox_volume`. The analytic input is the proved sinc-integral estimate
`cubeSumLaw_Icc_bounds` from `SumProduct.CubeSectionCore`.
-/

open MeasureTheory
open scoped Pointwise

namespace SumProduct

/-- The zero-dimensional cube section is the whole (one-point) space, of volume `1`. -/
theorem volume_cubeSection_fin_zero_toReal :
    (volume (cubeSection (Fin 0) 1)).toReal = 1 := by
  have huniv : cubeSection (Fin 0) 1 = Set.univ := by
    ext x; simp [mem_cubeSection]
  rw [huniv, show (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ => Set.univ by
      ext x; simp, volume_pi_pi]
  simp

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **Equation (3.1) as a theorem** (was `hensley_unitBox_volume`): the two-sided volume bound on
`unitBox K r`, with the sharp `√d` denominator and constants `1`/`5`, for every totally real `K`. -/
theorem hensley_unitBox_volume_proof (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) := by
  classical
  have hd1 : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  set m : ℕ := Module.finrank ℚ K - 1 with hm
  have hrm : (0 : ℝ) ≤ r ^ m := pow_nonneg hr _
  -- reduce the box volume to the unit `Fin m` cube section.
  have hbox : (volume (unitBox K r)).toReal
      = r ^ m * (volume (cubeSection (Fin m) 1)).toReal := by
    rw [unitBox_eq_cubeSection K r, volume_cubeSection_toReal r hr,
      volume_cubeSection_one_congr, card_index_eq (rfl : Module.finrank ℚ K = _)]
  rw [hbox]
  rcases eq_or_lt_of_le hd1 with hdeq | hd2
  · -- `d = 1`: `m = 0`, the cube section is a point of volume `1`; bounds are `1 ≤ 1 ≤ 5`.
    have hm0 : m = 0 := by omega
    rw [hm0, volume_cubeSection_fin_zero_toReal, ← hdeq]
    norm_num
  · -- `d ≥ 2`: apply the analytic core with `n = m ≥ 1`.
    have hmpos : 1 ≤ m := by omega
    obtain ⟨hlo, hhi⟩ := cubeSection_fin_one_volume_bounds m hmpos
    have hcast : ((m : ℝ) + 1) = (Module.finrank ℚ K : ℝ) := by
      have : (1 : ℕ) ≤ Module.finrank ℚ K := hd1
      rw [hm, Nat.cast_sub this]; ring
    rw [hcast] at hlo hhi
    set V1 := (volume (cubeSection (Fin m) 1)).toReal with hV1
    refine ⟨?_, ?_⟩
    · calc (2 * r) ^ m / Real.sqrt (Module.finrank ℚ K)
          = r ^ m * (2 ^ m / Real.sqrt (Module.finrank ℚ K)) := by rw [mul_pow]; ring
        _ ≤ r ^ m * V1 := mul_le_mul_of_nonneg_left hlo hrm
    · calc r ^ m * V1
          ≤ r ^ m * (5 * 2 ^ m / Real.sqrt (Module.finrank ℚ K)) :=
            mul_le_mul_of_nonneg_left hhi hrm
        _ = 5 * (2 * r) ^ m / Real.sqrt (Module.finrank ℚ K) := by rw [mul_pow]; ring

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **Equation (3.1)** (Hensley / Ball–Vaaler cube-slice volume bound), expressed in `logSpace K`:
the trace-zero box `unitBox K r ⊂ logSpace K ≅ ℝ^{d-1}` has volume in
`[(2r)^{d-1}/√d, 5(2r)^{d-1}/√d]`.

The public re-export of `hensley_unitBox_volume_proof`.  `unitBox K r`
is, definitionally, the sum-constrained cube `cubeSection {w ≠ w₀} r`; its volume reduces
(homogeneity + coordinate relabeling) to the 1-D law of a sum of `d-1` independent uniforms on
`[-1,1]`, whose interval probability is identified by Fourier inversion with `(1/π)∫ (sin t/t)^d`,
and bounded by the elementary estimate `π/√d ≤ ∫ (sin t/t)^d ≤ 5π/√d`. (No appeal to Vaaler/Ball;
the elementary sinc-integral bound suffices for the stated constants.) -/
theorem hensley_unitBox_volume (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) :=
  hensley_unitBox_volume_proof K r hr

end SumProduct
