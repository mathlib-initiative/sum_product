/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Golden-ratio numerics

Elementary real-analytic facts about the golden ratio `φ` used in the construction
(Lemma 4.1) and in the unit-lattice separation (Lemma 3.6 / Lemma 3.7).
-/

open scoped NumberField
open Pointwise

namespace SumProduct

/-- `8/5 ≤ φ` (since `√5 ≥ 11/5`). -/
theorem goldenRatio_ge : (8 : ℝ) / 5 ≤ Real.goldenRatio := by
  have h5 : (11 : ℝ) / 5 ≤ Real.sqrt 5 := by
    rw [show (11 : ℝ) / 5 = Real.sqrt ((11 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  change (8 : ℝ) / 5 ≤ (1 + Real.sqrt 5) / 2
  linarith

/-- For `X ≥ 2` and `0 < ε ≤ 3/20`, with `n = ⌊X⌋`, the directness ratio `(n+εX)/(n−εX)` is below
`φ` (in fact below `8/5`). This is what lets `card_construction` apply with `r = εX`. -/
theorem floor_ratio_lt_goldenRatio {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((⌊X⌋₊ : ℝ) + ε * X) / ((⌊X⌋₊ : ℝ) - ε * X) < Real.goldenRatio := by
  have hn2nat : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hn2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn2nat
  have hXlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hX0 : (0 : ℝ) < X := by linarith
  have hεX : ε * X < 3 * (⌊X⌋₊ : ℝ) / 13 := by
    nlinarith [mul_le_mul_of_nonneg_right hε hX0.le, hXlt, hn2]
  have hden : (0 : ℝ) < (⌊X⌋₊ : ℝ) - ε * X := by nlinarith [hεX, hn2]
  rw [div_lt_iff₀ hden]
  nlinarith [hεX, goldenRatio_ge, mul_nonneg (sub_nonneg.mpr goldenRatio_ge) hden.le]

open Real in
/-- `2/5 < log φ` (since `exp(2/5) < 8/5 ≤ φ`); the separation slack for the Lemma 3.7 packing. -/
theorem two_fifths_lt_log_goldenRatio : (2 : ℝ) / 5 < Real.log Real.goldenRatio := by
  rw [Real.lt_log_iff_exp_lt goldenRatio_pos]
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hb : Real.exp 1 ^ 2 < (8 / 5 : ℝ) ^ 5 := by
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have h5 : Real.exp (2 / 5) ^ 5 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h25 : Real.exp (2 / 5) < 8 / 5 :=
    lt_of_pow_lt_pow_left₀ 5 (by norm_num) (by rw [h5, he2]; exact hb)
  linarith [goldenRatio_ge]

end SumProduct
