/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.Boxes
import SumProduct.GoldenRatio
import SumProduct.UnitSeparation
import SumProduct.Martinet
import SumProduct.AdditiveCount
import SumProduct.MultiplicativeCount
import SumProduct.RegulatorBound

/-!
# Section 4 and Theorem 1.1

The construction `A = G·P` of Lemma 4.1 (`lemma_4_1`), its directness and
cardinality/sum/product estimates, the real-embedded form Theorem 1.2 (`theorem_1_2`), and the
final headline result Theorem 1.1 (`sumProduct_false`): the sum-product conjecture is false
over `ℝ`.
-/

open scoped NumberField
open Pointwise

namespace SumProduct

/-- Every infinite place sends a natural number to itself. -/
theorem place_natCast {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (n : ℕ) : w (n : K) = n := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq w (n : K), map_natCast, Complex.norm_natCast]

/-- Elements of the translated box `n + B⁺(r)` have every archimedean absolute value in
`[n - r, n + r]`. This is the additive-box geometry behind both the directness of `A = G·P`
and the sumset bound in Lemma 4.1. -/
theorem place_translate_bound {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (n : ℕ) {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    (n : ℝ) - r ≤ w (((n : 𝓞 K) + b : 𝓞 K) : K) ∧
      w (((n : 𝓞 K) + b : 𝓞 K) : K) ≤ (n : ℝ) + r := by
  rw [mem_boxAdd] at hb
  have hwb : w (b : K) ≤ r := hb w
  have hwn : w (n : K) = n := place_natCast w n
  have hcast : (((n : 𝓞 K) + b : 𝓞 K) : K) = (n : K) + (b : K) := by push_cast; ring
  rw [hcast]
  refine ⟨?_, ?_⟩
  · have htri : w (n : K) ≤ w ((n : K) + (b : K)) + w (b : K) := by
      have hh := w.1.add_le ((n : K) + (b : K)) (-(b : K))
      rw [add_neg_cancel_right, AbsoluteValue.map_neg] at hh
      exact hh
    linarith
  · calc w ((n : K) + (b : K)) ≤ w (n : K) + w (b : K) := w.1.add_le _ _
      _ ≤ (n : ℝ) + r := by rw [hwn]; linarith

open Real in
/-- **Directness of the construction** (the key step in Lemma 4.1).

If `g₁(n + b₁) = g₂(n + b₂)` with `g₁, g₂` units, `b₁, b₂ ∈ B⁺(r)`, and `r` small enough that
`(n+r)/(n−r) < φ`, then `g₁ = g₂` and `b₁ = b₂`. Hence the product map `G × P → 𝒪_K`,
`(g, p) ↦ g·p` (with `P = n + B⁺(r)`) is injective, giving `|A| = |G|·|P|`.

The unit `u = g₁⁻¹g₂` satisfies `p₁ = u·p₂`, so every archimedean absolute value of `u` is
`w(p₁)/w(p₂) ∈ [(n−r)/(n+r), (n+r)/(n−r)] ⊆ (φ⁻¹, φ)`; by [`unit_separation`] `u = ±1`, and `u = −1`
is excluded since it would force `b₁ + b₂ = −2n`, whence `2n = w(b₁+b₂) ≤ 2r < 2n`. -/
theorem directness {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    {g₁ g₂ : (𝓞 K)ˣ} {b₁ b₂ : 𝓞 K} (hb₁ : b₁ ∈ boxAdd K r) (hb₂ : b₂ ∈ boxAdd K r)
    (heq : (g₁ : 𝓞 K) * ((n : 𝓞 K) + b₁) = (g₂ : 𝓞 K) * ((n : 𝓞 K) + b₂)) :
    g₁ = g₂ ∧ b₁ = b₂ := by
  classical
  have hnr : (0 : ℝ) < (n : ℝ) - r := by linarith
  set u : (𝓞 K)ˣ := g₁⁻¹ * g₂ with hu
  -- `p₁ = u · p₂`.
  have hp : (n : 𝓞 K) + b₁ = (u : 𝓞 K) * ((n : 𝓞 K) + b₂) := by
    apply mul_left_cancel₀ (Units.ne_zero g₁)
    rw [heq]
    rw [← mul_assoc, ← Units.val_mul, hu, mul_inv_cancel_left]
  -- Every place of `u` lies in `(φ⁻¹, φ)`.
  have hu_sep : ∀ w : NumberField.InfinitePlace K,
      goldenRatio⁻¹ < w ((u : 𝓞 K) : K) ∧ w ((u : 𝓞 K) : K) < goldenRatio := by
    intro w
    obtain ⟨hp₁lo, hp₁hi⟩ := place_translate_bound w n hb₁
    obtain ⟨hp₂lo, hp₂hi⟩ := place_translate_bound w n hb₂
    have hp₂pos : 0 < w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := lt_of_lt_of_le hnr hp₂lo
    have hcoe : (((n : 𝓞 K) + b₁ : 𝓞 K) : K)
        = ((u : 𝓞 K) : K) * (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := by
      rw [hp]; push_cast; ring
    have hwu : w ((u : 𝓞 K) : K)
        = w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) / w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) := by
      rw [eq_div_iff hp₂pos.ne', ← map_mul, ← hcoe]
    have hub : (n : ℝ) + r < goldenRatio * ((n : ℝ) - r) := (div_lt_iff₀ hnr).mp hφ
    rw [hwu]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ hp₂pos]
      calc goldenRatio⁻¹ * w (((n : 𝓞 K) + b₂ : 𝓞 K) : K)
          ≤ goldenRatio⁻¹ * ((n : ℝ) + r) :=
            mul_le_mul_of_nonneg_left hp₂hi (le_of_lt (inv_pos.mpr goldenRatio_pos))
        _ < (n : ℝ) - r := by rw [inv_mul_lt_iff₀ goldenRatio_pos]; linarith [hub]
        _ ≤ w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) := hp₁lo
    · rw [div_lt_iff₀ hp₂pos]
      calc w (((n : 𝓞 K) + b₁ : 𝓞 K) : K) ≤ (n : ℝ) + r := hp₁hi
        _ < goldenRatio * ((n : ℝ) - r) := hub
        _ ≤ goldenRatio * w (((n : 𝓞 K) + b₂ : 𝓞 K) : K) :=
            mul_le_mul_of_nonneg_left hp₂lo (le_of_lt goldenRatio_pos)
  rcases unit_separation K u hu_sep with h1 | h1
  · -- `u = 1`: `g₁ = g₂` and `b₁ = b₂`.
    have hgg : g₁⁻¹ * g₂ = 1 := by rw [← hu]; exact h1
    refine ⟨inv_mul_eq_one.mp hgg, ?_⟩
    have hu1 : (u : 𝓞 K) = 1 := by rw [h1]; rfl
    rw [hu1, one_mul] at hp
    exact add_left_cancel hp
  · -- `u = -1`: impossible.
    exfalso
    have hu1 : (u : 𝓞 K) = -1 := by rw [h1]; rfl
    rw [hu1, neg_one_mul] at hp
    have hsum : b₁ + b₂ = -(((n + n : ℕ)) : 𝓞 K) := by push_cast; linear_combination hp
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
    have hb₁' : w₀ (b₁ : K) ≤ r := (mem_boxAdd.mp hb₁) w₀
    have hb₂' : w₀ (b₂ : K) ≤ r := (mem_boxAdd.mp hb₂) w₀
    have hval : w₀ ((b₁ + b₂ : 𝓞 K) : K) = (n : ℝ) + n := by
      have hcoe : ((b₁ + b₂ : 𝓞 K) : K) = -(((n + n : ℕ) : K)) := by rw [hsum]; push_cast; ring
      have hneg : w₀ (-(((n + n : ℕ) : K))) = w₀ (((n + n : ℕ) : K)) := w₀.1.map_neg _
      rw [hcoe, hneg, place_natCast]; push_cast; ring
    have htri : w₀ ((b₁ + b₂ : 𝓞 K) : K) ≤ w₀ (b₁ : K) + w₀ (b₂ : K) := by
      have he : ((b₁ + b₂ : 𝓞 K) : K) = (b₁ : K) + (b₂ : K) := by push_cast; ring
      rw [he]; exact w₀.1.add_le _ _
    rw [hval] at htri
    linarith

/-- Pointwise product bound behind `|A·A| ≤ |G·G|·|P·P|`: for finsets in a commutative monoid,
`|(S·T)²| ≤ |S²|·|T²|` (since `(S·T)·(S·T) = (S·S)·(T·T)`). -/
theorem card_mul_self_le {α : Type*} [CommMonoid α] [DecidableEq α] (S T : Finset α) :
    ((S * T) * (S * T)).card ≤ (S * S).card * (T * T).card := by
  rw [mul_mul_mul_comm]
  exact Finset.card_mul_le

/-- Every element `g·(n + b)` of the construction (with `g ∈ B^×(Y)`, `b ∈ B⁺(r)`) has every
archimedean absolute value `≤ e^Y · (n + r)`: multiplication by a unit in `B^×(Y)` expands each
embedding by at most `e^Y`. This drives the sumset bound `A + A ⊆ B⁺(4Xe^Y)` in Lemma 4.1. -/
theorem place_construction_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (w : NumberField.InfinitePlace K) {Y : ℝ} {g : (𝓞 K)ˣ} (hg : g ∈ boxMult K Y)
    {n : ℕ} {r : ℝ} {b : 𝓞 K} (hb : b ∈ boxAdd K r) :
    w (((g : 𝓞 K) * ((n : 𝓞 K) + b) : 𝓞 K) : K) ≤ Real.exp Y * ((n : ℝ) + r) := by
  have hgpos : 0 < w ((g : 𝓞 K) : K) :=
    NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero g)
  have hgle : w ((g : 𝓞 K) : K) ≤ Real.exp Y := by
    have hlog : Real.log (w ((g : 𝓞 K) : K)) ≤ Y :=
      le_trans (le_abs_self _) ((mem_boxMult.mp hg) w)
    calc w ((g : 𝓞 K) : K) = Real.exp (Real.log (w ((g : 𝓞 K) : K))) := (Real.exp_log hgpos).symm
      _ ≤ Real.exp Y := Real.exp_le_exp.mpr hlog
  have hble : w (((n : 𝓞 K) + b : 𝓞 K) : K) ≤ (n : ℝ) + r := (place_translate_bound w n hb).2
  have hcoe : (((g : 𝓞 K) * ((n : 𝓞 K) + b) : 𝓞 K) : K)
      = ((g : 𝓞 K) : K) * (((n : 𝓞 K) + b : 𝓞 K) : K) := by push_cast; ring
  rw [hcoe, map_mul]
  exact mul_le_mul hgle hble (apply_nonneg w _) (Real.exp_pos Y).le

open scoped Classical in
open Real in
/-- The construction `A = G·(n + B)` has exactly `|G|·|B|` elements, when `B ⊆ B⁺(r)` and `r` is
small enough (`(n+r)/(n−r) < φ`). This is the cardinality payoff of [`directness`]: the product
map `(g, b) ↦ g·(n + b)` is injective on `G ×ˢ B`. -/
theorem card_construction {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {n : ℕ} {r : ℝ} (hrn : r < (n : ℝ))
    (hφ : ((n : ℝ) + r) / ((n : ℝ) - r) < goldenRatio)
    (G : Finset (𝓞 K)ˣ) (B : Finset (𝓞 K)) (hB : ∀ b ∈ B, b ∈ boxAdd K r) :
    ((G ×ˢ B).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2))).card
      = G.card * B.card := by
  have hinj : Set.InjOn
      (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2)) ↑(G ×ˢ B) := by
    rintro ⟨g₁, b₁⟩ hmem₁ ⟨g₂, b₂⟩ hmem₂ heq
    simp only [Finset.mem_coe, Finset.mem_product] at hmem₁ hmem₂
    obtain ⟨hg, hb⟩ := directness hrn hφ (hB b₁ hmem₁.2) (hB b₂ hmem₂.2) heq
    exact Prod.ext hg hb
  rw [Finset.card_image_of_injOn hinj, Finset.card_product]

open scoped Classical in
/-- The Lemma 4.1 construction `A = B^×(Y)·(⌊X⌋ + B⁺(εX))` has exactly `|B^×(Y)|·|B⁺(εX)|`
elements, for `X ≥ 2` and `0 < ε ≤ 3/20` (instantiating [`card_construction`] via the floor-ratio
bound). -/
theorem card_construction_floor (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (Y : ℝ) {X ε : ℝ} (hX : 2 ≤ X) (hε0 : 0 < ε) (hε : ε ≤ 3 / 20) :
    ((boxMult K Y ×ˢ boxAdd K (ε * X)).image
        (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((⌊X⌋₊ : 𝓞 K) + gb.2))).card
      = (boxMult K Y).card * (boxAdd K (ε * X)).card := by
  refine card_construction (r := ε * X) ?_ (floor_ratio_lt_goldenRatio hX hε0 hε)
    (boxMult K Y) (boxAdd K (ε * X)) (fun b hb => hb)
  have hn2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ X by exact_mod_cast hX)
  have hXlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  nlinarith [mul_le_mul_of_nonneg_right hε (show (0 : ℝ) ≤ X by linarith), hXlt, hn2]

/-- `√d ≤ 15^d`. -/
private lemma sqrt_le_fifteen_pow {d : ℕ} : Real.sqrt (d : ℝ) ≤ 15 ^ d := by
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have h1 : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (two_ne_zero) d
    have h := Real.sqrt_le_sqrt hdd
    rwa [Real.sqrt_sq hdnn] at h
  have h2 : (d : ℝ) ≤ 15 ^ d := by
    calc (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
      _ ≤ 15 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  linarith

/-- Arithmetic behind the **lower** bound on `|A|` in Lemma 4.1 (with `c = 1/100`, `ε = 3/20`):
the target is dominated by the product of the two count lower bounds. -/
private lemma aux_L1 {X Y D : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ Y) {d : ℕ} (hd : 1 ≤ d) (hD : 1 ≤ D) :
    ((1 : ℝ) / 100 * X * Y) ^ d / (Y * D ^ ((3 : ℝ) / 2))
      ≤ Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) * (((3 : ℝ) / 20 * X) ^ d / Real.sqrt D) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hsD : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hDsD : D * Real.sqrt D = D ^ ((3 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hD0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  -- reduced inequality (denominators `D^{3/2}=D√D` cancel)
  have hred : ((1 : ℝ) / 100 * X * Y) ^ d / Y
      ≤ Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d / Real.sqrt (d : ℝ) := by
    rw [div_le_div_iff₀ hY0 hsd]
    have hrhs : Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d * Y
        = 15 ^ d * ((1 : ℝ) / 100 * X * Y) ^ d := by
      rw [show Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d * Y
          = (Y ^ (d - 1) * Y) * ((3 : ℝ) / 20 * X) ^ d by ring, ← pow_succ, Nat.sub_add_cancel hd,
        ← mul_pow, ← mul_pow]
      congr 1
      ring
    rw [hrhs]
    nlinarith [sqrt_le_fifteen_pow (d := d), pow_pos (show (0:ℝ) < 1/100*X*Y by positivity) d]
  calc ((1 : ℝ) / 100 * X * Y) ^ d / (Y * D ^ ((3 : ℝ) / 2))
      = (((1 : ℝ) / 100 * X * Y) ^ d / Y) / (D * Real.sqrt D) := by rw [hDsD]; ring
    _ ≤ (Y ^ (d - 1) * ((3 : ℝ) / 20 * X) ^ d / Real.sqrt (d : ℝ)) / (D * Real.sqrt D) :=
        (div_le_div_iff_of_pos_right (mul_pos hD0 hsD)).mpr hred
    _ = Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) * (((3 : ℝ) / 20 * X) ^ d / Real.sqrt D) := by
        rw [div_mul_div_comm, div_div, mul_assoc]

/-- Arithmetic behind the **upper** bound on `|A|` in Lemma 4.1: the product of the two count
upper bounds is dominated by `(XY/c)^d`. -/
private lemma aux_L2 {X Y : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ Y) {d : ℕ} (hd : 2 ≤ d) :
    10 * (5 * Y + 1) ^ (d - 1) * (2 * ((3 : ℝ) / 20 * X) + 1) ^ d
      ≤ (X * Y / (1 / 100)) ^ d := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hd1 : 1 ≤ d := by omega
  have h1 : (5 * Y + 1) ^ (d - 1) ≤ (6 * Y) ^ d :=
    calc (5 * Y + 1) ^ (d - 1) ≤ (6 * Y) ^ (d - 1) := by gcongr; linarith
      _ ≤ (6 * Y) ^ d := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : (2 * ((3 : ℝ) / 20 * X) + 1) ^ d ≤ X ^ d := by
    apply pow_le_pow_left₀ (by positivity); nlinarith
  have hpow : (10 : ℝ) * 6 ^ d ≤ 100 ^ d := by
    have h10 : (10 : ℝ) ≤ (100 / 6) ^ d :=
      le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) hd)
    have h100 : (100 : ℝ) ^ d = (100 / 6) ^ d * 6 ^ d := by rw [← mul_pow]; norm_num
    nlinarith [h10, pow_pos (show (0 : ℝ) < 6 by norm_num) d]
  have hXYpos : (0 : ℝ) ≤ (X * Y) ^ d := by positivity
  calc 10 * (5 * Y + 1) ^ (d - 1) * (2 * ((3 : ℝ) / 20 * X) + 1) ^ d
      ≤ 10 * (6 * Y) ^ d * X ^ d := by gcongr
    _ = 10 * 6 ^ d * (X * Y) ^ d := by rw [mul_pow, mul_pow]; ring
    _ ≤ 100 ^ d * (X * Y) ^ d := by nlinarith [hpow, hXYpos]
    _ = (X * Y / (1 / 100)) ^ d := by rw [← mul_pow]; ring_nf

/-- Arithmetic behind the **product-set** bound in Lemma 4.1 (reduced form, with `c = 1/100`):
`10 d (10Y+1)^{d-1} ≤ 100^d Y^{d-1}`. -/
private lemma aux_L3 {Y : ℝ} (hY : 2 ≤ Y) {d : ℕ} (hd : 2 ≤ d) :
    10 * (d : ℝ) * (10 * Y + 1) ^ (d - 1) ≤ 100 ^ d * Y ^ (d - 1) := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hd2d : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
  have hcore : (10 : ℝ) * 2 ^ d * 11 ^ (d - 1) ≤ 100 ^ d := by
    have h22 : (22 : ℝ) ^ d = 2 ^ d * 11 ^ d := by rw [← mul_pow]; norm_num
    have h11 : (11 : ℝ) ^ d = 11 * 11 ^ (d - 1) := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
    have e : (10 : ℝ) * 2 ^ d * 11 ^ (d - 1) = 10 / 11 * 22 ^ d := by rw [h22, h11]; ring
    rw [e]
    calc (10 : ℝ) / 11 * 22 ^ d ≤ 1 * 22 ^ d := by gcongr; norm_num
      _ = 22 ^ d := one_mul _
      _ ≤ 100 ^ d := by gcongr; norm_num
  calc 10 * (d : ℝ) * (10 * Y + 1) ^ (d - 1)
      ≤ 10 * 2 ^ d * (11 * Y) ^ (d - 1) := by gcongr; first | exact hd2d | linarith
    _ = 10 * 2 ^ d * 11 ^ (d - 1) * Y ^ (d - 1) := by rw [mul_pow]; ring
    _ ≤ 100 ^ d * Y ^ (d - 1) := by gcongr

/-- Arithmetic behind the **sumset** bound in Lemma 4.1: `8Xe^Y + 1 ≤ e^Y·εX/c`. -/
private lemma aux_L4 {X Y : ℝ} (hX : 2 ≤ X) (hY : 0 ≤ Y) :
    8 * X * Real.exp Y + 1 ≤ Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) := by
  have he : (1 : ℝ) ≤ Real.exp Y := Real.one_le_exp hY
  have hXe : (1 : ℝ) ≤ X * Real.exp Y := by nlinarith
  rw [show Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) = 15 * X * Real.exp Y by ring]
  nlinarith [hXe]

open scoped Classical in
open Real in
/-- **Lemma 4.1** (the construction), as stated in §4 of the paper.

There is an absolute constant `c > 0` such that for every totally real number field `K` of degree
`d ≥ 2` and all `X, Y ≥ 2`, there is a finite set `A ⊆ 𝒪_K` with
* `(cXY)^d / (Y · Δ_K^{3/2}) ≤ |A| ≤ (XY/c)^d`,
* `|A·A| ≤ c^{-d} Y^{1-d} Δ_K² |A|²`, and
* `|A + A| ≤ (e^Y/c)^d Δ_K^{1/2} |A|`,

where `Δ_K = |discr K|`.  (Here `A := G·P` with `G = B^×(Y)` a box in the unit lattice and
`P = X + B⁺(εX)` a box in the additive lattice; see §3–§4.) -/
theorem lemma_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (d : ℕ), Module.finrank ℚ K = d → 2 ≤ d → ∀ X Y : ℝ, 2 ≤ X → 2 ≤ Y →
      ∃ A : Finset (𝓞 K),
        (c * X * Y) ^ d / (Y * |(NumberField.discr K : ℝ)| ^ ((3 : ℝ) / 2)) ≤ (A.card : ℝ) ∧
        (A.card : ℝ) ≤ (X * Y / c) ^ d ∧
        ((A * A).card : ℝ) ≤
          c ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * |(NumberField.discr K : ℝ)| ^ 2 * (A.card : ℝ) ^ 2 ∧
        ((A + A).card : ℝ) ≤
          (Real.exp Y / c) ^ d * |(NumberField.discr K : ℝ)| ^ ((1 : ℝ) / 2) * (A.card : ℝ) := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro K _ _ _ d hd hd2 X Y hX hY
  classical
  have hd1 : 1 ≤ d := by omega
  set D : ℝ := |(NumberField.discr K : ℝ)| with hDdef
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hD0 : (0 : ℝ) < D := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hsqrtd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hsqrtD : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hRpos : (0 : ℝ) < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
  have hReg : NumberField.Units.regulator K ≤ D := by
    rw [hDdef]; exact regulator_le_discr K (by rw [hd]; exact hd2)
  obtain ⟨hGlo, hGhi⟩ := lattice_count_mult K d hd Y hY1
  obtain ⟨_, hGGhi⟩ := lattice_count_mult K d hd (2 * Y) (by linarith)
  obtain ⟨hBlo, hBhi⟩ := lattice_count_add K d hd (3 / 20 * X) (by positivity)
  set n : ℕ := ⌊X⌋₊ with hndef
  set Gc : Finset (𝓞 K) := (boxMult K Y).image (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) with hGcdef
  set P : Finset (𝓞 K) := (boxAdd K (3 / 20 * X)).image (fun b => (n : 𝓞 K) + b) with hPdef
  have hPcard : P.card = (boxAdd K (3 / 20 * X)).card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hGcard1 : (1 : ℝ) ≤ ((boxMult K Y).card : ℝ) := by
    have h1 : (1 : (𝓞 K)ˣ) ∈ boxMult K Y := by
      rw [mem_boxMult]; intro w
      simp only [Units.val_one, map_one, Real.log_one, abs_zero]; linarith
    exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  have hAeq : Gc * P = (boxMult K Y ×ˢ boxAdd K (3 / 20 * X)).image
      (fun gb : (𝓞 K)ˣ × 𝓞 K => (gb.1 : 𝓞 K) * ((n : 𝓞 K) + gb.2)) := by
    rw [hGcdef, hPdef]; ext x
    constructor
    · intro hx
      obtain ⟨a, ha, e, he, rfl⟩ := Finset.mem_mul.mp hx
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨(g, w), Finset.mem_product.mpr ⟨hg, hw⟩, rfl⟩
    · intro hx
      obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mul_mem_mul
        (Finset.mem_image_of_mem (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) (Finset.mem_product.mp hpr).1)
        (Finset.mem_image_of_mem (fun b => (n : 𝓞 K) + b) (Finset.mem_product.mp hpr).2)
  have hAcard : (Gc * P).card = (boxMult K Y).card * (boxAdd K (3 / 20 * X)).card := by
    rw [hAeq]; exact card_construction_floor K Y hX (by norm_num) (le_refl _)
  have hGlo' : Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D) ≤ ((boxMult K Y).card : ℝ) := by
    refine le_trans ?_ hGlo; gcongr
  refine ⟨Gc * P, ?_, ?_, ?_, ?_⟩
  · rw [hAcard]; push_cast
    refine le_trans (aux_L1 hX hY hd1 hD1) ?_
    exact mul_le_mul hGlo' hBlo (by positivity) (Nat.cast_nonneg _)
  · rw [hAcard]; push_cast
    refine le_trans ?_ (aux_L2 hX hY hd2)
    exact mul_le_mul hGhi hBhi (Nat.cast_nonneg _) (by positivity)
  · have hGGsub : Gc * Gc ⊆ (boxMult K (2 * Y)).image (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) := by
      intro z hz
      rw [hGcdef] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hz
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hb
      have hggmem : g * g' ∈ boxMult K (2 * Y) := by
        have := boxMult_mul hg hg'; rwa [show Y + Y = 2 * Y by ring] at this
      rw [show (g : 𝓞 K) * (g' : 𝓞 K) = ((g * g' : (𝓞 K)ˣ) : 𝓞 K) from (Units.val_mul g g').symm]
      exact Finset.mem_image_of_mem (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) hggmem
    have hAA : (((Gc * P) * (Gc * P)).card : ℝ)
        ≤ 10 * (10 * Y + 1) ^ (d - 1) * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 := by
      have h1 := card_mul_self_le Gc P
      have h2 : (Gc * Gc).card ≤ (boxMult K (2 * Y)).card :=
        le_trans (Finset.card_le_card hGGsub) Finset.card_image_le
      have h3 : (P * P).card ≤ (boxAdd K (3 / 20 * X)).card ^ 2 := by
        calc (P * P).card ≤ P.card * P.card := Finset.card_mul_le
          _ = (boxAdd K (3 / 20 * X)).card ^ 2 := by rw [hPcard]; ring
      have hGG : ((Gc * Gc).card : ℝ) ≤ 10 * (10 * Y + 1) ^ (d - 1) := by
        have h2' : ((Gc * Gc).card : ℝ) ≤ ((boxMult K (2 * Y)).card : ℝ) := by exact_mod_cast h2
        refine le_trans h2' ?_
        rw [show (10 : ℝ) * Y + 1 = 5 * (2 * Y) + 1 by ring]; exact hGGhi
      calc (((Gc * P) * (Gc * P)).card : ℝ)
          ≤ ((Gc * Gc).card : ℝ) * ((P * P).card : ℝ) := by exact_mod_cast h1
        _ ≤ 10 * (10 * Y + 1) ^ (d - 1) * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 := by
            gcongr; exact_mod_cast h3
    refine le_trans hAA ?_
    rw [hAcard]; push_cast
    rw [show ((1 : ℝ) / 100) ^ (-(d : ℤ)) = 100 ^ d by
          rw [zpow_neg, zpow_natCast, one_div, inv_pow, inv_inv],
       show Y ^ (1 - (d : ℤ)) = Y * (Y ^ d)⁻¹ by
          rw [show (1 : ℤ) - (d : ℤ) = 1 + (-(d : ℤ)) by ring, zpow_add₀ hY0.ne', zpow_one,
            zpow_neg, zpow_natCast]]
    have hYpow : (Y : ℝ) ^ d = Y ^ (d - 1) * Y := by rw [← pow_succ, Nat.sub_add_cancel hd1]
    have heq : (100 : ℝ) ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 *
        (Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D)) ^ 2 = 100 ^ d * Y ^ (d - 1) / (d : ℝ) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hdpos.le, hYpow]
      field_simp
    have hcardsq : (Y ^ (d - 1) / (Real.sqrt (d : ℝ) * D)) ^ 2 ≤ ((boxMult K Y).card : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hGlo' 2
    have hcoeff : 10 * (10 * Y + 1) ^ (d - 1)
        ≤ 100 ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 * ((boxMult K Y).card : ℝ) ^ 2 := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hcardsq (by positivity))
      rw [heq, le_div_iff₀ hdpos]
      nlinarith [aux_L3 hY hd2]
    rw [mul_pow,
      show (100 : ℝ) ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 *
          (((boxMult K Y).card : ℝ) ^ 2 * ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2)
        = (100 ^ d * (Y * (Y ^ d)⁻¹) * D ^ 2 * ((boxMult K Y).card : ℝ) ^ 2) *
          ((boxAdd K (3 / 20 * X)).card : ℝ) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · have hAAsub : (Gc * P) + (Gc * P) ⊆ boxAdd K (4 * X * Real.exp Y) := by
      have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0.le
      have hsub : ∀ z ∈ Gc * P, z ∈ boxAdd K (Real.exp Y * ((n : ℝ) + 3 / 20 * X)) := by
        intro z hz
        rw [hGcdef, hPdef] at hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hz
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
        rw [mem_boxAdd]; intro w; exact place_construction_le w hg hc
      intro x hx
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Finset.mem_add.mp hx
      have h12 := boxAdd_add (hsub a₁ ha₁) (hsub a₂ ha₂)
      rw [mem_boxAdd] at h12 ⊢
      intro w
      refine le_trans (h12 w) ?_
      have he : (0 : ℝ) < Real.exp Y := Real.exp_pos Y
      nlinarith [hnX, he, hX0, mul_le_mul_of_nonneg_left hnX he.le]
    have hcard : (((Gc * P) + (Gc * P)).card : ℝ) ≤ (2 * (4 * X * Real.exp Y) + 1) ^ d :=
      le_trans (by exact_mod_cast Finset.card_le_card hAAsub)
        (lattice_count_add K d hd (4 * X * Real.exp Y) (by positivity)).2
    refine le_trans hcard ?_
    rw [hAcard, show D ^ ((1 : ℝ) / 2) = Real.sqrt D from (Real.sqrt_eq_rpow D).symm]
    push_cast
    have hcardGB : (3 / 20 * X) ^ d / Real.sqrt D
        ≤ ((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ) := by
      calc (3 / 20 * X) ^ d / Real.sqrt D ≤ ((boxAdd K (3 / 20 * X)).card : ℝ) := hBlo
        _ = 1 * ((boxAdd K (3 / 20 * X)).card : ℝ) := (one_mul _).symm
        _ ≤ ((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ) := by
            gcongr
    have hDcardA : (3 / 20 * X) ^ d
        ≤ Real.sqrt D * (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ)) := by
      rw [mul_comm (Real.sqrt D)]; exact (div_le_iff₀ hsqrtD).mp hcardGB
    calc (2 * (4 * X * Real.exp Y) + 1) ^ d
        ≤ (Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100)) ^ d := by
          apply pow_le_pow_left₀ (by positivity)
          have := aux_L4 hX hY0.le; linarith [this]
      _ = (Real.exp Y / (1 / 100)) ^ d * (3 / 20 * X) ^ d := by
          rw [← mul_pow, show Real.exp Y / (1 / 100) * (3 / 20 * X)
            = Real.exp Y * ((3 : ℝ) / 20 * X) / (1 / 100) by ring]
      _ ≤ (Real.exp Y / (1 / 100)) ^ d *
            (Real.sqrt D * (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ))) := by
          gcongr
      _ = (Real.exp Y / (1 / 100)) ^ d * Real.sqrt D *
            (((boxMult K Y).card : ℝ) * ((boxAdd K (3 / 20 * X)).card : ℝ)) := by ring

/-- `(b^m)^t = (b^t)^m` for `b ≥ 0`, mixing a natural power and a real power. -/
private lemma rpow_natpow_comm {b : ℝ} (hb : 0 ≤ b) (t : ℝ) (m : ℕ) :
    (b ^ m) ^ t = (b ^ t) ^ m := by
  rw [← Real.rpow_natCast_mul hb, mul_comm, Real.rpow_mul_natCast hb]

/-- A totally real number field admits an injective ring embedding of its ring of integers `𝒪_K`
into `ℝ` (the restriction of any real infinite place). -/
private lemma exists_real_embedding (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : ∃ f : 𝓞 K →+* ℝ, Function.Injective f := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
  exact ⟨(NumberField.InfinitePlace.embedding_of_isReal hw).comp (algebraMap (𝓞 K) K),
    (NumberField.InfinitePlace.embedding_of_isReal hw).injective.comp
      NumberField.RingOfIntegers.coe_injective⟩

/-- **Theorem 1.2** (the general construction), in its real-embedded form.

There is an absolute constant `C > 0` such that, for infinitely many `d`, there is a totally real
number field `K` of degree `d`; choosing a real embedding `K ↪ ℝ` and applying the construction of
§4 with parameter `X ≥ 1`, the image `A ⊆ ℝ` of the constructed set `A ⊆ 𝒪_K` satisfies
`X^d ≤ |A| ≤ (CX)^d`, `|A + A| ≤ C^d |A|`, and `|A·A| ≤ |A|² / 2^d`.

Since a ring homomorphism out of a field is injective, the real embedding preserves the
cardinalities of `A`, `A + A` and `A · A`, so the bounds transfer verbatim from `𝒪_K` to `ℝ`.

In the paper this is Theorem 1.2 (with `A ⊆ 𝒪_K`); its proof combines the construction Lemma 4.1
with the field supplied by the explicit Martinet-towers hypothesis. -/
theorem theorem_1_2 (hMartinet : MartinetTotallyRealTowers) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧ 2 ≤ d ∧ ∀ X : ℝ, 1 ≤ X →
      ∃ A : Finset ℝ,
        X ^ d ≤ (A.card : ℝ) ∧ (A.card : ℝ) ≤ (C * X) ^ d ∧
        ((A + A).card : ℝ) ≤ C ^ d * (A.card : ℝ) ∧
        ((A * A).card : ℝ) ≤ (A.card : ℝ) ^ 2 / 2 ^ d := by
  classical
  obtain ⟨c₁, hc₁, L⟩ := lemma_4_1
  change ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d at hMartinet
  obtain ⟨C, hC, T⟩ := hMartinet
  -- Work with `Cd = max C 1 ≥ 1` as the discriminant base, `Y = max (4 Cd²/c₁) 2 ≥ 2` constant.
  set Cd : ℝ := max C 1 with hCddef
  have hCd1 : 1 ≤ Cd := le_max_right _ _
  have hCd0 : 0 < Cd := lt_of_lt_of_le one_pos hCd1
  have hCCd : C ≤ Cd := le_max_left _ _
  set Y : ℝ := max (4 * Cd ^ 2 / c₁) 2 with hYdef
  have hY2 : 2 ≤ Y := le_max_right _ _
  have hY0 : 0 < Y := lt_of_lt_of_le two_pos hY2
  have hYbig : 4 * Cd ^ 2 / c₁ ≤ Y := le_max_left _ _
  -- The output constant.
  set Cout : ℝ := max (3 * Y / c₁) ((Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2)) with hCoutdef
  have hCout0 : 0 < Cout :=
    lt_of_lt_of_le (show (0 : ℝ) < 3 * Y / c₁ by positivity) (le_max_left _ _)
  refine ⟨Cout, hCout0, fun N => ?_⟩
  obtain ⟨d₀, hd₀⟩ := pow_unbounded_of_one_lt Y one_lt_two
  obtain ⟨d, hdge, K, iF, iNF, iTR, hdeg, hdiscr⟩ := T (max (max N d₀) 2)
  letI := iF; letI := iNF; letI := iTR
  have hdN : N ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdge
  have hdd0 : d₀ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdge
  have hd2 : 2 ≤ d := le_trans (le_max_right _ _) hdge
  have hY2d : Y < (2 : ℝ) ^ d := lt_of_lt_of_le hd₀ (pow_le_pow_right₀ one_le_two hdd0)
  refine ⟨d, hdN, hd2, fun X hX1 => ?_⟩
  set Xt : ℝ := max X 2 with hXtdef
  have hXt2 : 2 ≤ Xt := le_max_right _ _
  have hXt0 : 0 < Xt := lt_of_lt_of_le two_pos hXt2
  obtain ⟨A, hAlow, hAhigh, hAmul, hAadd⟩ := L K d hdeg hd2 Xt Y hXt2 hY2
  obtain ⟨f, hf⟩ := exists_real_embedding K
  set A' : Finset ℝ := A.image f with hA'def
  have hcard : A'.card = A.card := by rw [hA'def]; exact Finset.card_image_of_injective A hf
  have hcardadd : (A' + A').card = (A + A).card := by
    rw [hA'def, ← Finset.image_add]; exact Finset.card_image_of_injective _ hf
  have hcardmul : (A' * A').card = (A * A).card := by
    rw [hA'def, ← Finset.image_mul]; exact Finset.card_image_of_injective _ hf
  set D : ℝ := |(NumberField.discr K : ℝ)| with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, abs_pos]
    exact Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hD0 : 0 ≤ D := hDpos.le
  have hDCd : D ≤ Cd ^ d := le_trans hdiscr (pow_le_pow_left₀ hC.le hCCd d)
  -- `4 Cd² ≤ c₁ Y`, the master inequality behind all the constant choices.
  have hc1Y : 4 * Cd ^ 2 ≤ c₁ * Y := by
    rw [mul_comm c₁ Y]; exact (div_le_iff₀ hc₁).mp hYbig
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · -- `X^d ≤ |A'|`
    rw [hcard]
    -- `D^{3/2} ≤ (Cd^{3/2})^d`
    have hE : D ^ ((3 : ℝ) / 2) ≤ (Cd ^ ((3 : ℝ) / 2)) ^ d := by
      rw [← rpow_natpow_comm hCd0.le]; exact Real.rpow_le_rpow hD0 hDCd (by norm_num)
    -- `Cd^{3/2} ≤ Cd²`, hence `2 Cd^{3/2} ≤ c₁ Y`.
    have hCd32 : Cd ^ ((3 : ℝ) / 2) ≤ Cd ^ 2 := by
      have h2 : (Cd : ℝ) ^ 2 = Cd ^ (2 : ℝ) := by rw [← Real.rpow_natCast Cd 2]; norm_num
      rw [h2]; exact Real.rpow_le_rpow_of_exponent_le hCd1 (by norm_num)
    have hbound : 2 * Cd ^ ((3 : ℝ) / 2) ≤ c₁ * Y := by nlinarith [sq_nonneg Cd, hCd32, hc1Y]
    -- `Y · D^{3/2} ≤ (c₁ Y)^d`
    have hYD : Y * D ^ ((3 : ℝ) / 2) ≤ (c₁ * Y) ^ d := by
      calc Y * D ^ ((3 : ℝ) / 2)
          ≤ Y * (Cd ^ ((3 : ℝ) / 2)) ^ d := by
            exact mul_le_mul_of_nonneg_left hE hY0.le
        _ ≤ (2 : ℝ) ^ d * (Cd ^ ((3 : ℝ) / 2)) ^ d :=
            mul_le_mul_of_nonneg_right hY2d.le (by positivity)
        _ = (2 * Cd ^ ((3 : ℝ) / 2)) ^ d := by rw [← mul_pow]
        _ ≤ (c₁ * Y) ^ d := pow_le_pow_left₀ (by positivity) hbound d
    have hden : 0 < Y * D ^ ((3 : ℝ) / 2) := by positivity
    -- `Xt^d ≤ |A|`, then `X^d ≤ Xt^d ≤ |A|`.
    have hXtlow : Xt ^ d ≤ (A.card : ℝ) := by
      refine le_trans ?_ hAlow
      rw [le_div_iff₀ hden, show c₁ * Xt * Y = Xt * (c₁ * Y) by ring, mul_pow]
      exact mul_le_mul_of_nonneg_left hYD (by positivity)
    exact le_trans (pow_le_pow_left₀ (by linarith) (le_max_left X 2) d) hXtlow
  · -- `|A'| ≤ (Cout X)^d`
    rw [hcard]
    have hXt3 : Xt ≤ 3 * X := by rw [hXtdef]; exact max_le (by linarith) (by linarith)
    have h3Y : 3 * Y / c₁ ≤ Cout := by rw [hCoutdef]; exact le_max_left _ _
    have hstep : Xt * Y / c₁ ≤ Cout * X := by
      calc Xt * Y / c₁ = (Y / c₁) * Xt := by ring
        _ ≤ (Y / c₁) * (3 * X) := by
            exact mul_le_mul_of_nonneg_left hXt3 (by positivity)
        _ = (3 * Y / c₁) * X := by ring
        _ ≤ Cout * X := mul_le_mul_of_nonneg_right h3Y (by linarith)
    exact le_trans hAhigh (pow_le_pow_left₀ (by positivity) hstep d)
  · -- `|A' + A'| ≤ Cout^d |A'|`
    rw [hcardadd, hcard]
    have hE2 : D ^ ((1 : ℝ) / 2) ≤ (Cd ^ ((1 : ℝ) / 2)) ^ d := by
      rw [← rpow_natpow_comm hCd0.le]; exact Real.rpow_le_rpow hD0 hDCd (by norm_num)
    have hfac : (Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2) ≤ Cout := by
      rw [hCoutdef]; exact le_max_right _ _
    have hcombine : (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2) ≤ Cout ^ d := by
      calc (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2)
          ≤ (Real.exp Y / c₁) ^ d * (Cd ^ ((1 : ℝ) / 2)) ^ d := by
            exact mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = ((Real.exp Y / c₁) * Cd ^ ((1 : ℝ) / 2)) ^ d := by rw [← mul_pow]
        _ ≤ Cout ^ d := pow_le_pow_left₀ (by positivity) hfac d
    calc (↑(A + A).card : ℝ)
        ≤ (Real.exp Y / c₁) ^ d * D ^ ((1 : ℝ) / 2) * (A.card : ℝ) := hAadd
      _ ≤ Cout ^ d * (A.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcombine (by positivity)
  · -- `|A' · A'| ≤ |A'|² / 2^d`
    rw [hcardmul, hcard]
    have hD2 : D ^ 2 ≤ (Cd ^ 2) ^ d := by
      calc D ^ 2 ≤ (Cd ^ d) ^ 2 := pow_le_pow_left₀ hD0 hDCd 2
        _ = (Cd ^ 2) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
    have hKey2 : D ^ 2 * Y * (2 : ℝ) ^ d ≤ (c₁ * Y) ^ d := by
      calc D ^ 2 * Y * (2 : ℝ) ^ d
          ≤ (Cd ^ 2) ^ d * (2 : ℝ) ^ d * (2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hD2 hY2d.le hY0.le (by positivity)) (by positivity)
        _ = (4 * Cd ^ 2) ^ d := by rw [mul_assoc, ← mul_pow, ← mul_pow]; congr 1; ring
        _ ≤ (c₁ * Y) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    have hzc : c₁ ^ (-(d : ℤ)) = (c₁ ^ d)⁻¹ := by rw [zpow_neg, zpow_natCast]
    have hzy : Y ^ (1 - (d : ℤ)) = Y * (Y ^ d)⁻¹ := by
      rw [show (1 : ℤ) - (d : ℤ) = 1 + (-(d : ℤ)) by ring, zpow_add₀ hY0.ne', zpow_one, zpow_neg,
        zpow_natCast]
    have hcoef : c₁ ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * D ^ 2 ≤ ((2 : ℝ) ^ d)⁻¹ := by
      rw [hzc, hzy,
        show (c₁ ^ d)⁻¹ * (Y * (Y ^ d)⁻¹) * D ^ 2 = D ^ 2 * Y / (c₁ ^ d * Y ^ d) by
          field_simp,
        div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity), ← mul_pow]
      exact hKey2
    calc (↑(A * A).card : ℝ)
        ≤ c₁ ^ (-(d : ℤ)) * Y ^ (1 - (d : ℤ)) * D ^ 2 * (A.card : ℝ) ^ 2 := hAmul
      _ ≤ ((2 : ℝ) ^ d)⁻¹ * (A.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = (A.card : ℝ) ^ 2 / 2 ^ d := by rw [div_eq_mul_inv, mul_comm]

/-- Additive estimate of the reduction: with `c ≤ 1/2` and a lower bound `B^(2d) ≤ n`, the sumset
bound `C^d·n` is dominated by `n^(2-c)` (here packaged as `B^d · n ≤ n^(2-c)`). -/
private lemma aux_add {B n c : ℝ} {d : ℕ} (hB1 : 1 ≤ B)
    (hc12 : c ≤ 1 / 2) (hn : B ^ (2 * d) ≤ n) :
    B ^ d * n ≤ n ^ (2 - c) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hbig : (1 : ℝ) ≤ B ^ (2 * d) := one_le_pow₀ hB1
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one (le_trans hbig hn)
  have hc1 : (0 : ℝ) ≤ 1 - c := by linarith
  have key : B ^ d ≤ n ^ (1 - c) := by
    have h1 : (B ^ (2 * d) : ℝ) ^ (1 - c) ≤ n ^ (1 - c) :=
      Real.rpow_le_rpow (pow_nonneg hB0 _) hn hc1
    rw [← Real.rpow_natCast B d]
    refine le_trans ?_ h1
    rw [← Real.rpow_natCast B (2 * d), ← Real.rpow_mul hB0]
    refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ 1 - 2 * c)]
  have hsplit : n ^ (2 - c) = n ^ (1 - c) * n := by
    rw [show (2 : ℝ) - c = (1 - c) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right key hn0.le

/-- Multiplicative estimate of the reduction: with `c·(3 log B) ≤ log 2` and an upper bound
`n ≤ B^(3d)`, the product-set bound `n²/2^d` is dominated by `n^(2-c)`. -/
private lemma aux_mul {B n c : ℝ} {d : ℕ} (hB1 : 1 ≤ B)
    (hc0 : 0 ≤ c) (hlog : c * (3 * Real.log B) ≤ Real.log 2)
    (hn : n ≤ B ^ (3 * d)) (hn1 : 1 ≤ n) :
    n ^ 2 / 2 ^ d ≤ n ^ (2 - c) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hB3c : B ^ (3 * c) ≤ 2 := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
      Real.rpow_def_of_pos hBpos]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hlog]
  have key : n ^ c ≤ (2 : ℝ) ^ d := by
    have h1 : n ^ c ≤ (B ^ (3 * d) : ℝ) ^ c := Real.rpow_le_rpow hn0.le hn hc0
    refine le_trans h1 ?_
    rw [← Real.rpow_natCast B (3 * d), ← Real.rpow_mul hB0,
      show ((3 * d : ℕ) : ℝ) * c = (3 * c) * (d : ℝ) by push_cast; ring,
      Real.rpow_mul hB0, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hB0 _) hB3c d
  have hsplit : n ^ (2 - c) = n ^ 2 / n ^ c := by
    rw [Real.rpow_sub hn0, ← Real.rpow_natCast n 2]
    norm_num
  rw [hsplit]
  gcongr

/-- **Theorem 1.1** (the sum-product conjecture is false over `ℝ`).

There is an absolute constant `c > 0` such that there are arbitrarily large finite sets
`A ⊆ ℝ` with `max(|A + A|, |A·A|) ≤ |A|^(2 - c)`.

"Arbitrarily large" is expressed as: for every `N` there is such an `A` with `|A| ≥ N`.
The single non-Mathlib mathematical input is supplied by the explicit hypothesis
`hMartinet : MartinetTotallyRealTowers`. -/
theorem sumProduct_false (hMartinet : MartinetTotallyRealTowers) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℝ, N ≤ A.card ∧
      ((max (A + A).card (A * A).card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (2 - c) := by
  obtain ⟨C₀, hC₀, H⟩ := theorem_1_2 hMartinet
  -- Enlarge the constant so that `B ≥ 2`; all the upper bounds are monotone in the constant.
  set B : ℝ := max C₀ 2 with hBdef
  have hB2 : 2 ≤ B := le_max_right _ _
  have hC₀B : C₀ ≤ B := le_max_left _ _
  have hB1 : 1 ≤ B := le_trans one_le_two hB2
  have hBpos : 0 < B := lt_of_lt_of_le two_pos hB2
  have hlogB : 0 < Real.log B := Real.log_pos (lt_of_lt_of_le one_lt_two hB2)
  -- The exponent saving.
  set c : ℝ := min (1 / 2) (Real.log 2 / (3 * Real.log B)) with hcdef
  have hc0 : 0 < c := by
    refine lt_min (by norm_num) ?_
    exact div_pos (Real.log_pos (by norm_num)) (by linarith)
  have hc12 : c ≤ 1 / 2 := min_le_left _ _
  -- `c · (3 log B) ≤ log 2`, from `c ≤ log 2 / (3 log B)`.
  have hlogc : c * (3 * Real.log B) ≤ Real.log 2 := by
    have hcr : c ≤ Real.log 2 / (3 * Real.log B) := min_le_right _ _
    have h3 : 0 < 3 * Real.log B := by linarith
    calc c * (3 * Real.log B)
        ≤ (Real.log 2 / (3 * Real.log B)) * (3 * Real.log B) :=
          mul_le_mul_of_nonneg_right hcr h3.le
      _ = Real.log 2 := by field_simp
  refine ⟨c, hc0, fun N => ?_⟩
  obtain ⟨d, hdN, hd2, HX⟩ := H N
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd2
  -- Apply the construction with `X = B²`.
  have hX1 : (1 : ℝ) ≤ B ^ 2 := by nlinarith
  obtain ⟨A, hlow, hhigh, hadd, hmul⟩ := HX (B ^ 2) hX1
  set n : ℝ := (A.card : ℝ) with hndef
  -- Rephrase the lower/upper bounds on `n` with base `B`.
  have hn2d : B ^ (2 * d) ≤ n := by rw [pow_mul]; exact hlow
  have hb3 : C₀ * B ^ 2 ≤ B ^ 3 := by
    rw [show B ^ 3 = B * B ^ 2 by ring]; exact mul_le_mul_of_nonneg_right hC₀B (sq_nonneg B)
  have hn3d : n ≤ B ^ (3 * d) := by
    calc n ≤ (C₀ * B ^ 2) ^ d := hhigh
      _ ≤ (B ^ 3) ^ d := pow_le_pow_left₀ (mul_nonneg hC₀.le (sq_nonneg B)) hb3 d
      _ = B ^ (3 * d) := by rw [← pow_mul]
  have hn1 : (1 : ℝ) ≤ n := le_trans (one_le_pow₀ hB1) hn2d
  -- The two estimates.
  have h_add : ((A + A).card : ℝ) ≤ n ^ (2 - c) := by
    calc ((A + A).card : ℝ) ≤ C₀ ^ d * n := hadd
      _ ≤ B ^ d * n := by gcongr
      _ ≤ n ^ (2 - c) := aux_add hB1 hc12 hn2d
  have h_mul : ((A * A).card : ℝ) ≤ n ^ (2 - c) := by
    calc ((A * A).card : ℝ) ≤ n ^ 2 / 2 ^ d := hmul
      _ ≤ n ^ (2 - c) := aux_mul hB1 hc0.le hlogc hn3d hn1
  refine ⟨A, ?_, ?_⟩
  · -- `N ≤ |A|`.
    have hb4 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
    have h4 : ((4 : ℕ) ^ d : ℝ) ≤ n := by
      calc ((4 : ℕ) ^ d : ℝ) = (4 : ℝ) ^ d := by push_cast; ring
        _ ≤ (B ^ 2) ^ d := by gcongr
        _ ≤ n := hlow
    have h4nat : (4 : ℕ) ^ d ≤ A.card := by rw [hndef] at h4; exact_mod_cast h4
    calc N ≤ d := hdN
      _ ≤ 2 ^ d := (Nat.lt_two_pow_self).le
      _ ≤ 4 ^ d := Nat.pow_le_pow_left (by norm_num) d
      _ ≤ A.card := h4nat
  · rw [Nat.cast_max]
    exact max_le h_add h_mul

end SumProduct
