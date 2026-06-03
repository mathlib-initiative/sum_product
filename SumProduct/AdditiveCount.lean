/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.Boxes

/-!
# Lemma 3.5 — the additive lattice-point count

For a totally real field of degree `d` and `X ≥ 0`,
`X^d / √Δ_K ≤ |B⁺(X)| ≤ (2X+1)^d`  (`lattice_count_add`).
The upper bound is an `L^∞` packing argument; the lower bound is Blichfeldt's theorem for the
Minkowski lattice (covolume `√Δ_K`).  Both bounds are proved here.
-/

open scoped NumberField
open Pointwise

namespace SumProduct

open NumberField NumberField.InfinitePlace in
/-- A nonzero algebraic integer has some archimedean absolute value `≥ 1`: since `|N(γ)| ≥ 1` and
`∏_w (w γ)^{mult w} = |N(γ)|`, not all places can be `< 1`. This is the `1`-separation of distinct
lattice points (`α ≠ β ⟹ ∃ w, 1 ≤ w(α−β)`) underlying the upper bounds of Lemmas 3.5 and 3.7. -/
theorem exists_place_ge_one {K : Type*} [Field K] [NumberField K] {γ : 𝓞 K} (hγ : γ ≠ 0) :
    ∃ w : InfinitePlace K, 1 ≤ w (γ : K) := by
  classical
  by_contra h
  push Not at h
  have hnorm_ne : Algebra.norm ℤ γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ
  have hge : (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (γ : K) ^ mult w := by
    rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ γ| := Int.one_le_abs hnorm_ne
    push_cast
    exact_mod_cast h1
  have hlt : (∏ w : InfinitePlace K, w (γ : K) ^ mult w) < 1 := by
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
    have hfac_lt : w₀ (γ : K) ^ mult w₀ < 1 :=
      pow_lt_one₀ (apply_nonneg w₀ _) (h w₀) mult_ne_zero
    have hrest_le : (∏ w ∈ Finset.univ.erase w₀, w (γ : K) ^ mult w) ≤ 1 :=
      Finset.prod_le_one (fun w _ => by positivity)
        (fun w _ => pow_le_one₀ (apply_nonneg w _) (h w).le)
    calc w₀ (γ : K) ^ mult w₀ * ∏ w ∈ Finset.univ.erase w₀, w (γ : K) ^ mult w
        ≤ w₀ (γ : K) ^ mult w₀ * 1 := mul_le_mul_of_nonneg_left hrest_le (by positivity)
      _ = w₀ (γ : K) ^ mult w₀ := mul_one _
      _ < 1 := hfac_lt
  linarith

open NumberField NumberField.InfinitePlace in
/-- The Minkowski (real) embedding of a totally real field, `α ↦ (σ_w α)_w`, into the coordinate
space `InfinitePlace K → ℝ`. -/
noncomputable def realEmbed (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (α : 𝓞 K) : NumberField.InfinitePlace K → ℝ :=
  fun w => embedding_of_isReal (NumberField.IsTotallyReal.isReal w) (α : K)

open NumberField NumberField.InfinitePlace in
/-- Each coordinate of `realEmbed` has absolute value equal to the corresponding place. -/
theorem abs_realEmbed {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (α : 𝓞 K) (w : InfinitePlace K) : |realEmbed K α w| = w (α : K) := by
  rw [realEmbed, ← Real.norm_eq_abs, norm_embedding_of_isReal]

open NumberField NumberField.InfinitePlace in
/-- Distinct algebraic integers are `1`-separated in the sup-metric of the real embedding: some
coordinate differs by `≥ 1`. This is the geometric form of `exists_place_ge_one`. -/
theorem exists_coord_dist_ge_one {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {α β : 𝓞 K} (h : α ≠ β) :
    ∃ w : InfinitePlace K, 1 ≤ |realEmbed K α w - realEmbed K β w| := by
  obtain ⟨w, hw⟩ := exists_place_ge_one (sub_ne_zero.mpr h)
  refine ⟨w, ?_⟩
  have hsub : realEmbed K α w - realEmbed K β w = realEmbed K (α - β) w := by
    simp only [realEmbed]
    rw [show ((α - β : 𝓞 K) : K) = (α : K) - (β : K) by push_cast; ring, map_sub]
  rw [hsub, abs_realEmbed]
  exact hw

/-- The Minkowski real embedding is injective (distinct integers differ in some coordinate). -/
theorem realEmbed_injective {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K] :
    Function.Injective (realEmbed K) := by
  intro α β h
  by_contra hne
  obtain ⟨w, hw⟩ := exists_coord_dist_ge_one hne
  rw [h, sub_self, abs_zero] at hw
  linarith

open NumberField NumberField.InfinitePlace in
/-- For a totally real field of degree `d`, there are exactly `d` infinite places. -/
theorem card_infinitePlace_eq {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) : Fintype.card (InfinitePlace K) = d := by
  have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hc := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hr := card_add_two_mul_card_eq_rank K
  rw [hd] at hr; omega

open MeasureTheory NumberField NumberField.InfinitePlace in
/-- Volume of an axis-aligned cube of side `b − a` in the embedding space `InfinitePlace K → ℝ`
(dimension `d`): `(b − a)^d`. -/
theorem volume_pi_Ioo_const {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) {a b : ℝ} (hab : a ≤ b) :
    volume (Set.univ.pi fun _ : InfinitePlace K => Set.Ioo a b) = ENNReal.ofReal ((b - a) ^ d) := by
  rw [volume_pi_pi]
  simp only [Real.volume_Ioo]
  rw [Finset.prod_const, Finset.card_univ, card_infinitePlace_eq hd,
    ← ENNReal.ofReal_pow (by linarith)]

open scoped Classical in
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- Volume of the open box `{x : mixedSpace K | ∀ w, normAtPlace w x < r}` for a totally real
field of degree `d`: it is `(2r)^d`. This is the box used in the Blichfeldt lower bound. -/
theorem volume_convexBodyLT_const {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (r : NNReal) :
    volume (convexBodyLT K (fun _ => r)) = (2 : ENNReal) ^ d * (r : ENNReal) ^ d := by
  have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hr : nrRealPlaces K = d := by
    have h := card_add_two_mul_card_eq_rank K
    rw [hd, h0] at h; omega
  have hsum : ∑ w : InfinitePlace K, mult w = d := by rw [sum_mult_eq, hd]
  rw [convexBodyLT_volume, convexBodyLTFactor, h0, pow_zero, mul_one, hr,
    Finset.prod_pow_eq_pow_sum, hsum, ENNReal.coe_pow]
  norm_num

open MeasureTheory NumberField NumberField.InfinitePlace in
/-- **Upper bound of Lemma 3.5.** `|B⁺(X)| ≤ (2X+1)^d`, by `L^∞` packing: the unit cubes centred
at the (1-separated) embedded lattice points are disjoint and lie in a box of side `2X+1`. -/
theorem boxAdd_card_le (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d := by
  classical
  have hcard : Fintype.card (InfinitePlace K) = d := by
    have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
    have hc := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hr := card_add_two_mul_card_eq_rank K
    rw [hd] at hr; omega
  set C : 𝓞 K → Set (InfinitePlace K → ℝ) :=
    fun α => Set.univ.pi fun w => Set.Ioo (realEmbed K α w - 1 / 2) (realEmbed K α w + 1 / 2)
    with hC
  have hmeas : ∀ α, MeasurableSet (C α) :=
    fun α => MeasurableSet.pi Set.countable_univ fun w _ => measurableSet_Ioo
  have hvolC : ∀ α, volume (C α) = 1 := fun α => by
    rw [hC]; simp only; rw [volume_pi_pi]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [Real.volume_Ioo, show realEmbed K α w + 1 / 2 - (realEmbed K α w - 1 / 2) = (1 : ℝ) by ring,
      ENNReal.ofReal_one]
  have hdisj : (↑(boxAdd K X) : Set (𝓞 K)).PairwiseDisjoint C := by
    intro α _ β _ hab
    obtain ⟨w, hw⟩ := exists_coord_dist_ge_one hab
    simp only [Function.onFun, hC]
    rw [Set.disjoint_univ_pi]
    refine ⟨w, Set.disjoint_left.mpr fun x hx hx' => ?_⟩
    rw [Set.mem_Ioo] at hx hx'
    have : |realEmbed K α w - realEmbed K β w| < 1 := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
    linarith
  have hsub : (⋃ α ∈ boxAdd K X, C α) ⊆
      Set.univ.pi fun _ : InfinitePlace K => Set.Ioo (-X - 1 / 2) (X + 1 / 2) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨α, hα, hxα⟩ := hx
    rw [hC] at hxα; simp only at hxα
    rw [Set.mem_univ_pi] at hxα ⊢
    intro w
    have hax := hxα w
    rw [Set.mem_Ioo] at hax ⊢
    have habs : |realEmbed K α w| ≤ X := by rw [abs_realEmbed]; exact (mem_boxAdd.mp hα) w
    rw [abs_le] at habs
    constructor <;> linarith [hax.1, hax.2, habs.1, habs.2]
  have hboxvol : volume (Set.univ.pi fun _ : InfinitePlace K => Set.Ioo (-X - 1 / 2) (X + 1 / 2))
      = ENNReal.ofReal ((2 * X + 1) ^ d) := by
    rw [volume_pi_pi]
    have hone : ∀ w ∈ (Finset.univ : Finset (InfinitePlace K)),
        volume (Set.Ioo (-X - 1 / 2) (X + 1 / 2)) = ENNReal.ofReal (2 * X + 1) := by
      intro w _; rw [Real.volume_Ioo]; congr 1; ring
    rw [Finset.prod_congr rfl hone, Finset.prod_const, Finset.card_univ, hcard,
      ← ENNReal.ofReal_pow (by linarith)]
  have hsum : (↑(boxAdd K X).card : ENNReal) ≤ ENNReal.ofReal ((2 * X + 1) ^ d) := by
    rw [← hboxvol]
    calc (↑(boxAdd K X).card : ENNReal)
        = ∑ α ∈ boxAdd K X, volume (C α) := by
          rw [Finset.sum_congr rfl fun α _ => hvolC α, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = volume (⋃ α ∈ boxAdd K X, C α) :=
          (measure_biUnion_finset hdisj fun α _ => hmeas α).symm
      _ ≤ _ := measure_mono hsub
  have hconv := (ENNReal.toReal_le_toReal (by simp) (by simp)).mpr hsum
  rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at hconv

open NumberField NumberField.InfinitePlace in
/-- Difference-set step of the Lemma 3.5 lower bound: any finite set of integers whose embeddings
all lie in a sup-ball of radius `r` around a common centre injects (via `α ↦ α − α₀`) into
`B⁺(2r)`, so its cardinality is `≤ |B⁺(2r)|`. -/
theorem card_le_boxAdd_of_ball {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (r : ℝ) (c : InfinitePlace K → ℝ) (T : Finset (𝓞 K))
    (hT : ∀ α ∈ T, ∀ w, |realEmbed K α w - c w| ≤ r) :
    T.card ≤ (boxAdd K (2 * r)).card := by
  rcases T.eq_empty_or_nonempty with hTe | ⟨α₀, hα₀⟩
  · simp [hTe]
  · refine Finset.card_le_card_of_injOn (fun α => α - α₀) ?_ ?_
    · intro α hα
      simp only [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← abs_realEmbed]
      have e : realEmbed K (α - α₀) w = realEmbed K α w - realEmbed K α₀ w := by
        simp only [realEmbed]
        rw [show ((α - α₀ : 𝓞 K) : K) = (α : K) - (α₀ : K) by push_cast; ring, map_sub]
      rw [e]
      calc |realEmbed K α w - realEmbed K α₀ w|
          ≤ |realEmbed K α w - c w| + |c w - realEmbed K α₀ w| := by
            rw [show realEmbed K α w - realEmbed K α₀ w
                = (realEmbed K α w - c w) + (c w - realEmbed K α₀ w) by ring]
            exact abs_add_le _ _
        _ ≤ r + r := by
            have h1 := hT α hα w
            have h2 := hT α₀ hα₀ w
            rw [abs_sub_comm (c w) (realEmbed K α₀ w)]
            linarith
        _ = 2 * r := by ring
    · intro α _ β _ h
      linear_combination h

open NumberField NumberField.mixedEmbedding in
/-- The additive embedding `𝒪_K ↪ mixedSpace K` (the mixed embedding restricted to the integers).
Its range is `mixedEmbedding.integerLattice K`. -/
noncomputable def latticeEmbed (K : Type*) [Field K] [NumberField K] : 𝓞 K →+ mixedSpace K :=
  ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).toAddMonoidHom

@[simp] theorem latticeEmbed_apply {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    latticeEmbed K α = NumberField.mixedEmbedding K (algebraMap (𝓞 K) K α) := rfl

theorem latticeEmbed_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (latticeEmbed K) :=
  (NumberField.mixedEmbedding_injective K).comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
theorem normAtPlace_latticeEmbed {K : Type*} [Field K] [NumberField K] (α : 𝓞 K)
    (w : InfinitePlace K) : normAtPlace w (latticeEmbed K α) = w (α : K) := by
  rw [latticeEmbed_apply, normAtPlace_apply]

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Metric in
/-- Membership in the open box `convexBodyLT K f`, in terms of `normAtPlace`. -/
theorem mem_convexBodyLT_iff {K : Type*} [Field K] [NumberField K] (f : InfinitePlace K → NNReal)
    (y : mixedSpace K) : y ∈ convexBodyLT K f ↔ ∀ w : InfinitePlace K, normAtPlace w y < f w := by
  simp only [convexBodyLT, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall]
  constructor
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw
  · intro h
    exact ⟨fun w hw => by rw [← normAtPlace_apply_of_isReal hw]; exact h w,
           fun w hw => by rw [← normAtPlace_apply_of_isComplex hw]; exact h w⟩

open NumberField NumberField.mixedEmbedding in
/-- The range of `latticeEmbed` is exactly the integer lattice. -/
theorem range_latticeEmbed (K : Type*) [Field K] [NumberField K] :
    Set.range (latticeEmbed K) = ↑(mixedEmbedding.integerLattice K) := by
  rw [mixedEmbedding.integerLattice, LinearMap.coe_range]
  rfl

open NumberField NumberField.mixedEmbedding in
/-- The bijection `𝒪_K ≃ integerLattice K` induced by the (injective) lattice embedding. -/
noncomputable def latticeEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ ↥(mixedEmbedding.integerLattice K) :=
  (Equiv.ofInjective (latticeEmbed K) latticeEmbed_injective).trans
    (Equiv.setCongr (range_latticeEmbed K))

open NumberField.mixedEmbedding in
@[simp] theorem latticeEquiv_coe {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    ((latticeEquiv K α : mixedSpace K)) = latticeEmbed K α := rfl

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- Pointwise count bound (heart of the Blichfeldt lower bound): for any translate by
`x : mixedSpace K`, the integers `α` whose embedding lands in the radius-`r` box `x + S`
inject (via `α ↦ α − α₀`) into `B⁺(2r)`, so there are at most `|B⁺(2r)|` of them. -/
theorem count_le_boxAdd {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.ncard
      ≤ (boxAdd K (2 * (r : ℝ))).card := by
  set T := {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} with hT
  rcases T.eq_empty_or_nonempty with he | ⟨α₀, hα₀⟩
  · simp [he]
  · have hinj : Set.InjOn (· - α₀) T := fun a _ b _ h => by linear_combination h
    have hsub : (· - α₀) '' T ⊆ ↑(boxAdd K (2 * (r : ℝ))) := by
      rintro _ ⟨α, hα, rfl⟩
      have hαmem : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r) := hα
      have hα₀mem : latticeEmbed K α₀ + x ∈ convexBodyLT K (fun _ => r) := hα₀
      rw [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← normAtPlace_latticeEmbed]
      have e : latticeEmbed K (α - α₀)
          = (latticeEmbed K α + x) - (latticeEmbed K α₀ + x) := by rw [map_sub]; abel
      rw [e]
      have key : normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
          ≤ normAtPlace w (latticeEmbed K α + x) + normAtPlace w (latticeEmbed K α₀ + x) := by
        calc normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
            = normAtPlace w ((latticeEmbed K α + x) + -(latticeEmbed K α₀ + x)) := by
              rw [sub_eq_add_neg]
          _ ≤ normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (-(latticeEmbed K α₀ + x)) := normAtPlace_add_le w _ _
          _ = normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (latticeEmbed K α₀ + x) := by rw [normAtPlace_neg]
      have h1 := (mem_convexBodyLT_iff _ _).mp hαmem w
      have h2 := (mem_convexBodyLT_iff _ _).mp hα₀mem w
      simp only at h1 h2
      have : (2 : ℝ) * (r : ℝ) = (r : ℝ) + (r : ℝ) := by ring
      linarith
    calc T.ncard = ((· - α₀) '' T).ncard := (Set.InjOn.ncard_image hinj).symm
      _ ≤ (↑(boxAdd K (2 * (r : ℝ))) : Set (𝓞 K)).ncard :=
            Set.ncard_le_ncard hsub (boxAdd K (2 * (r : ℝ))).finite_toSet
      _ = (boxAdd K (2 * (r : ℝ))).card := Set.ncard_coe_finset _

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- `encard` form of `count_le_boxAdd` (the form needed for the tsum bound). -/
theorem count_encard_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.encard
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ℕ∞) := by
  set T := {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} with hT
  rcases T.eq_empty_or_nonempty with he | ⟨α₀, hα₀⟩
  · simp [he]
  · have hinj : Set.InjOn (· - α₀) T := fun a _ b _ h => by linear_combination h
    have hsub : (· - α₀) '' T ⊆ ↑(boxAdd K (2 * (r : ℝ))) := by
      rintro _ ⟨α, hα, rfl⟩
      have hαmem : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r) := hα
      have hα₀mem : latticeEmbed K α₀ + x ∈ convexBodyLT K (fun _ => r) := hα₀
      rw [Finset.mem_coe, mem_boxAdd]
      intro w
      rw [← normAtPlace_latticeEmbed]
      have e : latticeEmbed K (α - α₀)
          = (latticeEmbed K α + x) - (latticeEmbed K α₀ + x) := by rw [map_sub]; abel
      rw [e]
      have key : normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
          ≤ normAtPlace w (latticeEmbed K α + x) + normAtPlace w (latticeEmbed K α₀ + x) := by
        calc normAtPlace w ((latticeEmbed K α + x) - (latticeEmbed K α₀ + x))
            = normAtPlace w ((latticeEmbed K α + x) + -(latticeEmbed K α₀ + x)) := by
              rw [sub_eq_add_neg]
          _ ≤ normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (-(latticeEmbed K α₀ + x)) := normAtPlace_add_le w _ _
          _ = normAtPlace w (latticeEmbed K α + x)
              + normAtPlace w (latticeEmbed K α₀ + x) := by rw [normAtPlace_neg]
      have h1 := (mem_convexBodyLT_iff _ _).mp hαmem w
      have h2 := (mem_convexBodyLT_iff _ _).mp hα₀mem w
      simp only at h1 h2
      have : (2 : ℝ) * (r : ℝ) = (r : ℝ) + (r : ℝ) := by ring
      linarith
    calc T.encard = ((· - α₀) '' T).encard := (Set.InjOn.encard_image hinj).symm
      _ ≤ (↑(boxAdd K (2 * (r : ℝ))) : Set (𝓞 K)).encard := Set.encard_le_encard hsub
      _ = ((boxAdd K (2 * (r : ℝ))).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- The multiplicity at `x`: the number of lattice points `ℓ` with `ℓ + x` in the radius-`r` box
is at most `|B⁺(2r)|`. (Tsum form of `count_encard_le`, reindexed over `𝒪_K`.) -/
theorem tsum_indicator_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (x : mixedSpace K) (r : NNReal) :
    ∑' l : ↥(mixedEmbedding.integerLattice K),
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) ((l : mixedSpace K) + x)
      ≤ ((boxAdd K (2 * (r : ℝ))).card : ENNReal) := by
  have hfun : (fun α : 𝓞 K =>
        (convexBodyLT K (fun _ => r)).indicator (fun _ => (1 : ENNReal)) (latticeEmbed K α + x))
      = {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)}.indicator (fun _ => 1) := by
    funext α
    by_cases h : latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)
    · have h' : α ∈ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : α ∉ {α : 𝓞 K | latticeEmbed K α + x ∈ convexBodyLT K (fun _ => r)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [← Equiv.tsum_eq (latticeEquiv K)]
  simp only [latticeEquiv_coe]
  rw [hfun, ← tsum_subtype, ENNReal.tsum_set_one]
  exact_mod_cast count_encard_le x r

open scoped Classical in
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- **Lower bound of Lemma 3.5** (Blichfeldt). For a totally real field of degree `d` and `X ≥ 0`,
`X^d / √Δ_K ≤ |B⁺(X)|`. Proof: the multiplicity `g(y) = #{ℓ ∈ L : ℓ + y ∈ S}` of the radius-`X/2`
box `S` satisfies `∫_F g = vol S = X^d` (fundamental-domain decomposition) and `g(y) ≤ |B⁺(X)|`
pointwise (`count`), so `X^d ≤ |B⁺(X)| · vol F = |B⁺(X)| · √Δ_K`. -/
theorem boxAdd_card_ge {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card := by
  set r : NNReal := ⟨X / 2, by positivity⟩ with hr
  have hcoe : (r : ℝ) = X / 2 := by rw [hr]; rfl
  have hr2 : 2 * (r : ℝ) = X := by rw [hcoe]; ring
  set S := convexBodyLT K (fun _ => r) with hS
  set F := ZSpan.fundamentalDomain (latticeBasis K) with hFdef
  have hfund : IsAddFundamentalDomain (mixedEmbedding.integerLattice K) F volume :=
    fundamentalDomain_integerLattice K
  haveI : MeasurableVAdd (mixedEmbedding.integerLattice K) (mixedSpace K) :=
    inferInstanceAs (MeasurableVAdd (mixedEmbedding.integerLattice K).toAddSubgroup _)
  haveI : VAddInvariantMeasure (mixedEmbedding.integerLattice K) (mixedSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (mixedEmbedding.integerLattice K).toAddSubgroup _ _)
  have hSmeas : MeasurableSet S := by
    rw [hS, convexBodyLT]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  set f : mixedSpace K → ENNReal := S.indicator (fun _ => 1) with hf
  have hfmeas : Measurable f := measurable_const.indicator hSmeas
  -- discriminant positivity
  have hsqrtpos : 0 < Real.sqrt |(NumberField.discr K : ℝ)| := by
    rw [Real.sqrt_pos, abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  -- covolume = √Δ
  have hFreal : (volume F).toReal = Real.sqrt |(NumberField.discr K : ℝ)| := by
    have hcov : ZLattice.covolume (mixedEmbedding.integerLattice K) volume
        = Real.sqrt |(NumberField.discr K : ℝ)| := by
      rw [mixedEmbedding.covolume_integerLattice, IsTotallyReal.nrComplexPlaces_eq_zero,
        pow_zero, one_mul]
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, Measure.real]
  have hFne : volume F ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hFreal
    exact (ne_of_gt hsqrtpos) hFreal.symm
  -- volume of the box
  have hvolS : volume S = (2 : ENNReal) ^ d * (r : ENNReal) ^ d :=
    volume_convexBodyLT_const hd r
  -- the integral chain: vol S ≤ |B⁺(X)| · vol F
  have hSF : volume S ≤ (↑(boxAdd K X).card : ENNReal) * volume F := by
    have hint : ∫⁻ y, f y = volume S := by
      rw [hf, lintegral_indicator hSmeas, setLIntegral_one]
    have hkey : volume S
        = ∑' l : ↥(mixedEmbedding.integerLattice K), ∫⁻ y in F, f (l +ᵥ y) := by
      rw [← hint]; exact hfund.lintegral_eq_tsum'' f
    have hdecomp : volume S
        = ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y) := by
      rw [hkey]
      exact (lintegral_tsum fun l : ↥(mixedEmbedding.integerLattice K) =>
        (hfmeas.comp (measurable_const_vadd l)).aemeasurable).symm
    rw [hdecomp]
    calc ∫⁻ y in F, ∑' l : ↥(mixedEmbedding.integerLattice K), f (l +ᵥ y)
        ≤ ∫⁻ _ in F, (↑(boxAdd K X).card : ENNReal) := by
          refine lintegral_mono fun y => ?_
          have h := tsum_indicator_le y r
          rw [hr2] at h
          exact h
      _ = (↑(boxAdd K X).card : ENNReal) * volume F := by rw [setLIntegral_const]
  -- convert to reals
  have hSne : volume S ≠ ⊤ := by
    rw [hvolS]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hprodne : (↑(boxAdd K X).card : ENNReal) * volume F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFne
  have hreal := (ENNReal.toReal_le_toReal hSne hprodne).mpr hSF
  rw [hvolS, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_natCast, hFreal, hcoe,
    ← mul_pow, show (2 : ℝ) * (X / 2) = X by ring] at hreal
  rw [div_le_iff₀ hsqrtpos]
  exact hreal

/-- **Lemma 3.5** (`lem-ball`, additive lattice-point count).

For a totally real field of degree `d` and `X ≥ 0`,
`X^d / √Δ_K ≤ |B⁺(X)| ≤ (2X+1)^d`. The lower bound is Blichfeldt's lemma applied to the
Minkowski lattice (covolume `√Δ_K`); the upper bound is an `L^∞` packing argument using that
distinct algebraic integers are `1`-separated in some embedding (`|N(x−y)| ≥ 1`).

(For `0 ≤ X < 1` the lower bound is trivial: `X^d/√Δ_K ≤ 1 ≤ |B⁺(X)|` as `0 ∈ B⁺(X)`.) -/
theorem lattice_count_add (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (X : ℝ) (hX : 0 ≤ X) :
    X ^ d / Real.sqrt |(NumberField.discr K : ℝ)| ≤ (boxAdd K X).card ∧
      ((boxAdd K X).card : ℝ) ≤ (2 * X + 1) ^ d :=
  ⟨boxAdd_card_ge hd X hX, boxAdd_card_le K d hd X hX⟩

end SumProduct
