/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SumProduct.Boxes
import SumProduct.Blichfeldt
import SumProduct.UnitSeparation
import SumProduct.GoldenRatio
import SumProduct.CubeSectionHensley

/-!
# Lemma 3.7 — the multiplicative lattice-point count

For a totally real field of degree `d` and `Y ≥ 1`,
`Y^{d-1} / (√d · R_K) ≤ |B^×(Y)| ≤ 10 (5Y+1)^{d-1}`  (`lattice_count_mult`).
Work takes place in the unit lattice inside `logSpace K`.  The lower bound is Blichfeldt; the
upper bound is a `{±1}`-fibration over a packing argument using the separation `unit_separation`.
The only analytic input is equation (3.1) (`hensley_unitBox_volume`).
-/

open scoped NumberField
open Pointwise

namespace SumProduct

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric in
/-- The unit-lattice points inside `unitBox K Y` form a finite set (discreteness + boundedness). -/
theorem unitLattice_inter_unitBox_finite {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (hY : 0 ≤ Y) : (↑(unitLattice K) ∩ unitBox K Y).Finite := by
  refine (unitLattice_inter_ball_finite K Y).subset ?_
  rintro x ⟨hx1, hx2, -⟩
  refine ⟨hx1, ?_⟩
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hY]
  intro w
  rw [Real.norm_eq_abs]
  exact hx2 w

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- Pointwise multiplicity bound for the unit lattice: every translate of the radius-`Y/2` box
contains at most `#(unitLattice ∩ unitBox Y)` lattice points (difference-set injection). -/
theorem unitLattice_multiplicity_le {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (y : logSpace K) :
    ∑' l : ↥(unitLattice K), (unitBox K (Y / 2)).indicator (fun _ => (1 : ENNReal)) (l +ᵥ y)
      ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
  have hfun : (fun l : ↥(unitLattice K) =>
        (unitBox K (Y / 2)).indicator (fun _ => (1 : ENNReal)) (l +ᵥ y))
      = {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.indicator (fun _ => 1) := by
    funext l
    by_cases h : l +ᵥ y ∈ unitBox K (Y / 2)
    · have h' : l ∈ {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : l ∉ {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [hfun, ← tsum_subtype, ENNReal.tsum_set_one]
  have hle : {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.encard
      ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
    rcases Set.eq_empty_or_nonempty {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}
      with he | ⟨l₀, hl₀⟩
    · rw [he]; simp
    · have hl₀mem : (l₀ : logSpace K) + y ∈ unitBox K (Y / 2) := hl₀
      calc {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.encard
          = ((fun l : ↥(unitLattice K) => ((l - l₀ : ↥(unitLattice K)) : logSpace K)) ''
              {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}).encard := by
            refine (Set.InjOn.encard_image ?_).symm
            intro a _ b _ hab
            simp only [] at hab
            exact sub_left_inj.mp (Subtype.coe_injective hab)
        _ ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
            refine Set.encard_le_encard ?_
            rintro _ ⟨l, hl, rfl⟩
            have hlmem : (l : logSpace K) + y ∈ unitBox K (Y / 2) := hl
            have hcoe : ((l - l₀ : ↥(unitLattice K)) : logSpace K)
                = ((l : logSpace K) + y) - ((l₀ : logSpace K) + y) := by
              rw [AddSubgroupClass.coe_sub]; abel
            refine ⟨SetLike.coe_mem _, ?_⟩
            change ((l - l₀ : ↥(unitLattice K)) : logSpace K) ∈ unitBox K Y
            rw [hcoe, show Y = Y / 2 + Y / 2 by ring]
            exact sub_mem_unitBox hlmem hl₀mem
  exact_mod_cast hle

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- The number of unit-lattice points in `unitBox K Y` is at most `|B^×(Y)|` (they are exactly the
image of `B^×(Y)` under the log embedding). -/
theorem unitLattice_inter_unitBox_ncard_le {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    (↑(unitLattice K) ∩ unitBox K Y).ncard ≤ (boxMult K Y).card := by
  have himg : ↑(unitLattice K) ∩ unitBox K Y
      = ↑((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))) := by
    ext p
    rw [Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨hp1, hp2⟩
      rw [SetLike.mem_coe, unitLattice, Submodule.mem_map] at hp1
      obtain ⟨x, -, hx⟩ := hp1
      have hx' : logEmbedding K x = p := hx
      refine ⟨Additive.toMul x, ?_, ?_⟩
      · rw [Finset.mem_coe, ← logEmbedding_mem_unitBox_iff]
        change logEmbedding K x ∈ unitBox K Y
        rw [hx']; exact hp2
      · change logEmbedding K x = p
        exact hx'
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_coe] at hu
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, unitLattice, Submodule.mem_map]
        exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩
      · rw [logEmbedding_mem_unitBox_iff]; exact hu
  rw [himg, Set.ncard_coe_finset]
  exact Finset.card_image_le

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric in
/-- **Lower bound of Lemma 3.7** (Blichfeldt in the unit lattice). For a totally real field of
degree `d` and `Y ≥ 1`, `Y^{d-1} / (√d · R_K) ≤ |B^×(Y)|`. -/
theorem boxMult_card_ge {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hRpos : 0 < regulator K := regulator_pos K
  have hdpos : 0 < Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_pos]
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hd] at this; exact_mod_cast this
  set b := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K) with hb
  set F := ZSpan.fundamentalDomain b with hF
  have hfund : IsAddFundamentalDomain (unitLattice K) F volume := by
    have h := ZSpan.isAddFundamentalDomain b volume
    rwa [(basisUnitLattice K).ofZLatticeBasis_span ℝ] at h
  haveI : MeasurableVAdd (unitLattice K) (logSpace K) :=
    inferInstanceAs (MeasurableVAdd (unitLattice K).toAddSubgroup _)
  haveI : VAddInvariantMeasure (unitLattice K) (logSpace K) volume :=
    inferInstanceAs (VAddInvariantMeasure (unitLattice K).toAddSubgroup _ _)
  have hSmeas : MeasurableSet (unitBox K (Y / 2)) := by
    rw [unitBox, Set.setOf_and]
    refine (IsClosed.inter ?_ ?_).measurableSet
    · rw [Set.setOf_forall]
      exact isClosed_iInter fun w =>
        isClosed_le (continuous_abs.comp (continuous_apply w)) continuous_const
    · exact isClosed_le
        (continuous_abs.comp (continuous_finsetSum _ fun w _ => continuous_apply w))
        continuous_const
  have hfin := unitLattice_inter_unitBox_finite (K := K) (Y := Y) hY0
  set N := (↑(unitLattice K) ∩ unitBox K Y).ncard with hNdef
  have hbli : volume (unitBox K (Y / 2)) ≤ (N : ENNReal) * volume F := by
    refine volume_le_of_tsum_indicator_le hfund hSmeas (fun y => ?_)
    refine (unitLattice_multiplicity_le y).trans ?_
    rw [hNdef, ← Set.Finite.cast_ncard_eq hfin]
    exact_mod_cast le_refl _
  have hcov : ZLattice.covolume (unitLattice K) volume = regulator K := rfl
  have hFreal : (volume F).toReal = regulator K := by
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund, Measure.real]
  have hFne : volume F ≠ ⊤ := by
    intro htop; rw [htop, ENNReal.toReal_top] at hFreal; exact (ne_of_gt hRpos) hFreal.symm
  have hsub : unitBox K (Y / 2) ⊆ closedBall 0 (Y / 2) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith)]
    intro w; rw [Real.norm_eq_abs]; exact hx.1 w
  have hSne : volume (unitBox K (Y / 2)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall 0 (Y / 2)).measure_lt_top)
  have hprodne : (N : ENNReal) * volume F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFne
  have hreal := (ENNReal.toReal_le_toReal hSne hprodne).mpr hbli
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hFreal] at hreal
  obtain ⟨hlo, -⟩ := hensley_unitBox_volume K (Y / 2) (by linarith)
  rw [hd, show (2 : ℝ) * (Y / 2) = Y by ring] at hlo
  have hNR : Y ^ (d - 1) / Real.sqrt d ≤ (N : ℝ) * regulator K := le_trans hlo hreal
  have key : Y ^ (d - 1) ≤ (N : ℝ) * regulator K * Real.sqrt d := (div_le_iff₀ hdpos).mp hNR
  have hNle : (N : ℝ) ≤ (boxMult K Y).card := by
    exact_mod_cast unitLattice_inter_unitBox_ncard_le (K := K) (Y := Y)
  calc Y ^ (d - 1) / (Real.sqrt d * regulator K)
      ≤ (N : ℝ) := by
        rw [div_le_iff₀ (by positivity),
          show (N : ℝ) * (Real.sqrt (d : ℝ) * regulator K) = N * regulator K * Real.sqrt d by ring]
        exact key
    _ ≤ (boxMult K Y).card := hNle

open scoped Classical in
open NumberField NumberField.Units NumberField.InfinitePlace in
set_option backward.isDefEq.respectTransparency false in
/-- A torsion unit of a totally real field is `±1` (its image under a real embedding is a real
root of unity, hence `±1`). -/
theorem torsion_eq_pm_one_of_totallyReal {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (x : torsion K) :
    (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    have hz := IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K))
    have hpos : 0 < nrRealPlaces K := by
      have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
      have hcard := card_eq_nrRealPlaces_add_nrComplexPlaces K
      have : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
      omega
    omega
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

open scoped Classical in
open NumberField NumberField.Units in
/-- The torsion order of a totally real number field is `2` (only `±1`). -/
theorem torsionOrder_eq_two_of_totallyReal {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : torsionOrder K = 2 := by
  classical
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
  exact torsion_eq_pm_one_of_totallyReal x

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- `|B^×(Y)| ≤ 2 · #(its log-embedding image)`: every fibre of the log embedding is a coset of
the torsion subgroup `{±1}`. -/
theorem boxMult_card_le_two_mul_image {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    (boxMult K Y).card
      ≤ 2 * ((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card := by
  refine Finset.card_le_mul_card_image _ 2 (fun p _ => ?_)
  rw [← torsionOrder_eq_two_of_totallyReal (K := K), torsionOrder]
  rcases (((boxMult K Y).filter
      (fun u => logEmbedding K (Additive.ofMul u) = p))).eq_empty_or_nonempty
    with he | ⟨u₀, hu₀⟩
  · rw [he]; simp
  · rw [Finset.mem_filter] at hu₀
    obtain ⟨-, hu₀p⟩ := hu₀
    have key : ∀ u ∈ (boxMult K Y).filter (fun u => logEmbedding K (Additive.ofMul u) = p),
        u * u₀⁻¹ ∈ torsion K := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [← logEmbedding_eq_zero_iff]
      have he2 : Additive.ofMul (u * u₀⁻¹) = Additive.ofMul u - Additive.ofMul u₀ := rfl
      rw [he2, map_sub, hu.2, hu₀p, sub_self]
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun u => if h : u * u₀⁻¹ ∈ torsion K then (⟨u * u₀⁻¹, h⟩ : torsion K) else 1)
      (fun u _ => Finset.mem_univ _) ?_
    intro u hu u' hu' heq
    rw [Finset.mem_coe] at hu hu'
    simp only [dif_pos (key u hu), dif_pos (key u' hu')] at heq
    exact mul_right_cancel (Subtype.ext_iff.mp heq)

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace Real in
/-- A unit-lattice point in `unitBox(2/5)` is `0`: the unit it comes from has every
`|log w(v)| ≤ 2/5 < log φ`, hence is `±1` by `unit_separation` (Lemma 3.6). -/
theorem unitLattice_unitBox_eq_zero {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {p : logSpace K}
    (hp : p ∈ unitLattice K) (hp2 : p ∈ unitBox K (2 / 5)) : p = 0 := by
  rw [unitLattice, Submodule.mem_map] at hp
  obtain ⟨x, -, hx⟩ := hp
  have hx' : logEmbedding K x = p := hx
  set v : (𝓞 K)ˣ := Additive.toMul x with hv
  have hvx : Additive.ofMul v = x := rfl
  have hvbox : v ∈ boxMult K (2 / 5) := by
    rw [← logEmbedding_mem_unitBox_iff, hvx, hx']; exact hp2
  rw [mem_boxMult] at hvbox
  have hsep : ∀ w : InfinitePlace K,
      goldenRatio⁻¹ < w ((v : 𝓞 K) : K) ∧ w ((v : 𝓞 K) : K) < goldenRatio := by
    intro w
    have hwpos : 0 < w ((v : 𝓞 K) : K) :=
      NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero _)
    have hlog : |Real.log (w ((v : 𝓞 K) : K))| < Real.log goldenRatio :=
      lt_of_le_of_lt (hvbox w) two_fifths_lt_log_goldenRatio
    rw [abs_lt] at hlog
    obtain ⟨hl1, hl2⟩ := hlog
    refine ⟨?_, ?_⟩
    · have h := Real.exp_lt_exp.mpr hl1
      rwa [Real.exp_log hwpos, Real.exp_neg, Real.exp_log goldenRatio_pos] at h
    · have h := Real.exp_lt_exp.mpr hl2
      rwa [Real.exp_log hwpos, Real.exp_log goldenRatio_pos] at h
  rw [← hx', ← hvx, logEmbedding_eq_zero_iff]
  rcases unit_separation K v hsep with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact neg_one_mem_torsion

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem Metric in
/-- **Packing bound** for the Lemma 3.7 upper estimate:
`#(unitLattice ∩ unitBox Y) ≤ 5(5Y+1)^{d-1}`. Disjoint translates of `unitBox(1/5)` (disjoint by
`unitLattice_unitBox_eq_zero`) pack into `unitBox(Y+1/5)`; eq (3.1) bounds the volumes, and the
constants work out exactly with radius `1/5`. -/
theorem unitLattice_inter_unitBox_packing {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) ≤ 5 * (5 * Y + 1) ^ (d - 1) := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hdpos : 0 < Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_pos]; have : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hd] at this; exact_mod_cast this
  have hfin := unitLattice_inter_unitBox_finite (K := K) (Y := Y) hY0
  set P := hfin.toFinset with hP
  set C : logSpace K → Set (logSpace K) := fun p => (fun y => y - p) ⁻¹' (unitBox K (1 / 5)) with hC
  have hvolfin : ∀ r : ℝ, 0 ≤ r → volume (unitBox K r) ≠ ⊤ := by
    intro r hr
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (isCompact_closedBall (0 : logSpace K) r).measure_lt_top)
    intro x hx
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]
    intro w; rw [Real.norm_eq_abs]; exact hx.1 w
  have hmeasC : ∀ p, MeasurableSet (C p) :=
    fun p => (measurableSet_unitBox (1 / 5)).preimage (by fun_prop)
  have hvolC : ∀ p, volume (C p) = volume (unitBox K (1 / 5)) := by
    intro p
    have hmp : MeasurePreserving (fun y : logSpace K => y - p) volume volume := by
      simpa [sub_eq_add_neg] using measurePreserving_add_right volume (-p)
    change volume ((fun y => y - p) ⁻¹' unitBox K (1 / 5)) = volume (unitBox K (1 / 5))
    exact hmp.measure_preimage (measurableSet_unitBox (1 / 5)).nullMeasurableSet
  have hdisj : (↑P : Set (logSpace K)).PairwiseDisjoint C := by
    intro p hp p' hp' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    simp only [hC, Set.mem_preimage] at hz hz'
    simp only [hP, Finset.mem_coe, Set.Finite.mem_toFinset] at hp hp'
    have hdiff : p' - p ∈ unitBox K (2 / 5) := by
      have h := sub_mem_unitBox hz hz'
      rw [show (1 : ℝ) / 5 + 1 / 5 = 2 / 5 by norm_num,
        show (z - p) - (z - p') = p' - p by abel] at h
      exact h
    have hlat : p' - p ∈ unitLattice K := (unitLattice K).sub_mem hp'.1 hp.1
    exact hne (sub_eq_zero.mp (unitLattice_unitBox_eq_zero hlat hdiff)).symm
  have hsub : (⋃ p ∈ P, C p) ⊆ unitBox K (Y + 1 / 5) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    simp only [hC, Set.mem_preimage] at hzp
    simp only [hP, Set.Finite.mem_toFinset] at hp
    have h := add_mem_unitBox hp.2 hzp
    rwa [show p + (z - p) = z by abel] at h
  have hpack : (P.card : ENNReal) * volume (unitBox K (1 / 5))
      ≤ volume (unitBox K (Y + 1 / 5)) := by
    calc (P.card : ENNReal) * volume (unitBox K (1 / 5))
        = ∑ p ∈ P, volume (C p) := by
          rw [Finset.sum_congr rfl (fun p _ => hvolC p), Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ p ∈ P, C p) := (measure_biUnion_finset hdisj (fun p _ => hmeasC p)).symm
      _ ≤ volume (unitBox K (Y + 1 / 5)) := measure_mono hsub
  -- convert to reals via eq (3.1)
  have hreal := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hvolfin _ (by norm_num)))
    (hvolfin _ (by positivity))).mpr hpack
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  obtain ⟨hlo, -⟩ := hensley_unitBox_volume K (1 / 5) (by norm_num)
  obtain ⟨-, hhi⟩ := hensley_unitBox_volume K (Y + 1 / 5) (by positivity)
  rw [hd, show (2 : ℝ) * (1 / 5) = 2 / 5 by norm_num] at hlo
  rw [hd] at hhi
  have hncard : ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) = (P.card : ℝ) := by
    rw [hP]; congr 1; exact Set.ncard_eq_toFinset_card _ hfin
  have hc : (0 : ℝ) < (2 / 5) ^ (d - 1) / Real.sqrt d := by positivity
  rw [hncard]
  refine le_of_mul_le_mul_right ?_ hc
  calc (P.card : ℝ) * ((2 / 5) ^ (d - 1) / Real.sqrt d)
      ≤ (P.card : ℝ) * (volume (unitBox K (1 / 5))).toReal := by gcongr
    _ ≤ (volume (unitBox K (Y + 1 / 5))).toReal := hreal
    _ ≤ 5 * (2 * (Y + 1 / 5)) ^ (d - 1) / Real.sqrt d := hhi
    _ = 5 * (5 * Y + 1) ^ (d - 1) * ((2 / 5) ^ (d - 1) / Real.sqrt d) := by
        rw [show (2 : ℝ) * (Y + 1 / 5) = (5 * Y + 1) * (2 / 5) by ring, mul_pow]; ring

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- The unit-lattice points in `unitBox Y` are exactly the log-embedding image of `B^×(Y)`. -/
theorem unitBox_inter_eq_image {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    ↑(unitLattice K) ∩ unitBox K Y
      = ↑((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))) := by
  ext p
  rw [Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨hp1, hp2⟩
    rw [SetLike.mem_coe, unitLattice, Submodule.mem_map] at hp1
    obtain ⟨x, -, hx⟩ := hp1
    have hx' : logEmbedding K x = p := hx
    refine ⟨Additive.toMul x, ?_, ?_⟩
    · rw [Finset.mem_coe, ← logEmbedding_mem_unitBox_iff]
      change logEmbedding K x ∈ unitBox K Y
      rw [hx']; exact hp2
    · change logEmbedding K x = p
      exact hx'
  · rintro ⟨u, hu, rfl⟩
    rw [Finset.mem_coe] at hu
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, unitLattice, Submodule.mem_map]
      exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩
    · rw [logEmbedding_mem_unitBox_iff]; exact hu

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- **Upper bound of Lemma 3.7**: `|B^×(Y)| ≤ 10(5Y+1)^{d-1}` (fibration `×2` over the torsion
`{±1}`, then the packing bound on the lattice points). -/
theorem boxMult_card_le {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) := by
  have himgcard : ((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card
      = (↑(unitLattice K) ∩ unitBox K Y).ncard := by
    rw [← Set.ncard_coe_finset, unitBox_inter_eq_image]
  have h2 : ((boxMult K Y).card : ℝ)
      ≤ 2 * (((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card : ℝ) := by
    exact_mod_cast boxMult_card_le_two_mul_image
  have hpack := unitLattice_inter_unitBox_packing hd Y hY
  calc ((boxMult K Y).card : ℝ)
      ≤ 2 * (((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card : ℝ) := h2
    _ = 2 * ((↑(unitLattice K) ∩ unitBox K Y).ncard : ℝ) := by rw [himgcard]
    _ ≤ 2 * (5 * (5 * Y + 1) ^ (d - 1)) := by linarith
    _ = 10 * (5 * Y + 1) ^ (d - 1) := by ring

/-- **Lemma 3.7** (`lem-ball-mult`, multiplicative lattice-point count), now PROVED:
`Y^{d-1}/(√d·R_K) ≤ |B^×(Y)| ≤ 10(5Y+1)^{d-1}` for totally real `K` of degree `d` and `Y ≥ 1`.
The lower bound is Blichfeldt in the unit lattice (`boxMult_card_ge`); the upper bound is the
`{±1}`-fibration over the packing bound (`boxMult_card_le`). The only analytic input is eq (3.1)
(`hensley_unitBox_volume`). -/
theorem lattice_count_mult (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ (d - 1) / (Real.sqrt d * NumberField.Units.regulator K) ≤ (boxMult K Y).card ∧
      ((boxMult K Y).card : ℝ) ≤ 10 * (5 * Y + 1) ^ (d - 1) :=
  ⟨boxMult_card_ge d hd Y hY, boxMult_card_le hd Y hY⟩

end SumProduct
