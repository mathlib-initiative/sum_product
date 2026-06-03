/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The additive, multiplicative and logarithmic boxes

Definitions and elementary properties of the boxes used throughout:
* `boxAdd K X = B⁺(X)` — algebraic integers with every place `≤ X`;
* `boxMult K Y = B^×(Y)` — units with every `|log w(u)| ≤ Y`;
* `unitBox K r` — the region of `logSpace K` corresponding to `B^×(r)` under `logEmbedding`.
Includes box arithmetic (`boxAdd_add`, `boxMult_mul`), the membership/measurability lemmas, and
the key identity `u ∈ B^×(Y) ↔ logEmbedding u ∈ unitBox K Y`.
-/

open scoped NumberField
open Pointwise

namespace SumProduct

/-- The additive box `B⁺(X) = {α ∈ 𝒪_K : w(α) ≤ X for every infinite place w}`
(i.e. all archimedean absolute values of `α` are `≤ X`). -/
def boxAddSet (K : Type*) [Field K] [NumberField K] (X : ℝ) : Set (𝓞 K) :=
  {α | ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X}

theorem boxAddSet_finite (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    (boxAddSet K X).Finite := by
  refine Set.Finite.of_finite_image (f := fun α : 𝓞 K => (α : K)) ?_
    (fun a _ b _ hab => NumberField.RingOfIntegers.coe_injective hab)
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ X).subset ?_
  rintro x ⟨α, hα, rfl⟩
  exact ⟨NumberField.RingOfIntegers.isIntegral_coe α, fun φ => by
    rw [← NumberField.InfinitePlace.apply φ]; exact hα (NumberField.InfinitePlace.mk φ)⟩

/-- The additive box `B⁺(X)` as a `Finset`. -/
noncomputable def boxAdd (K : Type*) [Field K] [NumberField K] (X : ℝ) : Finset (𝓞 K) :=
  (boxAddSet_finite K X).toFinset

@[simp] theorem mem_boxAdd {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : NumberField.InfinitePlace K, w (α : K) ≤ X :=
  Set.Finite.mem_toFinset _

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace in
/-- `B⁺(X)` is the pullback under the mixed embedding of the box `{x : ∀ w, normAtPlace w x ≤ X}`
in `mixedSpace K`. This connects `boxAdd` to Mathlib's `integerLattice` (whose covolume is
`√|Δ_K|`), the route for the Lemma 3.5 lower bound. -/
theorem mem_boxAdd_iff_normAtPlace {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (α : K)) ≤ X := by
  rw [mem_boxAdd]; simp only [normAtPlace_apply]

/-- The multiplicative box `B^×(Y) = {u ∈ 𝒪_K^× : |log w(u)| ≤ Y for every infinite place w}`,
a box in the unit (logarithmic) lattice. -/
def boxMultSet (K : Type*) [Field K] [NumberField K] (Y : ℝ) : Set (𝓞 K)ˣ :=
  {u | ∀ w : NumberField.InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K))| ≤ Y}

theorem boxMultSet_finite (K : Type*) [Field K] [NumberField K] (Y : ℝ) :
    (boxMultSet K Y).Finite := by
  refine Set.Finite.of_finite_image (f := fun u : (𝓞 K)ˣ => ((u : 𝓞 K) : K)) ?_
    (fun a _ b _ hab => Units.ext (NumberField.RingOfIntegers.coe_injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ (Real.exp Y)).subset ?_
  rintro x ⟨u, hu, rfl⟩
  refine ⟨NumberField.RingOfIntegers.isIntegral_coe _, fun φ => ?_⟩
  rw [← NumberField.InfinitePlace.apply φ]
  have hpos : 0 < (NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K) :=
    NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)
  have hlog : Real.log ((NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K)) ≤ Y :=
    le_trans (le_abs_self _) (hu (NumberField.InfinitePlace.mk φ))
  calc (NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K)
      = Real.exp (Real.log ((NumberField.InfinitePlace.mk φ) ((u : 𝓞 K) : K))) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp Y := Real.exp_le_exp.mpr hlog

/-- The multiplicative box `B^×(Y)` as a `Finset`. -/
noncomputable def boxMult (K : Type*) [Field K] [NumberField K] (Y : ℝ) : Finset (𝓞 K)ˣ :=
  (boxMultSet_finite K Y).toFinset

@[simp] theorem mem_boxMult {K : Type*} [Field K] [NumberField K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    u ∈ boxMult K Y ↔ ∀ w : NumberField.InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K))| ≤ Y :=
  Set.Finite.mem_toFinset _

/-- Additive boxes add: `B⁺(X) + B⁺(Y) ⊆ B⁺(X+Y)` (the triangle inequality for places).
Used for the sumset bound `A + A ⊆ B⁺(4Xe^Y)` in Lemma 4.1. -/
theorem boxAdd_add {K : Type*} [Field K] [NumberField K] {X Y : ℝ} {α β : 𝓞 K}
    (ha : α ∈ boxAdd K X) (hb : β ∈ boxAdd K Y) : α + β ∈ boxAdd K (X + Y) := by
  rw [mem_boxAdd] at ha hb ⊢
  intro w
  have he : ((α + β : 𝓞 K) : K) = (α : K) + (β : K) := by push_cast; ring
  rw [he]
  exact le_trans (w.1.add_le _ _) (add_le_add (ha w) (hb w))

/-- Multiplicative boxes multiply: `B^×(Y) · B^×(Y') ⊆ B^×(Y+Y')` (logarithms add).
Used for the small-doubling bound `G·G ⊆ B^×(2Y)` in Lemma 4.1. -/
theorem boxMult_mul {K : Type*} [Field K] [NumberField K] {Y Y' : ℝ} {u v : (𝓞 K)ˣ}
    (hu : u ∈ boxMult K Y) (hv : v ∈ boxMult K Y') : u * v ∈ boxMult K (Y + Y') := by
  rw [mem_boxMult] at hu hv ⊢
  intro w
  have hu0 : w ((u : 𝓞 K) : K) ≠ 0 :=
    ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u))
  have hv0 : w ((v : 𝓞 K) : K) ≠ 0 :=
    ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero v))
  have he : ((↑(u * v) : 𝓞 K) : K) = ((u : 𝓞 K) : K) * ((v : 𝓞 K) : K) := by push_cast; ring
  rw [he, map_mul, Real.log_mul hu0 hv0]
  calc |Real.log (w ((u : 𝓞 K) : K)) + Real.log (w ((v : 𝓞 K) : K))|
      ≤ |Real.log (w ((u : 𝓞 K) : K))| + |Real.log (w ((v : 𝓞 K) : K))| := abs_add_le _ _
    _ ≤ Y + Y' := add_le_add (hu w) (hv w)

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace in
/-- The region in `logSpace K` (`≅ ℝ^{d-1}`) corresponding to `B^×(r)` under `logEmbedding`:
the dropped coordinate `w₀` reappears as the sum constraint, because
`∑_w log w(u) = log |N(u)| = 0`, so `|log w₀(u)| = |∑_{w ≠ w₀} log w(u)|`. -/
def unitBox (K : Type*) [Field K] [NumberField K] (r : ℝ) : Set (logSpace K) :=
  {y | (∀ w, |y w| ≤ r) ∧ |∑ w, y w| ≤ r}

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace in
/-- For totally real `K`, a unit lies in `B^×(Y)` iff its log-embedding lies in `unitBox K Y`. -/
theorem logEmbedding_mem_unitBox_iff {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul u) ∈ unitBox K Y ↔ u ∈ boxMult K Y := by
  have hcomp : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      logEmbedding K (Additive.ofMul u) w = Real.log (w.val ((u : 𝓞 K) : K)) := by
    intro w
    rw [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul]
  have hsum : ∑ w, logEmbedding K (Additive.ofMul u) w
      = -Real.log ((w₀ : InfinitePlace K) ((u : 𝓞 K) : K)) := by
    rw [sum_logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one]; ring
  rw [mem_boxMult, unitBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w = w₀
    · subst hw
      rw [hsum, abs_neg] at h2
      exact h2
    · rw [← hcomp ⟨w, hw⟩]
      exact h1 ⟨w, hw⟩
  · intro h
    refine ⟨fun w => ?_, ?_⟩
    · rw [hcomp w]
      exact h w.val
    · rw [hsum, abs_neg]
      exact h w₀

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- Differences of `unitBox` points add radii: `unitBox a − unitBox b ⊆ unitBox (a+b)`. -/
theorem sub_mem_unitBox {K : Type*} [Field K] [NumberField K] {y z : logSpace K} {a b : ℝ}
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y - z ∈ unitBox K (a + b) := by
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun w => ?_, ?_⟩
  · rw [Pi.sub_apply, sub_eq_add_neg]
    calc |y w + -z w| ≤ |y w| + |(-z w)| := abs_add_le _ _
      _ = |y w| + |z w| := by rw [abs_neg]
      _ ≤ a + b := add_le_add (hy1 w) (hz1 w)
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [sub_eq_add_neg]
    calc |(∑ w, y w) + -(∑ w, z w)| ≤ |∑ w, y w| + |(-(∑ w, z w))| := abs_add_le _ _
      _ = |∑ w, y w| + |∑ w, z w| := by rw [abs_neg]
      _ ≤ a + b := add_le_add hy2 hz2

open scoped Classical in
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- Sums of `unitBox` points add radii: `unitBox a + unitBox b ⊆ unitBox (a+b)`. -/
theorem add_mem_unitBox {K : Type*} [Field K] [NumberField K] {y z : logSpace K} {a b : ℝ}
    (hy : y ∈ unitBox K a) (hz : z ∈ unitBox K b) : y + z ∈ unitBox K (a + b) := by
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun w => ?_, ?_⟩
  · calc |(y + z) w| = |y w + z w| := by rw [Pi.add_apply]
      _ ≤ |y w| + |z w| := abs_add_le _ _
      _ ≤ a + b := add_le_add (hy1 w) (hz1 w)
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    calc |(∑ w, y w) + ∑ w, z w| ≤ |∑ w, y w| + |∑ w, z w| := abs_add_le _ _
      _ ≤ a + b := add_le_add hy2 hz2

open scoped Classical in
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- `unitBox K r` is measurable (it is closed). -/
theorem measurableSet_unitBox {K : Type*} [Field K] [NumberField K] (r : ℝ) :
    MeasurableSet (unitBox K r) := by
  rw [unitBox, Set.setOf_and]
  refine (IsClosed.inter ?_ ?_).measurableSet
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun w =>
      isClosed_le (continuous_abs.comp (continuous_apply w)) continuous_const
  · exact isClosed_le
      (continuous_abs.comp (continuous_finsetSum _ fun w _ => continuous_apply w)) continuous_const

end SumProduct
