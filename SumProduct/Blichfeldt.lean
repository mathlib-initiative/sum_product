/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# An abstract Blichfeldt integral inequality

`volume S ≤ N · volume F` whenever every lattice translate of a measurable set `S` meets `S` at
most `N` times, with `F` a fundamental domain of the lattice.  This is the measure-theoretic core
shared by the lower bounds of Lemmas 3.5 and 3.7.
-/

open scoped NumberField
open Pointwise

namespace SumProduct

open MeasureTheory in
/-- **Blichfeldt integral inequality** (abstract). If every lattice translate of a measurable set
`S` is hit at most `N` times (`∑' ℓ, 𝟙_S(ℓ + y) ≤ N` for all `y`), then `vol S ≤ N · vol F` for a
fundamental domain `F` of the lattice `L`. This is the measure-theoretic core shared by the lower
bounds of Lemmas 3.5 and 3.7. -/
theorem volume_le_of_tsum_indicator_le {E : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    {L : Submodule ℤ E} [Countable ↥L] [MeasurableVAdd ↥L E] [VAddInvariantMeasure ↥L E volume]
    {F : Set E} (hF : IsAddFundamentalDomain (↥L) F volume) {S : Set E} (hSmeas : MeasurableSet S)
    {N : ℕ} (hbound : ∀ y : E,
      ∑' l : ↥L, S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ y) ≤ (N : ENNReal)) :
    volume S ≤ (N : ENNReal) * volume F := by
  set f : E → ENNReal := S.indicator (fun _ => 1) with hf
  have hfmeas : Measurable f := measurable_const.indicator hSmeas
  have hint : ∫⁻ y, f y = volume S := by rw [hf, lintegral_indicator hSmeas, setLIntegral_one]
  have hkey : volume S = ∑' l : ↥L, ∫⁻ y in F, f (l +ᵥ y) := by
    rw [← hint]; exact hF.lintegral_eq_tsum'' f
  have hdecomp : volume S = ∫⁻ y in F, ∑' l : ↥L, f (l +ᵥ y) := by
    rw [hkey]
    exact (lintegral_tsum fun l : ↥L => (hfmeas.comp (measurable_const_vadd l)).aemeasurable).symm
  rw [hdecomp]
  calc ∫⁻ y in F, ∑' l : ↥L, f (l +ᵥ y)
      ≤ ∫⁻ _ in F, (N : ENNReal) := lintegral_mono fun y => hbound y
    _ = (N : ENNReal) * volume F := by rw [setLIntegral_const]

end SumProduct
