/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Comparator challenge for the headline theorem

This is the trusted challenge side for `leanprover/comparator`.  It imports only Mathlib, states the
single classical hypothesis explicitly, and gives the reviewed theorem statement with a placeholder
proof.
-/

open scoped NumberField
open Pointwise

/-- **Theorem 3.2** (Martinet), as an explicit hypothesis.

There is an absolute constant `C > 0` such that for infinitely many degrees `d` there is a
totally real number field `K` of degree `d` over `ℚ` whose discriminant satisfies `Δ_K ≤ C^d`.

"Infinitely many `d`" is expressed as: for every `N` there is a degree `d ≥ N` that works. -/
def MartinetTotallyRealTowers : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d

/-- Trusted comparator challenge statement for the headline theorem. -/
theorem sumProduct_false (hMartinet : MartinetTotallyRealTowers) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ A : Finset ℝ, N ≤ A.card ∧
      ((max (A + A).card (A * A).card : ℕ) : ℝ) ≤ (A.card : ℝ) ^ (2 - c) := by
  sorry
