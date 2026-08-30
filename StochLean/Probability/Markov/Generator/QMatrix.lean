/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Transition
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Q-matrices

The foundational predicate is summability-based and intentionally has no countability assumption on
the state space.  Positivity is imposed only off the diagonal; the diagonal is the negative total
exit rate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

/-- A conservative Q-matrix. -/
structure IsQMatrix {E : Type*} (q : E → E → ℝ) : Prop where
  offDiag_nonneg : ∀ x y, x ≠ y → 0 ≤ q x y
  summable_offDiag : ∀ x, Summable (fun y : {y : E // y ≠ x} => q x y)
  diagonal_eq : ∀ x, q x x = -∑' y : {y : E // y ≠ x}, q x y

/-- Total rate of leaving a state. -/
def exitRate {E : Type*} (q : E → E → ℝ) (x : E) : ℝ :=
  -q x x

namespace IsQMatrix

variable {E : Type*} {q : E → E → ℝ}

/-- Exit rates are the sums of the off-diagonal rows. -/
theorem exitRate_eq_tsum (hq : IsQMatrix q) (x : E) :
    exitRate q x = ∑' y : {y : E // y ≠ x}, q x y := by
  rw [exitRate, hq.diagonal_eq]
  simp

/-- Exit rates are nonnegative. -/
theorem exitRate_nonneg (hq : IsQMatrix q) (x : E) : 0 ≤ exitRate q x := by
  rw [hq.exitRate_eq_tsum]
  exact tsum_nonneg fun y => hq.offDiag_nonneg x y y.property.symm

/-- Q-matrix diagonal entries are nonpositive. -/
theorem diagonal_nonpos (hq : IsQMatrix q) (x : E) : q x x ≤ 0 := by
  simpa only [exitRate, neg_nonneg] using hq.exitRate_nonneg x

/-- Every off-diagonal row has finite real sum. -/
theorem summable_div_exitBound (hq : IsQMatrix q) (x : E) (c : ℝ) :
    Summable (fun y : {y : E // y ≠ x} => q x y / c) :=
  (hq.summable_offDiag x).div_const c

end IsQMatrix

/-- The zero rate matrix is a Q-matrix. -/
theorem isQMatrix_zero {E : Type*} : IsQMatrix (fun _ _ : E => 0) where
  offDiag_nonneg := by simp
  summable_offDiag := by intro; simp
  diagonal_eq := by intro; simp

/-- Right-derivative relation between a nonnegative-time transition family and a Q-matrix. -/
def HasQMatrix {E : Type*} [MeasurableSpace E]
    (κ : ℝ≥0 → Kernel E E) (q : E → E → ℝ) : Prop :=
  ∀ x y, HasDerivWithinAt
    (fun t : ℝ => transitionProbability (κ t.toNNReal) x {y})
    (q x y) (Set.Ici 0) 0

/-- A transition family has at most one Q-matrix: right derivatives on the nonnegative half-line
are unique. -/
theorem HasQMatrix.eq {E : Type*} [MeasurableSpace E]
    {κ : ℝ≥0 → Kernel E E} {q r : E → E → ℝ}
    (hq : HasQMatrix κ q) (hr : HasQMatrix κ r) : q = r := by
  funext x y
  exact (uniqueDiffOn_Ici 0 0 Set.self_mem_Ici).eq_deriv _ (hq x y) (hr x y)

end ProbabilityTheory
