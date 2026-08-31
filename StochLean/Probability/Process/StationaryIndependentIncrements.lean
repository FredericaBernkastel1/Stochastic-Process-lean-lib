/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import StochLean.Probability.InfinitelyDivisible.Basic
public import StochLean.Probability.Process.StationaryIncrements

/-!
# Processes with stationary independent increments

This file joins Mathlib's independent-increment predicate with StochLean's stationary-increment
predicate.  The associated law family remains a separate datum so that process semantics and
law-level convolution semantics are not conflated.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- Stationary independent increments, with neither a time-zero normalization nor path regularity
silently included. -/
def HasStationaryIndependentIncrements {T : Type*} [Preorder T] [AddMonoid T] [Sub E]
    (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  HasStationaryIncrements X P ∧ HasIndepIncrements X P

namespace HasStationaryIndependentIncrements

variable {T : Type*} [Preorder T] [AddMonoid T] [Sub E]
  {X : T → Ω → E} {P : Measure Ω}

theorem stationaryIncrements (hX : HasStationaryIndependentIncrements X P) :
    HasStationaryIncrements X P := hX.1

theorem indepIncrements (hX : HasStationaryIndependentIncrements X P) :
    HasIndepIncrements X P := hX.2

end HasStationaryIndependentIncrements

section LawFamily

variable [AddCommGroup E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {P : Measure Ω} {ν : ℝ≥0 → ProbabilityMeasure E}

/-- `ν t` is the law of the increment from time zero to time `t`. -/
def HasIncrementLawFamily (X : ℝ≥0 → Ω → E) (ν : ℝ≥0 → ProbabilityMeasure E)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ t, HasLaw (fun ω ↦ X t ω - X 0 ω) (ν t) P

omit [MeasurableAdd₂ E] in
theorem HasIncrementLawFamily.hasLaw (hν : HasIncrementLawFamily X ν P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ X t ω - X 0 ω) (ν t) P := hν t

/-- The increment laws of an SII process form a convolution semigroup.  The proof uses the
stationary law of the later increment, Mathlib's two-increment independence theorem, and the
telescoping identity. -/
theorem HasStationaryIndependentIncrements.isConvolutionSemigroup
    (hX : HasStationaryIndependentIncrements X P) (hν : HasIncrementLawFamily X ν P) :
    IsConvolutionSemigroup ν := by
  intro s t
  have hfirst : HasLaw (fun ω ↦ X s ω - X 0 ω) (ν s) P := hν s
  have hlater : HasLaw (fun ω ↦ X (s + t) ω - X s ω) (ν t) P :=
    (hX.stationaryIncrements s t).symm.hasLaw (hν t)
  have hindep :
      (fun ω ↦ X s ω - X 0 ω) ⟂ᵢ[P] (fun ω ↦ X (s + t) ω - X s ω) :=
    hX.indepIncrements.indepFun_sub_sub (by simp) (by simp)
  have hsum : HasLaw
      (fun ω ↦ (X s ω - X 0 ω) + (X (s + t) ω - X s ω))
      ((ν s : Measure E) ∗ (ν t : Measure E)) P :=
    hindep.hasLaw_fun_add hfirst hlater
  have htel : (fun ω ↦ (X s ω - X 0 ω) + (X (s + t) ω - X s ω)) =
      (fun ω ↦ X (s + t) ω - X 0 ω) := by
    funext ω
    abel
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.coe_conv]
  exact (hν (s + t)).map_eq.symm.trans (htel ▸ hsum.map_eq)

/-- Consequently every increment marginal of an SII process is infinitely divisible. -/
theorem HasStationaryIndependentIncrements.incrementLaw_isInfinitelyDivisible
    (hX : HasStationaryIndependentIncrements X P) (hν : HasIncrementLawFamily X ν P)
    (t : ℝ≥0) : ProbabilityMeasure.IsInfinitelyDivisible (ν t) :=
  (hX.isConvolutionSemigroup hν).isInfinitelyDivisible t

end LawFamily

end ProbabilityTheory
