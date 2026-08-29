/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import StochLean.Probability.Process.Path.RightContinuous
public import StochLean.Probability.Process.StationaryIncrements

/-!
# Poisson processes

The predicate below packages the standard counting-process requirements without introducing a
new process type. Path properties use one common almost-sure event, and increment laws are only
asserted for ordered times, where natural subtraction represents an actual count increment.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A rate-`rate` Poisson process on nonnegative real time. -/
structure IsPoissonProcess (X : NNReal → Ω → ℕ) (rate : NNReal)
    (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] : Prop where
  aemeasurable : ∀ t, AEMeasurable (X t) P
  initial : X 0 =ᵐ[P] fun _ ↦ 0
  monotonePaths : HasMonotonePaths X P
  rightContinuousPaths : HasRightContinuousPaths X P
  indepIncrements : HasIndepIncrements X P
  incrementLaw : ∀ s t, s ≤ t →
    HasLaw (fun ω ↦ X t ω - X s ω) (poissonMeasure (rate * (t - s))) P

namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Every one-time marginal of a Poisson process has the expected Poisson law. -/
theorem hasLaw (hX : IsPoissonProcess X rate P) (t : NNReal) :
    HasLaw (X t) (poissonMeasure (rate * t)) P := by
  have hinc := hX.incrementLaw 0 t bot_le
  have heq : X t =ᵐ[P] fun ω ↦ X t ω - X 0 ω := by
    filter_upwards [hX.initial] with ω hω
    simp only [hω, Nat.sub_zero]
  simpa only [tsub_zero] using hinc.congr heq

/-- Poisson increment laws imply stationary increments. -/
theorem hasStationaryIncrements (hX : IsPoissonProcess X rate P) :
    HasStationaryIncrements X P := by
  intro s t
  have h₁ := hX.incrementLaw s (s + t) (by exact le_add_right (le_refl s))
  have h₂ := hX.incrementLaw 0 t bot_le
  have h₁' : HasLaw (fun ω ↦ X (s + t) ω - X s ω)
      (poissonMeasure (rate * t)) P := by
    simpa only [add_tsub_cancel_left] using h₁
  have h₂' : HasLaw (fun ω ↦ X t ω - X 0 ω) (poissonMeasure (rate * t)) P := by
    simpa only [tsub_zero] using h₂
  exact h₁'.identDistrib h₂'

end IsPoissonProcess

end ProbabilityTheory
