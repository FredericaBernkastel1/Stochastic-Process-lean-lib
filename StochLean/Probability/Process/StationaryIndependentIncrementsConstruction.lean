/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

/-
The ordered-time enumeration and cumulative-increment map below were independently adapted to
StochLean's SII construction after auditing Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, file
`Probability/Independence/Process/HasIndepIncrements/IsGaussianProcess.lean`
(Apache-2.0).  The Mathlib declarations are implementation-private; this module owns project-local
names and does not depend on any package other than Mathlib.
-/

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import StochLean.MeasureTheory.Constructions.KolmogorovExtension
public import StochLean.Probability.Process.StationaryIndependentIncrements

/-!
# Coordinate construction for stationary independent increments

Finite-dimensional candidate laws are obtained by taking independent laws for the chronologically
ordered gaps and mapping their cumulative sums to positions.  This module deliberately constructs
only the coordinate-product law; it asserts no path regularity.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.SIIConstruction

/-- Chronological enumeration of a finite nonnegative-time set with an extra initial zero. -/
noncomputable def orderedTimeWithZero (I : Finset ℝ≥0) (i : Fin (#I + 1)) : ℝ≥0 :=
  if h : i = 0 then 0 else I.orderEmbOfFin rfl (i.pred h)

@[simp]
theorem orderedTimeWithZero_zero (I : Finset ℝ≥0) : orderedTimeWithZero I 0 = 0 := rfl

theorem orderedTimeWithZero_of_ne_zero (I : Finset ℝ≥0) (i : Fin (#I + 1)) (hi : i ≠ 0) :
    orderedTimeWithZero I i = I.orderEmbOfFin rfl (i.pred hi) := by
  rw [orderedTimeWithZero, dif_neg hi]

@[simp]
theorem orderedTimeWithZero_succ (I : Finset ℝ≥0) (i : Fin #I) :
    orderedTimeWithZero I i.succ = I.orderEmbOfFin rfl i := by
  rw [orderedTimeWithZero_of_ne_zero, Fin.pred_succ]
  simp

theorem monotone_orderedTimeWithZero (I : Finset ℝ≥0) :
    Monotone (orderedTimeWithZero I) := by
  intro i j hij
  obtain rfl | hi := eq_or_ne i 0
  · simp
  rw [orderedTimeWithZero_of_ne_zero I i hi,
    orderedTimeWithZero_of_ne_zero I j (by grind)]
  exact OrderEmbedding.monotone _ (by simpa)

/-- Length of the `i`th chronological gap, including the first gap from zero. -/
noncomputable def orderedGap (I : Finset ℝ≥0) (i : Fin #I) : ℝ≥0 :=
  orderedTimeWithZero I i.succ - orderedTimeWithZero I i.castSucc

/-- Convert chronological increments into positions at the times in `I`. -/
noncomputable def incrementsToPositions (I : Finset ℝ≥0) :
    (Fin #I → ℝ) → (I → ℝ) :=
  fun x i => ∑ j ≤ (I.orderIsoOfFin rfl).symm i, x j

theorem measurable_incrementsToPositions (I : Finset ℝ≥0) :
    Measurable (incrementsToPositions I) := by
  rw [measurable_pi_iff]
  intro i
  exact Finset.measurable_sum _ fun j _ => measurable_pi_apply j

/-- Product law of the independent increments over the chronological gaps of `I`. -/
noncomputable def incrementProduct
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) : Measure (Fin #I → ℝ) :=
  Measure.pi fun i => (ν (orderedGap I i) : Measure ℝ)

instance incrementProduct.instIsProbabilityMeasure
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (incrementProduct ν I) := by
  unfold incrementProduct
  infer_instance

instance incrementProduct.instIsFiniteMeasure
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) :
    IsFiniteMeasure (incrementProduct ν I) := by infer_instance

/-- Finite-dimensional position law obtained from independent chronological increments. -/
noncomputable def finitePositionLaw
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  (incrementProduct ν I).map (incrementsToPositions I)

instance finitePositionLaw.instIsProbabilityMeasure
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (finitePositionLaw ν I) := by
  unfold finitePositionLaw
  exact Measure.isProbabilityMeasure_map (measurable_incrementsToPositions I).aemeasurable

instance finitePositionLaw.instIsFiniteMeasure
    (ν : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) :
    IsFiniteMeasure (finitePositionLaw ν I) := by infer_instance

section ProjectiveLimit

variable (ν : ℝ≥0 → ProbabilityMeasure ℝ)
  (hν : IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => ℝ) (finitePositionLaw ν))

/-- Coordinate-product probability measure associated with a proved-consistent SII finite-law
family.  Projective consistency is kept as a separate proof obligation rather than hidden in data. -/
noncomputable def coordinateMeasure : Measure (ℝ≥0 → ℝ) :=
  projectiveLimitOfStandardBorel (α := fun _ : ℝ≥0 => ℝ) (finitePositionLaw ν) hν

instance coordinateMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure (coordinateMeasure ν hν) := by
  unfold coordinateMeasure
  infer_instance

instance coordinateMeasure.instIsFiniteMeasure :
    IsFiniteMeasure (coordinateMeasure ν hν) := by infer_instance

/-- Raw coordinate process on the Kolmogorov product space. -/
def coordinateProcess (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω t

@[fun_prop]
theorem measurable_coordinateProcess (t : ℝ≥0) : Measurable (coordinateProcess t) :=
  measurable_pi_apply t

/-- The coordinate process recovers every prescribed finite-dimensional position law. -/
theorem hasLaw_restrict (I : Finset ℝ≥0) :
    HasLaw I.restrict (finitePositionLaw ν I) (coordinateMeasure ν hν) := by
  refine ⟨(Finset.measurable_restrict I).aemeasurable, ?_⟩
  exact projectiveLimitOfStandardBorel_map_restrict
    (α := fun _ : ℝ≥0 => ℝ) (finitePositionLaw ν) hν I

end ProjectiveLimit

end ProbabilityTheory.SIIConstruction
