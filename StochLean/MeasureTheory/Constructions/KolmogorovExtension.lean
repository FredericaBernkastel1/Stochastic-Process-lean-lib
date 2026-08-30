/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import KolmogorovExtension4.KolmogorovExtension
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Kolmogorov extension on standard Borel spaces

This file is the stable StochLean facade over the audited arbitrary-index construction from
`kolmogorov_extension4`.  Its public statements use only measurable-space-level
`StandardBorelSpace` assumptions.  The compatible Polish topologies installed by
`upgradeStandardBorel` are implementation details.

The constructor works for finite measures and for an arbitrary index type, including the empty
type.  Probability and uniqueness are obtained from Mathlib's canonical `IsProjectiveLimit` API.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  [∀ i, StandardBorelSpace (α i)]

/-- The arbitrary-index projective limit of a finite projective family on standard Borel
coordinate spaces.  No topology and no `Nonempty ι` assumption occurs in the public type. -/
noncomputable def projectiveLimitOfStandardBorel
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    Measure (∀ i, α i) := by
  letI := fun i ↦ upgradeStandardBorel (α i)
  exact projectiveLimit P hP

set_option linter.style.haveILetI false in
/-- Correctness of `projectiveLimitOfStandardBorel`: all prescribed finite-dimensional
marginals are recovered. -/
theorem isProjectiveLimit_projectiveLimitOfStandardBorel
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimitOfStandardBorel P hP) P := by
  letI := fun i ↦ upgradeStandardBorel (α i)
  exact isProjectiveLimit_projectiveLimit hP

instance projectiveLimitOfStandardBorel.instIsFiniteMeasure
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    IsFiniteMeasure (projectiveLimitOfStandardBorel P hP) :=
  (isProjectiveLimit_projectiveLimitOfStandardBorel P hP).isFiniteMeasure

/-- Probability preservation has no nonempty-index hypothesis; the empty marginal fixes the
total mass even when `ι` is empty. -/
instance projectiveLimitOfStandardBorel.instIsProbabilityMeasure
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsProbabilityMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    IsProbabilityMeasure (projectiveLimitOfStandardBorel P hP) :=
  (isProjectiveLimit_projectiveLimitOfStandardBorel P hP).isProbabilityMeasure

/-- The projective limit is uniquely characterized by its finite marginals. -/
theorem IsProjectiveLimit.eq_projectiveLimitOfStandardBorel
    {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P)
    {ν : Measure (∀ i, α i)} (hν : IsProjectiveLimit ν P) :
    ν = projectiveLimitOfStandardBorel P hP :=
  hν.unique (isProjectiveLimit_projectiveLimitOfStandardBorel P hP)

/-- Existence and uniqueness as a corollary of the single canonical constructor. -/
theorem existsUnique_isProjectiveLimit_of_standardBorel
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    ∃! ν : Measure (∀ i, α i), IsProjectiveLimit ν P := by
  refine ⟨projectiveLimitOfStandardBorel P hP,
    isProjectiveLimit_projectiveLimitOfStandardBorel P hP, ?_⟩
  intro ν hν
  exact hν.eq_projectiveLimitOfStandardBorel hP

/-- Finite-dimensional recovery for the raw coordinate process `fun i ω ↦ ω i` on the product
sample space.  No separate canonical-process structure is introduced. -/
theorem projectiveLimitOfStandardBorel_map_restrict
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) (J : Finset ι) :
    (projectiveLimitOfStandardBorel P hP).map J.restrict = P J :=
  isProjectiveLimit_projectiveLimitOfStandardBorel P hP J

end MeasureTheory
