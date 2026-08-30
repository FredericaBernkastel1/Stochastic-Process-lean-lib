/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Complete and usual filtrations

Right continuity and completeness are kept as separate requirements. In particular, applying
`Filtration.rightCont` does not manufacture subsets of null sets in the initial sigma-algebra.
This file defines the property only; a completed right-continuation must change to the genuinely
completed measurable-space/measure setting and is deliberately not faked on the same ambient
space.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- A sub-sigma-algebra is complete for `P` relative to the ambient probability space when it
contains every `P`-null subset of the ambient space. For the initial sigma-algebra of a usual
filtration this is the standard, stronger requirement: the null set need not already belong to
the smaller sigma-algebra. -/
def IsCompleteSubMeasurableSpace (P : Measure Ω) (m' : MeasurableSpace Ω) : Prop :=
  ∀ s, P s = 0 → MeasurableSet[m'] s

namespace IsCompleteSubMeasurableSpace

variable {P : Measure Ω} {m' : MeasurableSpace Ω}

theorem mono_null (h : IsCompleteSubMeasurableSpace P m')
    {s t : Set Ω} (hs0 : P s = 0) (hts : t ⊆ s) :
    MeasurableSet[m'] t :=
  h t (measure_mono_null hts hs0)

theorem ambient [P.IsComplete] : IsCompleteSubMeasurableSpace P m := by
  intro s hs
  exact measurableSet_of_null hs

end IsCompleteSubMeasurableSpace

namespace Filtration

variable [PartialOrder ι] [OrderBot ι]

/-- The usual conditions: right continuity together with `P`-completeness of the initial
sigma-algebra. Neither conjunct is silently inferred from the other. -/
def IsUsual (ℱ : Filtration ι m) (P : Measure Ω) : Prop :=
  ℱ.IsRightContinuous ∧ IsCompleteSubMeasurableSpace P (ℱ ⊥)

namespace IsUsual

variable {ℱ : Filtration ι m} {P : Measure Ω}

theorem rightContinuous (h : IsUsual ℱ P) : ℱ.IsRightContinuous :=
  h.1

theorem complete_initial (h : IsUsual ℱ P) :
    IsCompleteSubMeasurableSpace P (ℱ ⊥) :=
  h.2

end IsUsual

/-- A right-continuous filtration whose initial sigma-algebra is not complete is not usual. This
is the semantic guard preventing `rightCont` from being mistaken for usual augmentation. -/
theorem not_isUsual_of_not_complete_initial {ℱ : Filtration ι m} {P : Measure Ω}
    (h : ¬ IsCompleteSubMeasurableSpace P (ℱ ⊥)) : ¬ IsUsual ℱ P :=
  fun hu ↦ h hu.complete_initial

end Filtration

end MeasureTheory
