/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Adapted

/-!
# Natural filtration minimality

Mathlib supplies the natural filtration and its adaptedness theorem. This file adds the thin
order-theoretic minimality bridge used by downstream stochastic-process APIs.
-/

@[expose] public section

open MeasureTheory TopologicalSpace

namespace MeasureTheory.Filtration

variable {Ω ι β : Type*} {m : MeasurableSpace Ω} [Preorder ι]
  [TopologicalSpace β] [MetrizableSpace β] [MeasurableSpace β] [BorelSpace β]

/-- The natural filtration is contained in every filtration to which the process is strongly
adapted. -/
theorem natural_le_of_stronglyAdapted
    (u : ι → Ω → β) (hu : ∀ i, StronglyMeasurable (u i))
    (ℱ : Filtration ι m) (hadapt : StronglyAdapted ℱ u) :
    Filtration.natural u hu ≤ ℱ := by
  intro i
  apply iSup₂_le
  intro j hji
  exact (hadapt.stronglyMeasurable_le hji).measurable.comap_le

end MeasureTheory.Filtration
