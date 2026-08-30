/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Continuous mapping at almost every limit point

Mathlib already provides the globally continuous mapping theorem.  This file adds the exact
Portmanteau bridge needed when a measurable map is continuous only almost everywhere under the
limit law.  Positive mass at discontinuity points is deliberately excluded by the hypothesis.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MeasureTheory

private theorem closure_preimage_isClosed_subset_union_not_continuousAt
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (g : E → F) {C : Set F} (hC : IsClosed C) :
    closure (g ⁻¹' C) ⊆ g ⁻¹' C ∪ {x | ¬ ContinuousAt g x} := by
  intro x hx
  by_cases hg : ContinuousAt g x
  · left
    change g x ∈ C
    have hmem : g x ∈ closure C :=
      hg.continuousWithinAt.mem_closure hx (mapsTo_preimage g C)
    simpa only [hC.closure_eq] using hmem
  · exact Or.inr hg

/-- Mapping theorem for a measurable map whose discontinuity set has zero mass under the limit
law.  Weak convergence remains ordinary `Tendsto` in Mathlib's `ProbabilityMeasure` topology. -/
theorem ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    {ι E F : Type*} {l : Filter ι}
    [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
    [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hμ : Tendsto μ l (𝓝 ν)) {g : E → F} (hg : Measurable g)
    (hcont : (ν : Measure E) {x | ¬ ContinuousAt g x} = 0) :
    Tendsto (fun i ↦ (μ i).map hg.aemeasurable) l
      (𝓝 (ν.map hg.aemeasurable)) := by
  refine tendsto_of_forall_isClosed_limsup_le' fun C hC ↦ ?_
  simp_rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hg hC.measurableSet]
  let A : Set E := g ⁻¹' C
  calc
    limsup (fun i ↦ (μ i : Measure E) A) l
        ≤ limsup (fun i ↦ (μ i : Measure E) (closure A)) l :=
      Filter.limsup_le_limsup (.of_forall fun i ↦ measure_mono subset_closure)
        (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ (ν : Measure E) (closure A) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ ≤ (ν : Measure E) (A ∪ {x | ¬ ContinuousAt g x}) :=
      measure_mono (closure_preimage_isClosed_subset_union_not_continuousAt g hC)
    _ ≤ (ν : Measure E) A + (ν : Measure E) {x | ¬ ContinuousAt g x} :=
      measure_union_le _ _
    _ = (ν : Measure E) A := by rw [hcont, add_zero]

end MeasureTheory
