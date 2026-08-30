/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Vague convergence of locally finite measures

Mathlib's probability-measure topology already owns weak convergence.  This file fills the
distinct locally-finite-measure gap: vague convergence is convergence against real-valued
compactly supported continuous test functions.  Local finiteness is part of the predicate, so the
Bochner integral is never being used through its non-integrable fallback convention.
-/

@[expose] public section

open CompactlySupported Filter Set
open scoped Topology

namespace MeasureTheory

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Vague convergence of locally finite measures, tested by `C_c(X, ℝ)`. -/
def TendstoVaguely (μ : ι → Measure X) (l : Filter ι) (ν : Measure X) : Prop :=
  (∀ i, IsFiniteMeasureOnCompacts (μ i)) ∧ IsFiniteMeasureOnCompacts ν ∧
    ∀ f : C_c(X, ℝ),
      Tendsto (fun i ↦ ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν))

namespace TendstoVaguely

omit [OpensMeasurableSpace X] in
theorem finiteOnCompacts_left {μ : ι → Measure X} {l : Filter ι} {ν : Measure X}
    (h : TendstoVaguely μ l ν) (i : ι) : IsFiniteMeasureOnCompacts (μ i) :=
  h.1 i

omit [OpensMeasurableSpace X] in
theorem finiteOnCompacts_right {μ : ι → Measure X} {l : Filter ι} {ν : Measure X}
    (h : TendstoVaguely μ l ν) : IsFiniteMeasureOnCompacts ν :=
  h.2.1

omit [OpensMeasurableSpace X] in
theorem integral_tendsto {μ : ι → Measure X} {l : Filter ι} {ν : Measure X}
    (h : TendstoVaguely μ l ν) (f : C_c(X, ℝ)) :
    Tendsto (fun i ↦ ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)) :=
  h.2.2 f

end TendstoVaguely

omit [OpensMeasurableSpace X] in
private theorem finiteMeasure_finiteOnCompacts (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ where
  lt_top_of_isCompact := fun _ _ ↦ measure_lt_top μ _

/-- Ordinary weak convergence of probability measures implies vague convergence of their
underlying measures.  This bridge does not define a second weak-convergence predicate. -/
theorem ProbabilityMeasure.tendstoVaguely_of_tendsto
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} {l : Filter ι}
    (h : Tendsto μ l (𝓝 ν)) :
    TendstoVaguely (fun i ↦ (μ i : Measure X)) l (ν : Measure X) := by
  refine ⟨fun i ↦ finiteMeasure_finiteOnCompacts (μ i : Measure X),
    finiteMeasure_finiteOnCompacts (ν : Measure X), fun f ↦ ?_⟩
  simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h)
      f.toBoundedContinuousFunction

/-- On a compact space every continuous test function has compact support, so vague and ordinary
weak convergence of probability measures agree. -/
theorem ProbabilityMeasure.tendsto_iff_tendstoVaguely [CompactSpace X]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} {l : Filter ι} :
    Tendsto μ l (nhds ν) ↔
      TendstoVaguely (fun i ↦ (μ i : Measure X)) l (ν : Measure X) := by
  constructor
  · exact ProbabilityMeasure.tendstoVaguely_of_tendsto
  · intro h
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    let g : C_c(X, ℝ) :=
      CompactlySupportedContinuousMap.continuousMapEquiv f.toContinuousMap
    simpa [g] using h.integral_tendsto g

/-- Dirac masses escaping every compact set converge vaguely to the zero measure. -/
theorem tendstoVaguely_dirac_zero_of_tendsto_cocompact
    {x : ι → X} {l : Filter ι} (hx : Tendsto x l (cocompact X)) :
    TendstoVaguely (fun i ↦ Measure.dirac (x i)) l 0 := by
  refine ⟨fun i ↦ finiteMeasure_finiteOnCompacts (Measure.dirac (x i)),
    finiteMeasure_finiteOnCompacts (0 : Measure X), fun f ↦ ?_⟩
  simp_rw [integral_dirac' f _ f.continuous.stronglyMeasurable, integral_zero_measure]
  convert (zero_at_infty f).comp hx using 1
  funext i
  rfl

end MeasureTheory
