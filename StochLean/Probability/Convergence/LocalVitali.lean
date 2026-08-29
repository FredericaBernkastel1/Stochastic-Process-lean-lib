/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureLocal
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Local Vitali convergence

This module applies Mathlib's finite-measure Vitali theorem on every measurable finite-measure
restriction. It is the local bridge appropriate for sigma-finite and more general ambient spaces.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E]

/-- Uniform integrability on every measurable set of finite measure. -/
def LocallyUnifIntegrable (f : ℕ → α → E) (p : ENNReal) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → UnifIntegrable f p (μ.restrict s)

/-- Local `Lᵖ` membership on every measurable set of finite measure. -/
def LocallyMemLp (g : α → E) (p : ENNReal) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → MemLp g p (μ.restrict s)

/-- Local convergence in measure plus local uniform integrability implies `Lᵖ` convergence on each
finite-measure restriction. -/
theorem TendstoLocallyInMeasure.tendsto_eLpNorm_restrict
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : LocallyMemLp g p μ) (hui : LocallyUnifIntegrable f p μ)
    (hfg : TendstoLocallyInMeasure μ f atTop g)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p (μ.restrict s)) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  exact tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n ↦ (hf n).restrict)
    (hg s hs hμs) (hui s hs hμs) (hfg s hs hμs)

end MeasureTheory
