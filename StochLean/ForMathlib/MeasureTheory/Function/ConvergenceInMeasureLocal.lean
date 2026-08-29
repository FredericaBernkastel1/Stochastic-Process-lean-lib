/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Local convergence in measure

This file defines convergence in measure on every measurable set of finite measure. Unlike
`MeasureTheory.TendstoInMeasure`, this is the local notion used on sigma-finite spaces in Klenke,
Definition 6.2.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι κ E : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section EDist

variable [EDist E]

/-- `f` converges locally in `μ`-measure to `g` along `l` if it converges in measure after
restricting `μ` to every measurable set of finite measure. -/
def TendstoLocallyInMeasure (μ : Measure α) (f : ι → α → E) (l : Filter ι)
    (g : α → E) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → TendstoInMeasure (μ.restrict s) f l g

namespace TendstoInMeasure

/-- Global convergence in measure implies local convergence in measure. -/
theorem locally {f : ι → α → E} {l : Filter ι} {g : α → E}
    (h : TendstoInMeasure μ f l g) : TendstoLocallyInMeasure μ f l g := by
  intro s _hs _hμs ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ bot_le) (fun _ ↦ Measure.restrict_le_self _)

end TendstoInMeasure

namespace TendstoLocallyInMeasure

variable {f f' : ι → α → E} {l : Filter ι} {g g' : α → E}

/-- On a finite measure, local convergence in measure is the same as Mathlib's global notion. -/
theorem iff_tendstoInMeasure [IsFiniteMeasure μ] :
    TendstoLocallyInMeasure μ f l g ↔ TendstoInMeasure μ f l g := by
  constructor
  · intro h
    simpa only [Measure.restrict_univ] using h Set.univ MeasurableSet.univ (measure_ne_top μ _)
  · exact TendstoInMeasure.locally

/-- Local convergence is preserved when the indexing filter is strengthened. -/
theorem mono {v : Filter ι} (hvl : v ≤ l) (h : TendstoLocallyInMeasure μ f l g) :
    TendstoLocallyInMeasure μ f v g := by
  intro s hs hμs
  exact (h s hs hμs).mono hvl

/-- Local convergence is preserved by reindexing. -/
theorem comp {v : Filter κ} {ns : κ → ι} (h : TendstoLocallyInMeasure μ f l g)
    (hns : Tendsto ns v l) : TendstoLocallyInMeasure μ (f ∘ ns) v g := by
  intro s hs hμs
  exact (h s hs hμs).comp hns

/-- Local convergence depends only on the almost-everywhere classes of all functions involved. -/
theorem congr (hleft : ∀ i, f i =ᵐ[μ] f' i) (hright : g =ᵐ[μ] g')
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f' l g' := by
  intro s hs hμs
  apply (h s hs hμs).congr
  · intro i
    exact Measure.AbsolutelyContinuous.ae_eq Measure.restrict_le_self.absolutelyContinuous
      (hleft i)
  · exact Measure.AbsolutelyContinuous.ae_eq Measure.restrict_le_self.absolutelyContinuous hright

theorem congr_left (hleft : ∀ i, f i =ᵐ[μ] f' i)
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f' l g :=
  h.congr hleft EventuallyEq.rfl

theorem congr_right (hright : g =ᵐ[μ] g')
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f l g' :=
  h.congr (fun _ ↦ EventuallyEq.rfl) hright

end TendstoLocallyInMeasure

end EDist

section AlmostEverywhere

variable {f : ℕ → α → E} {g : α → E} [PseudoEMetricSpace E]

/-- Almost-everywhere convergence implies local convergence in measure, without assuming that the
ambient measure is finite. -/
theorem tendstoLocallyInMeasure_of_tendsto_ae
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    TendstoLocallyInMeasure μ f atTop g := by
  intro s _hs hμs
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  exact tendstoInMeasure_of_tendsto_ae (fun n ↦ (hf n).restrict) (ae_restrict_of_ae hfg)

end AlmostEverywhere

end MeasureTheory
