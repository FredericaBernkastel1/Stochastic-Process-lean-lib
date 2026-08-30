/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Transporting densities through measure-preserving equivalences

This is a generic change-of-coordinates bridge for measures with density.
-/

@[expose] public section

open Function
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- A measure-preserving measurable equivalence transports a density by composition with its
inverse. -/
lemma MeasurePreserving.map_withDensity_equiv (e : α ≃ᵐ β)
    (h : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) :
    Measure.map e (μ.withDensity f) = ν.withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurableSet_preimage.mpr hs),
    withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    h.setLIntegral_comp_preimage_emb e.measurableEmbedding (f ∘ e.symm) s

end MeasureTheory
