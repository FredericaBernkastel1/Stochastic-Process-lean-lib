/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Probability couplings

This generic owner deliberately contains no Markov-chain structure.  A coupling is simply a joint
law with prescribed coordinate marginals.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace ProbabilityTheory

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- A joint measure is a coupling of its prescribed first and second marginals. -/
def IsCoupling (γ : Measure (E × F)) (μ : Measure E) (ν : Measure F) : Prop :=
  Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν

namespace IsCoupling

/-- The first marginal identity. -/
theorem fst {γ : Measure (E × F)} {μ : Measure E} {ν : Measure F}
    (h : IsCoupling γ μ ν) : Measure.map Prod.fst γ = μ :=
  h.1

/-- The second marginal identity. -/
theorem snd {γ : Measure (E × F)} {μ : Measure E} {ν : Measure F}
    (h : IsCoupling γ μ ν) : Measure.map Prod.snd γ = ν :=
  h.2

/-- A coupling of probability measures is itself explicitly required to be a probability law by
downstream APIs; this theorem records that its total mass is already forced by either marginal. -/
theorem measure_univ {γ : Measure (E × F)} {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ]
    (h : IsCoupling γ μ ν) : γ Set.univ = 1 := by
  calc
    γ Set.univ = (Measure.map Prod.fst γ) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = μ Set.univ := congrArg (fun m : Measure E => m Set.univ) h.1
    _ = 1 := MeasureTheory.measure_univ

end IsCoupling

/-- Product probability is the independent coupling. -/
theorem isCoupling_prod (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν := by
  constructor
  · simpa using Measure.map_fst_prod (E := E) (F := F) (μ := μ) (ν := ν)
  · simpa using Measure.map_snd_prod (E := E) (F := F) (μ := μ) (ν := ν)

/-- Probability that the two coordinates of a coupling disagree. -/
def couplingMismatch (γ : Measure (E × E)) : ℝ≥0∞ :=
  γ {p | p.1 ≠ p.2}

end ProbabilityTheory
