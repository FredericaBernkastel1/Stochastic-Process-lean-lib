/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Conditional iid and directing-measure vocabulary

Conditional laws are stated almost everywhere after evaluating `condDistrib` at the conditioning
random variable. This avoids asserting equality of arbitrary kernel versions at every point.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω E S : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E] [MeasurableSpace S]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A sequence is conditionally iid given `Θ` if its coordinates are conditionally independent
given `σ(Θ)` and their regular conditional distributions agree almost everywhere. -/
structure IsConditionallyIIDGiven (X : ℕ → Ω → E) (Θ : Ω → S) (μ : Measure Ω)
    [IsFiniteMeasure μ] : Prop where
  measurable_conditioner : Measurable Θ
  measurable_coordinate : ∀ n, Measurable (X n)
  condIndependent :
    iCondIndepFun (MeasurableSpace.comap Θ inferInstance)
      measurable_conditioner.comap_le X μ
  condDistrib_eq_zero : ∀ n,
    ∀ᵐ ω ∂μ, condDistrib (X n) Θ μ (Θ ω) = condDistrib (X 0) Θ μ (Θ ω)

namespace IsConditionallyIIDGiven

theorem condDistrib_eq {X : ℕ → Ω → E} {Θ : Ω → S}
    (h : IsConditionallyIIDGiven X Θ μ) (i j : ℕ) :
    ∀ᵐ ω ∂μ, condDistrib (X i) Θ μ (Θ ω) = condDistrib (X j) Θ μ (Θ ω) := by
  filter_upwards [h.condDistrib_eq_zero i, h.condDistrib_eq_zero j] with ω hi hj
  exact hi.trans hj.symm

end IsConditionallyIIDGiven

/-- A probability-measure-valued random variable directs a sequence when, conditionally on that
random measure, the coordinates are independent and every coordinate has that conditional law. -/
structure IsDirectingMeasure (X : ℕ → Ω → E) (Θ : Ω → ProbabilityMeasure E)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Prop where
  measurable_director : Measurable Θ
  measurable_coordinate : ∀ n, Measurable (X n)
  condIndependent :
    iCondIndepFun (MeasurableSpace.comap Θ inferInstance)
      measurable_director.comap_le X μ
  condDistrib_eq : ∀ n,
    ∀ᵐ ω ∂μ, condDistrib (X n) Θ μ (Θ ω) = (Θ ω : Measure E)

/-- The single public structural de Finetti representation API. Future consumers should use this
predicate rather than introducing a second representation notion. -/
def HasDeFinettiRepresentation (X : ℕ → Ω → E) (μ : Measure Ω)
    [IsFiniteMeasure μ] : Prop :=
  ∃ Θ : Ω → ProbabilityMeasure E, IsDirectingMeasure X Θ μ

theorem IsDirectingMeasure.isConditionallyIIDGiven
    {X : ℕ → Ω → E} {Θ : Ω → ProbabilityMeasure E}
    (h : IsDirectingMeasure X Θ μ) : IsConditionallyIIDGiven X Θ μ where
  measurable_conditioner := h.measurable_director
  measurable_coordinate := h.measurable_coordinate
  condIndependent := h.condIndependent
  condDistrib_eq_zero := by
    intro n
    filter_upwards [h.condDistrib_eq n, h.condDistrib_eq 0] with ω hn h0
    exact hn.trans h0.symm

end ProbabilityTheory
