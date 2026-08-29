/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Semantic guards for conditional probability

Mathlib deliberately totalizes conditioning on a null event.  This module adds a small typed
boundary for public probability statements: a `ConditionableEvent` carries measurability and
positive probability, so its conditional measure is genuinely a probability measure.  Regular
conditional distributions remain kernels and are unique only almost everywhere under the law of
the conditioning variable.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

noncomputable section

variable {Ω α β S : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- An event on which conditioning is mathematically defined as a probability measure. -/
structure ConditionableEvent (P : Measure Ω) where
  event : Set Ω
  measurableSet_event : MeasurableSet event
  prob_ne_zero : P event ≠ 0

namespace ConditionableEvent

/-- The conditional probability measure attached to a positive measurable event. -/
def measure (B : ConditionableEvent P) : Measure Ω := P[|B.event]

instance [IsFiniteMeasure P] (B : ConditionableEvent P) : IsProbabilityMeasure B.measure :=
  cond_isProbabilityMeasure B.prob_ne_zero

/-- Safe event-conditioning formula.  The positivity assumption is carried by `B`, rather than
being lost through the totalized raw `cond` operation. -/
theorem measure_apply (B : ConditionableEvent P) (A : Set Ω) :
    B.measure A = (P B.event)⁻¹ * P (B.event ∩ A) :=
  cond_apply B.measurableSet_event P A

@[simp]
theorem measure_event [IsFiniteMeasure P] (B : ConditionableEvent P) :
    B.measure B.event = 1 :=
  cond_apply_self B.prob_ne_zero (measure_ne_top P B.event)

end ConditionableEvent

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S] {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → β} {Y : Ω → S}

/-- Any two finite kernels representing the same joint law are equal only almost everywhere
under the law of the conditioning variable.  This is the public uniqueness semantics for
conditioning at a point. -/
theorem conditionalKernel_ae_eq_of_compProd_eq
    {κ η : Kernel β S} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hY : AEMeasurable Y μ)
    (hκ : μ.map (fun ω ↦ (X ω, Y ω)) = μ.map X ⊗ₘ κ)
    (hη : μ.map (fun ω ↦ (X ω, Y ω)) = μ.map X ⊗ₘ η) :
    κ =ᵐ[μ.map X] η := by
  exact (condDistrib_ae_eq_of_measure_eq_compProd X hY hκ).symm.trans
    (condDistrib_ae_eq_of_measure_eq_compProd X hY hη)

end

end ProbabilityTheory
