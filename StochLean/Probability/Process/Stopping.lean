/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import StochLean.Probability.Process.Measurability.Progressive

/-!
# Evaluation of right-continuous adapted processes at stopping times

This file records the bridge from the right-continuous progressive-measurability theorem to
Mathlib's canonical stopping-time API. Stopping times retain codomain `WithTop ℝ≥0`; no theorem
silently assumes that they are finite.
-/

@[expose] public section

open ProbabilityTheory
open NNReal
open TopologicalSpace

namespace MeasureTheory

namespace StronglyAdapted

/-- A right-continuous strongly adapted process evaluated at a stopping time is measurable with
respect to the stopping-time sigma-algebra. This is the reusable chain
`right-continuous + adapted → progressive → stopped-value measurable`. At `τ = ∞` this theorem
uses Mathlib's total `stoppedValue`; it makes no mathematical identification of an `X∞`. Any such
interpretation must separately assume almost-sure finiteness or supply an explicit terminal
value. -/
theorem measurable_stoppedValue_of_rightContinuous
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E} {τ : Ω → WithTop ℝ≥0}
    (hX : StronglyAdapted ℱ X)
    (hright : ∀ ω, IsRightContinuousPath fun t ↦ X t ω)
    (hτ : IsStoppingTime ℱ τ) :
    Measurable[hτ.measurableSpace] (stoppedValue X τ) :=
  measurable_stoppedValue (hX.isStronglyProgressive_of_rightContinuous hright) hτ

end StronglyAdapted

end MeasureTheory
