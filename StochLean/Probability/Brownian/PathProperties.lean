/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Construction

/-!
# Brownian path regularity

The Kolmogorov--Chentsov selector has every path locally Hoelder of every exponent below one
half.  An arbitrary Brownian realization inherits all those exponents on one common
indistinguishability event.  The latter formulation deliberately avoids intersecting an
uncountable family of exponent-dependent almost-sure events.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

/-- The selected canonical representative has every path locally Hoelder for every exponent
strictly between zero and one half. -/
theorem IsPreBrownianReal.mk_memHolder_lt_half (hB : IsPreBrownianReal B P)
    (ω : Ω) (t : ℝ≥0) (β : ℝ≥0) (hβ : 0 < β) (hβhalf : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (hB.mk B · ω) U :=
  hB.memHolder_mk ω t β hβ hβhalf

/-- Every Brownian realization has, on one common event, paths locally Hoelder of all exponents
strictly below one half.  This is the simultaneous all-exponents form used by downstream path
arguments. -/
theorem IsBrownianReal.ae_locallyHolder_lt_half (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t (β : ℝ≥0), 0 < β → β < 2⁻¹ →
      ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (B · ω) U := by
  filter_upwards [hB.mk_ae_forall_eq] with ω hω
  intro t β hβ hβhalf
  obtain ⟨U, hUt, C, hC⟩ :=
    hB.toIsPreBrownianReal.memHolder_mk ω t β hβ hβhalf
  refine ⟨U, hUt, C, ?_⟩
  simpa only [hω] using hC

end ProbabilityTheory
