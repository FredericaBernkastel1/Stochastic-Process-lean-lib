/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.Adapted

/-!
# Joint/product measurability of stochastic processes

This predicate means measurability on the ordinary product sigma-algebra. It is intentionally
distinct from progressive and predictable measurability.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} [MeasurableSpace T] [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

def IsProductMeasurable (X : T → Ω → E) : Prop :=
  Measurable (Function.uncurry X)

namespace IsProductMeasurable

variable {X : T → Ω → E}

theorem measurable_coordinate (h : IsProductMeasurable X) (t : T) : Measurable (X t) :=
  h.of_uncurry_left

theorem measurable_path (h : IsProductMeasurable X) (ω : Ω) :
    Measurable fun t ↦ X t ω :=
  h.of_uncurry_right

/-- Product measurability implies measurability into the coordinate-product sigma-algebra. No
topological path-space law is asserted. -/
theorem measurable_process (h : IsProductMeasurable X) :
    Measurable fun ω ↦ (X · ω) :=
  measurable_pi_lambda _ fun t ↦ h.measurable_coordinate t

end IsProductMeasurable

end ProbabilityTheory
