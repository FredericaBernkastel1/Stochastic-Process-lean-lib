/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.IdentDistrib

/-!
# Stationary increments
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [AddMonoid T] [MeasurableSpace E] [Sub E]

/-- A process has stationary increments when the law of an increment depends only on its lag.
The reference increment is `X t - X 0`; no assumption that `X 0 = 0` is built into the notion. -/
def HasStationaryIncrements (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ s t, IdentDistrib (fun ω ↦ X (s + t) ω - X s ω) (fun ω ↦ X t ω - X 0 ω) P P

namespace HasStationaryIncrements

variable {X : T → Ω → E} {P : Measure Ω}

theorem increment_identDistrib (hX : HasStationaryIncrements X P) (s t : T) :
    IdentDistrib (fun ω ↦ X (s + t) ω - X s ω) (fun ω ↦ X t ω - X 0 ω) P P :=
  hX s t

end HasStationaryIncrements

end ProbabilityTheory
