/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Order.LeftRight
public import StochLean.Probability.Process.Path.Monotone

/-!
# Almost-sure right-continuous paths
-/

@[expose] public section

open MeasureTheory Filter Set

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

/-- A deterministic path is right-continuous when it is continuous at every time within the
corresponding upper interval. -/
def IsRightContinuousPath (x : T → E) : Prop :=
  ∀ t, ContinuousWithinAt x (Ici t) t

/-- A process has almost-sure right-continuous paths when one common full-measure event supports
right-continuity at every time. -/
def HasRightContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsRightContinuousPath fun t ↦ X t ω

namespace HasRightContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

/-- Right-continuous paths are invariant under indistinguishable modification. -/
theorem congr (hXY : Indistinguishable X Y P) (hX : HasRightContinuousPaths X P) :
    HasRightContinuousPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcont
  simpa only [IsRightContinuousPath, hω] using hcont

end HasRightContinuousPaths

end ProbabilityTheory
