/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.RightContinuous

/-!
# Almost-sure continuous paths

Path properties use one common full-measure event for the whole trajectory.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [TopologicalSpace T] [TopologicalSpace E]

def IsContinuousPath (x : T → E) : Prop :=
  Continuous x

def HasContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsContinuousPath fun t ↦ X t ω

namespace HasContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

theorem congr (hXY : Indistinguishable X Y P) (hX : HasContinuousPaths X P) :
    HasContinuousPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcont
  simpa only [IsContinuousPath, hω] using hcont

end HasContinuousPaths

namespace IsContinuousPath

variable [Preorder T]

theorem isRightContinuousPath {x : T → E} (h : IsContinuousPath x) :
    IsRightContinuousPath x :=
  fun _ ↦ h.continuousWithinAt

end IsContinuousPath

theorem HasContinuousPaths.hasRightContinuousPaths [Preorder T]
    {X : T → Ω → E} {P : Measure Ω} (h : HasContinuousPaths X P) :
    HasRightContinuousPaths X P :=
  h.mono fun _ hω ↦ hω.isRightContinuousPath

end ProbabilityTheory
