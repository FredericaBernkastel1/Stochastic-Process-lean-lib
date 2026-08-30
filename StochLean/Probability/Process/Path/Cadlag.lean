/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Path.Continuous
public import Mathlib.Topology.Order.LeftRight

/-!
# Almost-sure left-continuous and càdlàg paths

This file provides only trajectory predicates. It does not construct the Skorokhod topology.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

section LeftContinuous

variable [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

def IsLeftContinuousPath (x : T → E) : Prop :=
  ∀ t, ContinuousWithinAt x (Iic t) t

def HasLeftContinuousPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsLeftContinuousPath fun t ↦ X t ω

namespace HasLeftContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

theorem congr (hXY : Indistinguishable X Y P) (hX : HasLeftContinuousPaths X P) :
    HasLeftContinuousPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcont
  simpa only [IsLeftContinuousPath, hω] using hcont

end HasLeftContinuousPaths

namespace IsContinuousPath

theorem isLeftContinuousPath {x : T → E} (h : IsContinuousPath x) :
    IsLeftContinuousPath x :=
  fun _ ↦ h.continuousWithinAt

end IsContinuousPath

theorem HasContinuousPaths.hasLeftContinuousPaths
    {X : T → Ω → E} {P : Measure Ω} (h : HasContinuousPaths X P) :
    HasLeftContinuousPaths X P :=
  h.mono fun _ hω ↦ hω.isLeftContinuousPath

end LeftContinuous

section Cadlag

variable [LinearOrder T] [TopologicalSpace T] [OrderBot T]
  [TopologicalSpace E]

/-- A deterministic càdlàg path is right-continuous and has a finite strict-left limit at every
time other than the lower endpoint. The existential limit keeps the predicate on its natural
domain and does not use a totalized `leftLim` fallback value. -/
def IsCadlagPath (x : T → E) : Prop :=
  IsRightContinuousPath x ∧
    ∀ t, t ≠ ⊥ → ∃ y : E, Tendsto x (nhdsWithin t (Iio t)) (𝓝 y)

/-- A process has càdlàg paths when one common full-measure event supports the whole trajectory
property. -/
def HasCadlagPaths (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, IsCadlagPath fun t ↦ X t ω

namespace HasCadlagPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

theorem hasRightContinuousPaths (h : HasCadlagPaths X P) : HasRightContinuousPaths X P :=
  h.mono fun _ hω ↦ hω.1

theorem congr (hXY : Indistinguishable X Y P) (hX : HasCadlagPaths X P) :
    HasCadlagPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hcad
  refine ⟨?_, ?_⟩
  · simpa only [IsRightContinuousPath, hω] using hcad.1
  · intro t ht
    obtain ⟨y, hy⟩ := hcad.2 t ht
    exact ⟨y, hy.congr' (Eventually.of_forall fun u ↦ hω u)⟩

end HasCadlagPaths

end Cadlag

end ProbabilityTheory
