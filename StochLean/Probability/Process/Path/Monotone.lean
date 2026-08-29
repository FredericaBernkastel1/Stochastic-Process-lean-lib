/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Almost-sure monotone paths

Path properties are stated on one common full-measure event. This is stronger than having an
exceptional null set that may depend on a pair of times.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- Two processes are indistinguishable when their complete trajectories agree on one common
almost-sure event. This is stronger than pointwise almost-sure equality at each time. -/
def Indistinguishable (X Y : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

/-- A process has almost-sure monotone paths when one common full-measure event supports a
monotone trajectory at every time. -/
def HasMonotonePaths [Preorder T] [Preorder E] (X : T → Ω → E)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, Monotone fun t ↦ X t ω

namespace HasMonotonePaths

variable [Preorder T] [Preorder E] {X Y : T → Ω → E} {P : Measure Ω}

/-- Monotone paths are invariant under indistinguishable modification. -/
theorem congr (hXY : Indistinguishable X Y P) (hX : HasMonotonePaths X P) :
    HasMonotonePaths Y P := by
  filter_upwards [hXY, hX] with ω hω hmono
  intro s t hst
  simpa only [hω] using hmono hst

end HasMonotonePaths

namespace Indistinguishable

variable {X Y Z : T → Ω → E} {P : Measure Ω}

protected theorem refl (X : T → Ω → E) : Indistinguishable X X P :=
  Filter.Eventually.of_forall fun _ _ ↦ rfl

protected theorem symm (h : Indistinguishable X Y P) : Indistinguishable Y X P := by
  filter_upwards [h] with ω hω t
  exact (hω t).symm

protected theorem trans (hXY : Indistinguishable X Y P) (hYZ : Indistinguishable Y Z P) :
    Indistinguishable X Z P := by
  filter_upwards [hXY, hYZ] with ω hXYω hYZω t
  exact (hXYω t).trans (hYZω t)

/-- Indistinguishability implies pointwise almost-sure equality at every fixed time. -/
theorem ae_eq (h : Indistinguishable X Y P) (t : T) : X t =ᵐ[P] Y t :=
  h.mono fun _ hω ↦ hω t

end Indistinguishable

end ProbabilityTheory
