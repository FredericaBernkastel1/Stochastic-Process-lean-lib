/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Modification and indistinguishability of stochastic processes

The two relations in this file deliberately have different quantifier order. A modification may
use a different null set at every time; indistinguishability requires one common full-measure event
on which the complete trajectories agree.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- `X` and `Y` are modifications (versions) of one another when their coordinates agree almost
surely at every fixed time. The exceptional null set may depend on the time. -/
def IsModification (X Y : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ t, X t =ᵐ[P] Y t

/-- Two processes are indistinguishable when their complete trajectories agree on one common
almost-sure event. This is strictly stronger than modification for uncountable time sets. -/
def Indistinguishable (X Y : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

namespace IsModification

variable {X Y Z : T → Ω → E} {P : Measure Ω}

protected theorem refl (X : T → Ω → E) : IsModification X X P :=
  fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl

protected theorem symm (h : IsModification X Y P) : IsModification Y X P :=
  fun t ↦ (h t).symm

protected theorem trans (hXY : IsModification X Y P) (hYZ : IsModification Y Z P) :
    IsModification X Z P :=
  fun t ↦ (hXY t).trans (hYZ t)

/-- For a countable time set, modification and indistinguishability coincide. -/
theorem indistinguishable_of_countable [Countable T] (h : IsModification X Y P) :
    Indistinguishable X Y P := by
  rw [Indistinguishable, ae_all_iff]
  exact h

variable [MeasurableSpace E]

/-- A modification has the same law on every finite coordinate set. -/
theorem map_restrict_eq (h : IsModification X Y P) (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = P.map (fun ω ↦ I.restrict (Y · ω)) :=
  map_restrict_eq_of_forall_ae_eq h I

/-- Under the genuine coordinate-product measurability assumptions, a modification has the same
coordinate-product process law. This is not a statement about a continuous or càdlàg path-space
topology. -/
theorem map_process_eq [IsFiniteMeasure P]
    (h : IsModification X Y P)
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P)
    (hY : AEMeasurable (fun ω ↦ (Y · ω)) P) :
    P.map (fun ω ↦ (X · ω)) = P.map (fun ω ↦ (Y · ω)) :=
  map_eq_of_forall_ae_eq hX hY h

end IsModification

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

theorem isModification (h : Indistinguishable X Y P) : IsModification X Y P :=
  h.ae_eq

end Indistinguishable

end ProbabilityTheory
