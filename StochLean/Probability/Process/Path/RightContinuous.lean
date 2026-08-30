/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.IsLUB
public import StochLean.Probability.Process.Path.Monotone

/-!
# Almost-sure right-continuous paths
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

section PathDefinitions

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

end PathDefinitions

namespace IsModification

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder T] [TopologicalSpace T] [OrderTopology T] [DenselyOrdered T] [NoMaxOrder T]
  [FirstCountableTopology T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [TopologicalSpace E] [T2Space E] {X Y : T → Ω → E} {P : Measure Ω}

/-- On a densely ordered interval without a terminal time, two right-continuous modifications are
indistinguishable. The proof obtains common equality on a countable dense set and then approaches
every time from the right. -/
theorem indistinguishable_of_rightContinuous
    (hmod : IsModification X Y P)
    (hX : HasRightContinuousPaths X P)
    (hY : HasRightContinuousPaths Y P) :
    Indistinguishable X Y P := by
  have hdense : ∀ᵐ ω ∂P, ∀ n, X (TopologicalSpace.denseSeq T n) ω =
      Y (TopologicalSpace.denseSeq T n) ω := by
    rw [ae_all_iff]
    exact fun n ↦ hmod (TopologicalSpace.denseSeq T n)
  filter_upwards [hdense, hX, hY] with ω hω hXω hYω
  intro t
  have hD : Dense (Set.range (TopologicalSpace.denseSeq T)) :=
    TopologicalSpace.denseRange_denseSeq T
  obtain ⟨u, _huanti, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto t
  have hwithin : Tendsto u atTop (nhdsWithin t (Ici t)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (hu n).1.le⟩
  have hXt : Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X t ω)) :=
    (hXω t).tendsto.comp hwithin
  have hYt : Tendsto (fun n ↦ Y (u n) ω) atTop (𝓝 (Y t ω)) :=
    (hYω t).tendsto.comp hwithin
  have hseq : ∀ n, X (u n) ω = Y (u n) ω := by
    intro n
    obtain ⟨k, hk⟩ := (hu n).2
    rw [← hk]
    exact hω k
  exact tendsto_nhds_unique hXt
    (hYt.congr' (Eventually.of_forall fun n ↦ (hseq n).symm))

end IsModification

end ProbabilityTheory
