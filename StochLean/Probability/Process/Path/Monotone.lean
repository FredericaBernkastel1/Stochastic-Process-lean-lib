/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Equivalence

/-!
# Almost-sure monotone paths

Path properties are stated on one common full-measure event. This is stronger than having an
exceptional null set that may depend on a pair of times.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}

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

end ProbabilityTheory
