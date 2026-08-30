/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Forward transition systems

A `TransitionSystem T E` contains kernels only for legal forward-time pairs.  In particular, no
value is manufactured for `r > s`.  Mathlib composition is chronological in the following sense:
`η ∘ₖ κ` first runs `κ` and then `η`.  Thus Chapman-Kolmogorov is written
`K r t = K s t ∘ₖ K r s`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable (T E : Type*) [Preorder T] [MeasurableSpace E]

/-- A two-parameter family of kernels indexed only by forward-time pairs. -/
abbrev TransitionSystem := (r s : T) → r ≤ s → Kernel E E

variable {T E}

/-- The Markov and Chapman-Kolmogorov laws for a forward transition system.  The diagonal law is
the canonical completion of Klenke Definition 14.42. -/
structure IsMarkovTransitionSystem (K : TransitionSystem T E) : Prop where
  isMarkovKernel : ∀ r s hrs, IsMarkovKernel (K r s hrs)
  diagonal : ∀ t, K t t le_rfl = Kernel.id
  comp : ∀ {r s t} (hrs : r ≤ s) (hst : s ≤ t),
    K r t (hrs.trans hst) = K s t hst ∘ₖ K r s hrs

namespace IsMarkovTransitionSystem

variable {K : TransitionSystem T E}

/-- Every legal member of a Markov transition system is a Markov kernel. -/
theorem markov (hK : IsMarkovTransitionSystem K) (r s : T) (hrs : r ≤ s) :
    IsMarkovKernel (K r s hrs) :=
  hK.isMarkovKernel r s hrs

/-- Chapman-Kolmogorov with its chronological orientation made explicit. -/
theorem chapmanKolmogorov (hK : IsMarkovTransitionSystem K)
    {r s t : T} (hrs : r ≤ s) (hst : s ≤ t) :
    K r t (hrs.trans hst) = K s t hst ∘ₖ K r s hrs :=
  hK.comp hrs hst

/-- A forward transition system is independent of the proof supplied for a fixed legal pair. -/
theorem proof_irrel (K : TransitionSystem T E) {r s : T} (h₁ h₂ : r ≤ s) :
    K r s h₁ = K r s h₂ := by
  rw [Subsingleton.elim h₁ h₂]

end IsMarkovTransitionSystem

end ProbabilityTheory
