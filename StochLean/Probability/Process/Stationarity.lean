/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Stationary stochastic processes

Stationarity is equality of the full coordinate-product process law under every time shift. It is
not reduced to equality of one-time marginals, and it is not advertised as equality in a
continuous or càdlàg path-space topology.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} [AddMonoid T] [MeasurableSpace E]

/-- A process is stationary when every deterministic time shift has the same
coordinate-product law as the original process. -/
def IsStationary (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ s, IdentDistrib (fun ω t ↦ X t ω) (fun ω t ↦ X (s + t) ω) P P

namespace IsStationary

variable {X : T → Ω → E} {P : Measure Ω}

theorem identDistrib_shift (h : IsStationary X P) (s : T) :
    IdentDistrib (fun ω t ↦ X t ω) (fun ω t ↦ X (s + t) ω) P P :=
  h s

/-- Every fixed coordinate of a stationary process has the corresponding shifted law. This is a
consequence of stationarity, not its definition. -/
theorem coordinate_identDistrib (h : IsStationary X P) (s t : T) :
    IdentDistrib (X t) (X (s + t)) P P := by
  simpa [Function.comp_def] using (h s).comp (measurable_pi_apply t)

/-- Every finite collection of coordinates has the corresponding jointly shifted law. -/
theorem finset_identDistrib (h : IsStationary X P) (s : T) (I : Finset T) :
    IdentDistrib (fun ω ↦ I.restrict (X · ω))
      (fun ω ↦ I.restrict (fun t ↦ X (s + t) ω)) P P := by
  simpa [Function.comp_def, Finset.restrict_def] using
    (h s).comp (Finset.measurable_restrict _)

end IsStationary

/-- A failed finite-dimensional shift law is enough to reject stationarity. This guard makes it
impossible for equal one-time marginals alone to discharge the public definition. -/
theorem not_isStationary_of_not_finset_identDistrib {X : T → Ω → E} {P : Measure Ω}
    {s : T} {I : Finset T}
    (h : ¬ IdentDistrib (fun ω ↦ I.restrict (X · ω))
      (fun ω ↦ I.restrict (fun t ↦ X (s + t) ω)) P P) :
    ¬ IsStationary X P :=
  fun hstat ↦ h (hstat.finset_identDistrib s I)

end ProbabilityTheory
