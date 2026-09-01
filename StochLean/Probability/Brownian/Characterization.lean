/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Construction

/-!
# Gaussian covariance characterization of Brownian motion

This bridge preserves Mathlib's canonical Brownian predicates.  In particular the Gaussian
process condition accepts singular finite-dimensional covariance matrices; no positive-definite
matrix strengthening is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

/-- A process is Brownian exactly when it is a centered Gaussian process with covariance
`min s t` and almost-surely continuous paths. -/
theorem isBrownianReal_iff_gaussian_covariance :
    IsBrownianReal B P ↔
      IsGaussianProcess B P ∧
      (∀ t, P[B t] = 0) ∧
      (∀ s t, s ≤ t → cov[B s, B t; P] = s) ∧
      ∀ᵐ ω ∂P, Continuous (B · ω) := by
  constructor
  · intro hB
    exact ⟨hB.isGaussianProcess, hB.integral_eval,
      fun s t hst ↦ by simpa [min_eq_left hst] using hB.covariance_eval s t,
      hB.cont⟩
  · rintro ⟨hG, hmean, hcov, hcont⟩
    exact
      { toIsPreBrownianReal := hG.isPreBrownianReal_of_covariance hmean hcov
        cont := hcont }

end ProbabilityTheory
