/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Transformations

/-! Semantic compile-time guards for the canonical Brownian bridge layer. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

example (hB : IsPreBrownianReal B P) : ∀ᵐ ω ∂P, B 0 ω = 0 :=
  hB.eval_zero_ae_eq_zero

example (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : brownianTimeInversion B 0 ω = 0 := by
  simp

example (hB : IsPreBrownianReal B P) :
    HasStationaryIndependentIncrements B P :=
  hB.hasStationaryIndependentIncrements

example (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ProbabilityMeasure.IsInfinitelyDivisible (brownianIncrementLaw t) :=
  hB.brownianIncrementLaw_isInfinitelyDivisible t

example (hB : IsPreBrownianReal B P) : IsGaussianProcess (brownianBridge B) P :=
  hB.brownianBridge_isGaussianProcess

example (hB : IsPreBrownianReal B P) : ∀ᵐ ω ∂P, brownianBridge B 0 ω = 0 :=
  hB.brownianBridge_zero_ae

example (hB : IsPreBrownianReal B P) (s t : ℝ≥0) (hs : s ≤ 1) (ht : t ≤ 1) :
    cov[brownianBridge B s, brownianBridge B t; P] =
      ((min s t : ℝ≥0) : ℝ) - (s : ℝ) * (t : ℝ) :=
  hB.covariance_brownianBridge s t hs ht

/-- The active Mathlib characterization reconstructs pre-Brownian finite-dimensional laws. -/
example (hG : IsGaussianProcess B P) (hmean : ∀ t, P[B t] = 0)
    (hcov : ∀ s t, s ≤ t → cov[B s, B t; P] = s) : IsPreBrownianReal B P :=
  hG.isPreBrownianReal_of_covariance hmean hcov

/-- Scaling remains guarded by the genuine nonzero-time-scale hypothesis. -/
example (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P :=
  hB.smul hc

end ProbabilityTheory
