/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Blumenthal
public import StochLean.Probability.Brownian.Characterization
public import StochLean.Probability.Brownian.BridgeWienerIntegral
public import StochLean.Probability.Brownian.DeterministicWienerIntegral
public import StochLean.Probability.Brownian.PathFunctionals
public import StochLean.Probability.Brownian.PathProperties
public import StochLean.Probability.Brownian.PaleyWienerZygmundPointwise
public import StochLean.Probability.Brownian.Schauder
public import StochLean.Probability.Brownian.StrongMarkov
public import StochLean.Probability.Brownian.Reflection
public import StochLean.Probability.Brownian.Arcsine
public import StochLean.Probability.Brownian.Transformations
public import StochLean.Probability.Process.Regularity.KolmogorovChentsov

/-! Semantic compile-time guards for the canonical Brownian bridge layer. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

#check @exists_modification_holder_iSup

/-- The project-owned Kolmogorov extension and regularization pipeline produces a genuine
Brownian process without any dependency beyond Mathlib. -/
example : IsBrownianReal BrownianReal.brownianCoordinate BrownianReal.preBrownianMeasure :=
  BrownianReal.isBrownianReal_brownianCoordinate

example (ω : ℝ≥0 → ℝ) : Continuous (BrownianReal.brownianCoordinate · ω) :=
  BrownianReal.continuous_brownianCoordinate ω

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

example (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t ≤ 1) :
    HasLaw (brownianBridge B t) (gaussianReal 0 (t * (1 - t))) P :=
  hB.hasLaw_brownianBridge t ht

/-- The singular deterministic-Wiener bridge representation is used only below time one. -/
example (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t < 1) :
    HasLaw (fun ω ↦ hB.deterministicWienerBridge t ω)
      (gaussianReal 0 (((t : ℝ) * (1 - (t : ℝ))).toNNReal)) P :=
  hB.hasLaw_deterministicWienerBridge t ht

/-- The terminal bridge value is a separate theorem; it does not evaluate the singular kernel. -/
example (hB : IsPreBrownianReal B P) : hB.deterministicWienerBridge 1 = 0 := by simp

/-- The bridge residual is fresh Gaussian noise, independent of the terminal value. -/
example (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t ≤ 1) :
    IndepFun (brownianBridge B t) (B 1) P :=
  hB.indepFun_brownianBridge_endpoint t ht

/-- The conditional endpoint regression keeps the corrected variance `t * (1 - t)`. -/
example [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t ≤ 1)
    (hBt : Measurable (B t)) (hB1 : Measurable (B 1)) :
    condDistrib (B t) (B 1) P =ᵐ[P.map (B 1)]
      GaussianConditioning.affineNoiseKernel (t : ℝ)
        (gaussianReal 0 (t * (1 - t))) :=
  hB.condDistrib_eval_given_endpoint t ht hBt hB1

example (t : ℝ≥0) (x : ℝ) :
    GaussianConditioning.affineNoiseKernel (t : ℝ)
        (gaussianReal 0 (t * (1 - t))) x =
      gaussianReal ((t : ℝ) * x) (t * (1 - t)) :=
  GaussianConditioning.affineNoiseKernel_gaussian_apply (t : ℝ) x (t * (1 - t))

/-- The active Mathlib characterization reconstructs pre-Brownian finite-dimensional laws. -/
example (hG : IsGaussianProcess B P) (hmean : ∀ t, P[B t] = 0)
    (hcov : ∀ s t, s ≤ t → cov[B s, B t; P] = s) : IsPreBrownianReal B P :=
  hG.isPreBrownianReal_of_covariance hmean hcov

/-- Brownian motion is characterized without excluding singular covariance matrices. -/
example :
    IsBrownianReal B P ↔
      IsGaussianProcess B P ∧
      (∀ t, P[B t] = 0) ∧
      (∀ s t, s ≤ t → cov[B s, B t; P] = s) ∧
      ∀ᵐ ω ∂P, Continuous (B · ω) :=
  isBrownianReal_iff_gaussian_covariance

/-- Scaling remains guarded by the genuine nonzero-time-scale hypothesis. -/
example (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P :=
  hB.smul hc

/-- Time inversion includes the zero branch and preserves the full Brownian predicate. -/
example (hB : IsBrownianReal B P) :
    IsBrownianReal (brownianTimeInversion B) P :=
  hB.timeInversion

/-- All subcritical Hoelder exponents hold on one common indistinguishability event. -/
example (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t (β : ℝ≥0), 0 < β → β < 2⁻¹ →
      ∃ U ∈ nhds t, ∃ C, HolderOnWith C β (B · ω) U :=
  hB.ae_locallyHolder_lt_half

/-- The pointwise PWZ result is stronger than failure of a uniformly Hoelder neighborhood. -/
example (hB : IsPreBrownianReal B P) {γ : ℝ≥0} (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ∀ t C : ℝ≥0, ¬ HolderAtWith C γ (B · ω) t :=
  hB.ae_nowhere_holderAtWith_gt_half hγ

/-- The project-owned relative difference quotient is almost surely nowhere finite. -/
example (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ¬ HasFiniteDerivativeAt (B · ω) t :=
  hB.ae_nowhere_hasFiniteDerivativeAt

/-- Special dyadic Schauder approximants converge uniformly almost surely; this intentionally
does not follow from the arbitrary-Hilbert-basis `L²` expansion. -/
example (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (dyadicSchauderApproximation (B · ω)) (B · ω)
      atTop (Set.Icc (0 : ℝ≥0) 1) :=
  hB.ae_tendstoUniformlyOn_dyadicSchauderApproximation

/-- The measurable countable running supremum agrees with genuine strict path exceedance on the
single Brownian continuity event. -/
example (hB : IsBrownianReal B P) {T : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂P, ENNReal.ofReal a < denseRunningSupremum B T ω ↔
      ∃ t : ℝ≥0, t ≤ T ∧ a < B t ω :=
  hB.ae_lt_denseRunningSupremum_iff ha

/-- Reflection is obtained from the project-owned dyadic first-passage construction, with the
strict boundary discharged by Gaussian atomlessness. -/
example [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < B t ω} = 2 * P {ω | a < B T ω} :=
  hB.reflection_principle ha T

/-- The last-zero functional is measurable on the canonical all-path-continuous representative. -/
example (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Measurable (lastZeroBefore (hB.toIsPreBrownianReal.mk B) T) :=
  measurable_lastZeroBefore hB.toIsPreBrownianReal.measurable_mk
    hB.toIsPreBrownianReal.continuous_mk T

/-- Arbitrary Brownian realizations inherit last-zero measurability modulo their law. -/
example (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (lastZeroBefore B T) P :=
  hB.aemeasurable_lastZeroBefore T

/-- Lévy's arcsine CDF holds on the full deterministic interval, including both endpoints. -/
example [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {q T : ℝ≥0} (hT : T ≠ 0) (hqT : q ≤ T) :
    P {ω | lastZeroBefore B T ω ≤ q} =
      ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) :=
  hB.lastZeroBefore_cdf hT hqT

/-- The arbitrary finite-stopping-time result is obtained from the actual upper dyadic
approximation, not from a countable-range hypothesis on the target stopping time. -/
example {I : Type*} [Finite I] [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (t : I → ℝ≥0) (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (hfcont : Continuous f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τ ω : WithTop ℝ≥0))) :
    P[(f ∘ brownianFutureIncrementsAfter B τ t) | hτ.measurableSpace] =ᵐ[P]
      fun _ ↦ P[f ∘ brownianFutureIncrements B 0 t] :=
  hB.condExp_futureIncrementsAfter hBm t f hf hfcont C hC hbound τ hτ

/-- The zero--one statement is deliberately about probability triviality of the canonical
continuous representative's germ sigma-field. -/
example (hB : IsBrownianReal B P) {A : Set Ω}
    (hA : MeasurableSet[⨅ s > 0,
      Filtration.natural (hB.toIsPreBrownianReal.mk B)
        (fun t ↦ (hB.toIsPreBrownianReal.measurable_mk t).stronglyMeasurable) s] A) :
    P A = 0 ∨ P A = 1 :=
  hB.blumenthal_zeroOne_canonical hA

/-- The deterministic Wiener object is an actual linear isometry on the `L²` quotient. -/
noncomputable example (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  hB.deterministicWienerIntegral T

noncomputable example (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ‖hB.deterministicWienerIntegral T f‖ = ‖f‖ :=
  hB.norm_deterministicWienerIntegral T f

noncomputable example (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    cov[(fun ω ↦ hB.deterministicWienerIntegral T f ω),
        (fun ω ↦ hB.deterministicWienerIntegral T g ω); P] =
      ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s * g s ∂volume :=
  hB.covariance_deterministicWienerIntegral T f g

end ProbabilityTheory
