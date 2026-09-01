/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.SineTruncationExtraction
public import StochLean.Probability.InfinitelyDivisible.LevySemigroup

/-!
# Converse Lévy--Khintchine theorem for real probability laws

This module completes the law-to-triplet direction internally.  Canonical convolution roots are
weighted by `1 - sinc x`, their finite weak limit is divided away from zero to recover the jump
measure, the atom at zero recovers the Gaussian variance, and the sine-truncation residual recovers
the drift.  The result is converted back to StochLean's fixed strict-truncation convention.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.LevyTriplet

theorem integral_sineTruncationRatio_canonicalRootExtraction
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (t : ℝ) :
    ∫ x, sineTruncationRatio t x ∂
        (canonicalRootExtractionFiniteMeasure hμ n : Measure ℝ) =
      ∫ x, levyExponentIntegrandWithTruncation Real.sin t x ∂
        (hμ.canonicalRootIntensity n : Measure ℝ) := by
  rw [canonicalRootExtractionFiniteMeasure, coe_extractionFiniteMeasure,
    extractionMeasure,
    integral_withDensity_eq_integral_smul measurable_extractionWeight]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x = 0
  · subst x
    simp [sineTruncationRatio, levyExponentIntegrandWithTruncation]
  · rw [sineTruncationRatio, if_neg hx]
    simp only [NNReal.smul_def, Complex.real_smul]
    have hw : ((extractionWeight x : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast (extractionWeight_pos hx).ne')
    field_simp

theorem integral_sineTruncationRatio_eq_gaussian_add_jump
    (kappa : FiniteMeasure ℝ) (t : ℝ) :
    ∫ x, sineTruncationRatio t x ∂(kappa : Measure ℝ) =
      -((((kappa {0} : ℝ) * 3 * t ^ 2 : ℝ) : ℂ)) +
        ∫ x, levyExponentIntegrandWithTruncation Real.sin t x ∂
          extractedJumpMeasure kappa := by
  have hweighted :
      ∫ x, levyExponentIntegrandWithTruncation Real.sin t x ∂
          extractedJumpMeasure kappa =
        ∫ x, sineTruncationRatio t x ∂
          ((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ) := by
    calc
      _ = ∫ x, (extractionWeight x) • sineTruncationRatio t x ∂
          extractedJumpMeasure kappa := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x = 0
        · subst x
          simp [sineTruncationRatio, levyExponentIntegrandWithTruncation]
        · rw [sineTruncationRatio, if_neg hx]
          simp only [NNReal.smul_def, Complex.real_smul]
          have hw : ((extractionWeight x : ℝ) : ℂ) ≠ 0 := by
            exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast (extractionWeight_pos hx).ne')
          field_simp
      _ = ∫ x, sineTruncationRatio t x ∂
          (extractedJumpMeasure kappa).withDensity
            (fun x => (extractionWeight x : ℝ≥0∞)) := by
        rw [integral_withDensity_eq_integral_smul measurable_extractionWeight]
      _ = _ := by rw [extractedJumpMeasure_withDensity_extractionWeight]
  have hfi : Integrable (sineTruncationRatio t) (kappa : Measure ℝ) := by
    have hC : 0 ≤ max (3 * t ^ 2)
        ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)) :=
      (mul_nonneg (by norm_num) (sq_nonneg t)).trans (le_max_left _ _)
    apply (integrable_const
      (max (3 * t ^ 2) ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)))).mono
    · exact (continuous_sineTruncationRatio t).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        simpa [Real.norm_of_nonneg hC] using norm_sineTruncationRatio_le t x
  have hsplit := integral_add_compl (μ := (kappa : Measure ℝ))
    (MeasurableSet.singleton 0) hfi
  have hzero :
      ∫ x in ({0} : Set ℝ), sineTruncationRatio t x ∂(kappa : Measure ℝ) =
        -((((kappa {0} : ℝ) * 3 * t ^ 2 : ℝ) : ℂ)) := by
    rw [integral_singleton]
    rw [FiniteMeasure.measureReal_eq_coe_coeFn]
    simp [sineTruncationRatio]
    ring
  calc
    _ = ∫ x in ({0} : Set ℝ), sineTruncationRatio t x ∂(kappa : Measure ℝ) +
        ∫ x in ({0} : Set ℝ)ᶜ, sineTruncationRatio t x ∂(kappa : Measure ℝ) :=
      hsplit.symm
    _ = _ := by rw [hzero, ← hweighted]

noncomputable def canonicalRootSineDrift
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) : ℝ :=
  ∫ x, Real.sin x ∂(hμ.canonicalRootIntensity n : Measure ℝ)

theorem canonicalRootLinearization_eq_sineDecomposition
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (t : ℝ) :
    canonicalRootLinearization hμ n t =
      (∫ x, levyExponentIntegrandWithTruncation Real.sin t x ∂
        (hμ.canonicalRootIntensity n : Measure ℝ)) +
      (((t * canonicalRootSineDrift hμ n : ℝ) : ℂ) * Complex.I) := by
  have hsin : Integrable Real.sin (hμ.canonicalRootIntensity n : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono
    · exact Real.continuous_sin.aestronglyMeasurable
    · exact ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x
  have hcorr : Integrable
      (fun x => (((t * Real.sin x : ℝ) : ℂ) * Complex.I))
      (hμ.canonicalRootIntensity n : Measure ℝ) :=
    (hsin.const_mul t).ofReal.mul_const Complex.I
  have hsine : Integrable (levyExponentIntegrandWithTruncation Real.sin t)
      (hμ.canonicalRootIntensity n : Measure ℝ) := by
    have hC : 0 ≤ 2 + |t| := by positivity
    apply (integrable_const (2 + |t| : ℝ)).mono
    · unfold levyExponentIntegrandWithTruncation
      fun_prop
    · apply ae_of_all
      intro x
      calc
        _ ≤ ‖Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) - 1‖ +
            ‖(((t * Real.sin x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ ≤ 2 + |t| := by
          have hexp : ‖Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I)) - 1‖ ≤ 2 := by
            calc
              _ ≤ ‖Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))‖ + ‖(1 : ℂ)‖ :=
                norm_sub_le _ _
              _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
          have hsinle :
              ‖(((t * Real.sin x : ℝ) : ℂ) * Complex.I)‖ ≤ |t| := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
              Real.norm_eq_abs, abs_mul]
            nlinarith [Real.abs_sin_le_one x, abs_nonneg t]
          linarith
        _ = ‖(2 + |t| : ℝ)‖ := (Real.norm_of_nonneg hC).symm
  rw [← ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity
    hμ n t]
  have hpoint : LevyTriplet.poissonExponentIntegrand t = fun x =>
      levyExponentIntegrandWithTruncation Real.sin t x +
        (((t * Real.sin x : ℝ) : ℂ) * Complex.I) := by
    funext x
    simp only [LevyTriplet.poissonExponentIntegrand,
      levyExponentIntegrandWithTruncation]
    ring
  rw [hpoint, integral_add hsine hcorr, canonicalRootSineDrift,
    integral_mul_const, integral_complex_ofReal, integral_const_mul]

theorem tendsto_integral_sineLevyExponent_canonicalRootIntensity
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {kappa : FiniteMeasure ℝ}
    (hkappa : Tendsto (canonicalRootExtractionFiniteMeasure hμ) atTop (𝓝 kappa))
    (t : ℝ) :
    Tendsto
      (fun n => ∫ x, levyExponentIntegrandWithTruncation Real.sin t x ∂
        (hμ.canonicalRootIntensity n : Measure ℝ))
      atTop (𝓝 (∫ x, sineTruncationRatio t x ∂(kappa : Measure ℝ))) := by
  have h := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hkappa
    (sineTruncationRatioBCF t)
  simpa [sineTruncationRatioBCF,
    integral_sineTruncationRatio_canonicalRootExtraction] using h

noncomputable def extractedSineDrift
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    (kappa : FiniteMeasure ℝ) : ℝ :=
  (hμ.exponent 1 - ∫ x, sineTruncationRatio 1 x ∂(kappa : Measure ℝ)).im

noncomputable def extractedTriplet
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    (kappa : FiniteMeasure ℝ) : LevyTriplet where
  gaussianVariance := 6 * kappa {0}
  drift := extractedSineDrift hμ kappa -
    ∫ x, (Real.sin x - levyTruncation x) ∂extractedJumpMeasure kappa
  jumpMeasure := extractedJumpMeasure kappa
  isLevyMeasure_jumpMeasure := isLevyMeasure_extractedJumpMeasure kappa

theorem extractedTriplet_driftUnderTruncation_sin
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    (kappa : FiniteMeasure ℝ) :
    (extractedTriplet hμ kappa).driftUnderTruncation Real.sin =
      extractedSineDrift hμ kappa := by
  simp only [driftUnderTruncation, extractedTriplet]
  ring

theorem tendsto_canonicalRootSineDrift
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {kappa : FiniteMeasure ℝ}
    (hkappa : Tendsto (canonicalRootExtractionFiniteMeasure hμ) atTop (𝓝 kappa)) :
    Tendsto (canonicalRootSineDrift hμ) atTop
      (𝓝 (extractedSineDrift hμ kappa)) := by
  have hdiff :=
    (ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
      hμ 1).sub
        (tendsto_integral_sineLevyExponent_canonicalRootIntensity hμ hkappa 1)
  have hcomplex : Tendsto
      (fun n => ((canonicalRootSineDrift hμ n : ℝ) : ℂ) * Complex.I)
      atTop
      (𝓝 (hμ.exponent 1 -
        ∫ x, sineTruncationRatio 1 x ∂(kappa : Measure ℝ))) := by
    apply Tendsto.congr' _ hdiff
    filter_upwards [] with n
    rw [canonicalRootLinearization_eq_sineDecomposition hμ n 1]
    push_cast
    ring
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  rw [show canonicalRootSineDrift hμ =
      Complex.im ∘ fun n => ((canonicalRootSineDrift hμ n : ℝ) : ℂ) * Complex.I by
    funext n
    simp [Function.comp_apply]]
  simpa [extractedSineDrift] using him

theorem exponent_eq_extracted_sine
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {kappa : FiniteMeasure ℝ}
    (hkappa : Tendsto (canonicalRootExtractionFiniteMeasure hμ) atTop (𝓝 kappa))
    (t : ℝ) :
    hμ.exponent t =
      (∫ x, sineTruncationRatio t x ∂(kappa : Measure ℝ)) +
        (((t * extractedSineDrift hμ kappa : ℝ) : ℂ) * Complex.I) := by
  have hjump :=
    tendsto_integral_sineLevyExponent_canonicalRootIntensity hμ hkappa t
  have hdriftR := tendsto_canonicalRootSineDrift hμ hkappa
  have hmulR : Tendsto (fun n => t * canonicalRootSineDrift hμ n) atTop
      (𝓝 (t * extractedSineDrift hμ kappa)) := tendsto_const_nhds.mul hdriftR
  have hdriftC : Tendsto
      (fun n => (((t * canonicalRootSineDrift hμ n : ℝ) : ℂ))) atTop
      (𝓝 (((t * extractedSineDrift hμ kappa : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hmulR
  have hdrift := hdriftC.mul_const Complex.I
  have hsum := hjump.add hdrift
  have hroot : Tendsto
      (fun n => canonicalRootLinearization hμ n t) atTop
      (𝓝 ((∫ x, sineTruncationRatio t x ∂(kappa : Measure ℝ)) +
        (((t * extractedSineDrift hμ kappa : ℝ) : ℂ) * Complex.I))) := by
    apply Tendsto.congr' _ hsum
    filter_upwards [] with n
    exact (canonicalRootLinearization_eq_sineDecomposition hμ n t).symm
  exact tendsto_nhds_unique
    (ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
      hμ t) hroot

theorem extractedTriplet_exponent_eq
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {kappa : FiniteMeasure ℝ}
    (hkappa : Tendsto (canonicalRootExtractionFiniteMeasure hμ) atTop (𝓝 kappa)) :
    (extractedTriplet hμ kappa).exponent = hμ.exponent := by
  funext t
  rw [← (extractedTriplet hμ kappa).exponentWithTruncation_eq
    isAdmissibleLevyTruncation_sin t]
  rw [exponent_eq_extracted_sine hμ hkappa t,
    integral_sineTruncationRatio_eq_gaussian_add_jump kappa t]
  rw [exponentWithTruncation, extractedTriplet_driftUnderTruncation_sin]
  simp only [extractedTriplet]
  push_cast
  ring

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exists_representingTriplet
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    ∃ eta : LevyTriplet, eta.Represents μ := by
  obtain ⟨kappa, _, hkappa⟩ := hμ.exists_canonicalRootExtractionLimit
  refine ⟨extractedTriplet hμ kappa, fun t => ?_⟩
  rw [← hμ.exp_exponent t]
  rw [extractedTriplet_exponent_eq hμ hkappa]

/-- A real law is infinitely divisible exactly when it admits a StochLean Lévy triplet. -/
theorem isInfinitelyDivisible_iff_exists_representingTriplet
    {μ : ProbabilityMeasure ℝ} :
    μ.IsInfinitelyDivisible ↔ ∃ eta : LevyTriplet, eta.Represents μ := by
  constructor
  · exact fun hμ => hμ.exists_representingTriplet
  · rintro ⟨eta, heta⟩
    exact heta.isInfinitelyDivisible

/-- Every infinitely divisible real law has a unique triplet in the fixed StochLean convention. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.hasUniqueLevyTriplet
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    HasUniqueLevyTriplet μ := by
  obtain ⟨eta, heta⟩ := hμ.exists_representingTriplet
  exact heta.hasUniqueLevyTriplet

end ProbabilityTheory.LevyTriplet
