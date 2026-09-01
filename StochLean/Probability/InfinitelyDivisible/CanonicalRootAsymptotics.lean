/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Approximation
public import StochLean.Probability.InfinitelyDivisible.FiniteMeasureFourier

/-!
# Canonical-root asymptotics

This module develops the finite-measure extraction input for the converse real
Lévy--Khintchine theorem.  For an infinitely divisible law, its canonical `(n+1)`st roots have
characteristic functions `exp (ψ/(n+1))`.  Their scaled laws therefore linearize to the normalized
continuous exponent `ψ` without choosing branches of the complex logarithm.

The second-difference weight is then applied directly to those finite intensities.  Its Fourier
transform converges to the second difference of `ψ`; this is the finite-measure compactness datum
from which the Gaussian coefficient and Lévy measure are recovered.  Everything here is native
StochLean code and depends only on Mathlib.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

/-- The linearized characteristic function of the canonical `(n+1)`st convolution root. -/
noncomputable def canonicalRootLinearization
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (t : ℝ) : ℂ :=
  ((n + 1 : ℕ) : ℂ) *
    (charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t - 1)

/-- Canonical roots linearize to the normalized continuous characteristic exponent. -/
theorem ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto (fun n => canonicalRootLinearization hμ n t) atTop (𝓝 (hμ.exponent t)) := by
  have h := tendsto_nat_mul_cexp_sub_one_div (hμ.exponent t)
  convert h using 1
  funext n
  rw [canonicalRootLinearization, hμ.charFun_nthRoot]

/-- The finite intensity used by the canonical-root compound-Poisson approximation. -/
noncomputable abbrev _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) : FiniteMeasure ℝ :=
  hμ.compoundPoissonRootIntensity n

/-- The Poisson exponent of the scaled canonical root is its linearized characteristic
function. -/
theorem ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (t : ℝ) :
    ∫ x, LevyTriplet.poissonExponentIntegrand t x
      ∂(hμ.canonicalRootIntensity n : Measure ℝ) =
      canonicalRootLinearization hμ n t := by
  rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
    ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
  change ∫ x, LevyTriplet.poissonExponentIntegrand t x
      ∂(((n + 1 : ℕ) : NNReal) •
        (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ)) = _
  rw [show (((n + 1 : ℕ) : NNReal) •
      (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ)) =
        ((((n + 1 : ℕ) : NNReal) : ENNReal) •
          (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ)) by rfl]
  rw [integral_smul_measure]
  · rw [show (∫ x, LevyTriplet.poissonExponentIntegrand t x
        ∂(hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ)) =
          charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t - 1 by
      have hone : Integrable (fun _ : ℝ => (1 : ℂ))
          (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) := integrable_const 1
      have hexp : Integrable (fun x : ℝ =>
          Complex.exp (((x * t : ℝ) : ℂ) * Complex.I))
          (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) := by
        exact (integrable_const (1 : ℝ)).mono (by fun_prop) <|
          ae_of_all _ fun x => by
            rw [Complex.norm_exp_ofReal_mul_I]
            norm_num
      unfold LevyTriplet.poissonExponentIntegrand
      rw [integral_sub hexp hone]
      have hchar :
          (∫ x, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I)
            ∂(hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ)) =
            charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t := by
        rw [charFun_apply_real]
        apply integral_congr_ae
        filter_upwards [] with x
        congr 2
        push_cast
        ring
      rw [hchar]
      simp]
    rw [canonicalRootLinearization]
    simp only [Complex.real_smul]
    rw [ENNReal.coe_toReal]
    push_cast
    norm_num

theorem ProbabilityMeasure.IsInfinitelyDivisible.tendsto_integral_poissonExponentIntegrand_canonicalRootIntensity
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto
      (fun n => ∫ x, LevyTriplet.poissonExponentIntegrand t x
        ∂(hμ.canonicalRootIntensity n : Measure ℝ))
      atTop (𝓝 (hμ.exponent t)) := by
  simpa only [ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity] using
    ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization hμ t

/-- The finite second-difference measure attached to a scaled canonical root. -/
noncomputable def canonicalRootSecondDifferenceMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (s : ℝ) : Measure ℝ :=
  (hμ.canonicalRootIntensity n : Measure ℝ).withDensity
    (fun x => (LevyTriplet.secondDifferenceWeight s x : ℝ≥0∞))

instance instFiniteCanonicalRootSecondDifferenceMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (s : ℝ) :
    IsFiniteMeasure (canonicalRootSecondDifferenceMeasure hμ n s) := by
  apply IsFiniteMeasure.mk
  rw [canonicalRootSecondDifferenceMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hbound : ∀ x : ℝ, (LevyTriplet.secondDifferenceWeight s x : ℝ≥0∞) ≤ 4 := by
    intro x
    have hreal : (LevyTriplet.secondDifferenceWeight s x : ℝ) ≤ 4 := by
      rw [LevyTriplet.secondDifferenceWeight_coe]
      nlinarith [Real.neg_one_le_cos (s * x)]
    exact_mod_cast hreal
  calc
    ∫⁻ x, (LevyTriplet.secondDifferenceWeight s x : ℝ≥0∞)
        ∂(hμ.canonicalRootIntensity n : Measure ℝ) ≤
        ∫⁻ _ : ℝ, 4 ∂(hμ.canonicalRootIntensity n : Measure ℝ) :=
      lintegral_mono hbound
    _ < ∞ := lintegral_const_lt_top (by norm_num)

/-- Fourier transform of the canonical-root second-difference measure. -/
theorem ProbabilityMeasure.IsInfinitelyDivisible.charFun_canonicalRootSecondDifferenceMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    (n : ℕ) (s t : ℝ) :
    charFun (canonicalRootSecondDifferenceMeasure hμ n s) t =
      -(canonicalRootLinearization hμ n (t + s) +
        canonicalRootLinearization hμ n (t - s) -
        2 * canonicalRootLinearization hμ n t) := by
  rw [charFun_apply_real, canonicalRootSecondDifferenceMeasure,
    integral_withDensity_eq_integral_smul
      (LevyTriplet.measurable_secondDifferenceWeight s)]
  rw [integral_congr_ae (ae_of_all _ fun x => by
    simpa only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul] using
      LevyTriplet.weighted_probChar_eq_neg_secondDifference s t x)]
  rw [integral_neg]
  have hp := LevyTriplet.integrable_poissonExponentIntegrand
    (hμ.canonicalRootIntensity n : Measure ℝ) (t + s)
  have hm := LevyTriplet.integrable_poissonExponentIntegrand
    (hμ.canonicalRootIntensity n : Measure ℝ) (t - s)
  have ht := LevyTriplet.integrable_poissonExponentIntegrand
    (hμ.canonicalRootIntensity n : Measure ℝ) t
  have hpoint (u x : ℝ) :
      levyExponentIntegrand u x = LevyTriplet.poissonExponentIntegrand u x -
        (((u * levyTruncation x : ℝ) : ℂ) * Complex.I) := by
    rw [LevyTriplet.poissonExponentIntegrand_eq_levyExponentIntegrand_add]
    ring
  have hcancel (x : ℝ) :
      levyExponentIntegrand (t + s) x + levyExponentIntegrand (t - s) x -
          2 * levyExponentIntegrand t x =
        LevyTriplet.poissonExponentIntegrand (t + s) x +
          LevyTriplet.poissonExponentIntegrand (t - s) x -
          2 * LevyTriplet.poissonExponentIntegrand t x := by
    simp only [hpoint]
    push_cast
    ring
  rw [integral_congr_ae (ae_of_all _ hcancel)]
  congr 1
  calc
    (∫ x, LevyTriplet.poissonExponentIntegrand (t + s) x +
        LevyTriplet.poissonExponentIntegrand (t - s) x -
        2 * LevyTriplet.poissonExponentIntegrand t x
      ∂(hμ.canonicalRootIntensity n : Measure ℝ)) =
        (∫ x, LevyTriplet.poissonExponentIntegrand (t + s) x +
          LevyTriplet.poissonExponentIntegrand (t - s) x
          ∂(hμ.canonicalRootIntensity n : Measure ℝ)) -
        ∫ x, 2 * LevyTriplet.poissonExponentIntegrand t x
          ∂(hμ.canonicalRootIntensity n : Measure ℝ) :=
      integral_sub (hp.add hm) (ht.const_mul 2)
    _ = ((∫ x, LevyTriplet.poissonExponentIntegrand (t + s) x
          ∂(hμ.canonicalRootIntensity n : Measure ℝ)) +
        ∫ x, LevyTriplet.poissonExponentIntegrand (t - s) x
          ∂(hμ.canonicalRootIntensity n : Measure ℝ)) -
        2 * ∫ x, LevyTriplet.poissonExponentIntegrand t x
          ∂(hμ.canonicalRootIntensity n : Measure ℝ) := by
      rw [integral_add hp hm, integral_const_mul]
    _ = canonicalRootLinearization hμ n (t + s) +
        canonicalRootLinearization hμ n (t - s) -
        2 * canonicalRootLinearization hμ n t := by
      rw [ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity,
        ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity,
        ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity]

/-- The Fourier transforms of the finite extraction measures converge to the second difference
of the normalized exponent. -/
theorem ProbabilityMeasure.IsInfinitelyDivisible.tendsto_charFun_canonicalRootSecondDifferenceMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (s t : ℝ) :
    Tendsto
      (fun n => charFun (canonicalRootSecondDifferenceMeasure hμ n s) t)
      atTop
      (𝓝 (-(hμ.exponent (t + s) + hμ.exponent (t - s) -
        2 * hμ.exponent t))) := by
  rw [show (fun n => charFun (canonicalRootSecondDifferenceMeasure hμ n s) t) =
      fun n => -(canonicalRootLinearization hμ n (t + s) +
        canonicalRootLinearization hμ n (t - s) -
        2 * canonicalRootLinearization hμ n t) by
    funext n
    exact ProbabilityMeasure.IsInfinitelyDivisible.charFun_canonicalRootSecondDifferenceMeasure
      hμ n s t]
  exact (((ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
      hμ (t + s)).add
    (ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
      hμ (t - s))).sub
      ((ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
        hμ t).const_mul 2)).neg

/-- Bundled finite-measure form of the canonical second-difference extraction measure. -/
noncomputable def canonicalRootSecondDifferenceFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (s : ℝ) :
    FiniteMeasure ℝ :=
  ⟨canonicalRootSecondDifferenceMeasure hμ n s,
    instFiniteCanonicalRootSecondDifferenceMeasure hμ n s⟩

@[simp, norm_cast]
theorem coe_canonicalRootSecondDifferenceFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (s : ℝ) :
    (canonicalRootSecondDifferenceFiniteMeasure hμ n s : Measure ℝ) =
      canonicalRootSecondDifferenceMeasure hμ n s := rfl

/-- The limiting Fourier transform of a fixed second-difference extraction family. -/
noncomputable def canonicalRootSecondDifferenceLimitChar
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (s t : ℝ) : ℂ :=
  -(hμ.exponent (t + s) + hμ.exponent (t - s) - 2 * hμ.exponent t)

theorem continuous_canonicalRootSecondDifferenceLimitChar
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (s : ℝ) :
    Continuous (canonicalRootSecondDifferenceLimitChar hμ s) := by
  unfold canonicalRootSecondDifferenceLimitChar
  fun_prop

/-- Existence of the finite weighted limit measure extracted from canonical roots.  This is the
compactness conclusion needed to separate the Gaussian atom at zero from the jump measure in the
converse Lévy--Khintchine theorem. -/
theorem ProbabilityMeasure.IsInfinitelyDivisible.exists_canonicalRootSecondDifferenceLimit
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (s : ℝ) :
    ∃ κ : FiniteMeasure ℝ,
      (∀ t, charFun (κ : Measure ℝ) t =
        canonicalRootSecondDifferenceLimitChar hμ s t) ∧
      Tendsto (fun n => canonicalRootSecondDifferenceFiniteMeasure hμ n s)
        atTop (𝓝 κ) := by
  apply exists_finiteMeasure_of_tendsto_charFun'
    (continuous_canonicalRootSecondDifferenceLimitChar hμ s).continuousAt
  intro t
  simpa [canonicalRootSecondDifferenceLimitChar] using
    ProbabilityMeasure.IsInfinitelyDivisible.tendsto_charFun_canonicalRootSecondDifferenceMeasure
      hμ s t

end ProbabilityTheory
