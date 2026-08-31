/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import StochLean.Probability.Process.StationaryIndependentIncrements

/-!
# Brownian process bridges and time inversion

Mathlib's canonical `IsPreBrownianReal` and `IsBrownianReal` predicates are reused.  The only new
transformation here is a source-facing piecewise spelling of time inversion which treats time zero
as a genuine branch and is proved equal to Mathlib's implementation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- The canonical one-time Brownian increment law. -/
noncomputable def brownianIncrementLaw (t : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 t, inferInstance⟩

@[simp, norm_cast]
theorem coe_brownianIncrementLaw (t : ℝ≥0) :
    ((brownianIncrementLaw t : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal 0 t :=
  rfl

/-- The Brownian bridge transform on the natural time interval `0 ≤ t ≤ 1`.

The function is defined on all nonnegative times so that callers may choose either an interval
subtype or explicit interval hypotheses at the API boundary. -/
noncomputable def brownianBridge (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ B t ω - (t : ℝ) * B 1 ω

@[simp]
theorem brownianBridge_one (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : brownianBridge B 1 ω = 0 := by
  simp [brownianBridge]

theorem IsPreBrownianReal.brownianBridge_zero_ae (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, brownianBridge B 0 ω = 0 := by
  simpa [brownianBridge] using hB.eval_zero_ae_eq_zero

/-- A Brownian bridge is a Gaussian process. -/
theorem IsPreBrownianReal.brownianBridge_isGaussianProcess (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (brownianBridge B) P := by
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  classical
  refine ⟨{t, 1},
    { toFun := fun x ↦ x ⟨t, by simp⟩ - (t : ℝ) * x ⟨1, by simp⟩
      map_add' := by intro x y; simp; ring
      map_smul' := by intro c x; simp; ring }, ?_⟩
  intro ω
  simp [brownianBridge]

theorem IsPreBrownianReal.integral_brownianBridge (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    P[brownianBridge B t] = 0 := by
  change ∫ ω, (B t ω - (t : ℝ) * B 1 ω) ∂P = 0
  rw [integral_sub (hB.integrable_eval t) ((hB.integrable_eval 1).const_mul (t : ℝ)),
    integral_const_mul, hB.integral_eval, hB.integral_eval]
  simp

/-- Covariance of the Brownian bridge on its natural unit interval. -/
theorem IsPreBrownianReal.covariance_brownianBridge (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (hs : s ≤ 1) (ht : t ≤ 1) :
    cov[brownianBridge B s, brownianBridge B t; P] =
      ((min s t : ℝ≥0) : ℝ) - (s : ℝ) * (t : ℝ) := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  have hslp : MemLp (B s) 2 P := hB.isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two
  have htlp : MemLp (B t) 2 P := hB.isGaussianProcess.hasGaussianLaw_eval t |>.memLp_two
  have h1lp : MemLp (B 1) 2 P := hB.isGaussianProcess.hasGaussianLaw_eval 1 |>.memLp_two
  change cov[fun ω ↦ B s ω - (s : ℝ) * B 1 ω,
    fun ω ↦ B t ω - (t : ℝ) * B 1 ω; P] = _
  rw [covariance_fun_sub_fun_sub hslp (h1lp.const_mul (s : ℝ)) htlp
    (h1lp.const_mul (t : ℝ))]
  rw [covariance_const_mul_right, covariance_const_mul_left,
    covariance_const_mul_left, covariance_const_mul_right]
  rw [hB.covariance_eval, hB.covariance_eval, hB.covariance_eval,
    hB.covariance_eval]
  rw [min_eq_left hs, min_eq_right ht]
  simp
  ring

/-- A Brownian-bridge marginal at `t ∈ [0,1]` is centered Gaussian with variance `t(1-t)`. -/
theorem IsPreBrownianReal.hasLaw_brownianBridge (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (ht : t ≤ 1) :
    HasLaw (brownianBridge B t) (gaussianReal 0 (t * (1 - t))) P := by
  have hG := hB.brownianBridge_isGaussianProcess.hasGaussianLaw_eval t
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal]
  congr 2
  · exact hB.integral_brownianBridge t
  · have hcov := hB.covariance_brownianBridge t t ht ht
    rw [covariance_self hG.aemeasurable] at hcov
    simp only [min_self] at hcov
    apply NNReal.eq
    rw [hcov]
    have ht' : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    rw [Real.coe_toNNReal _ (by nlinarith [t.coe_nonneg])]
    rw [NNReal.coe_mul, NNReal.coe_sub ht]
    simp
    ring

/-- Brownian time inversion with its natural `t = 0` branch exposed. -/
noncomputable def brownianTimeInversion (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if t = 0 then 0 else t * B (1 / t) ω

theorem brownianTimeInversion_eq (B : ℝ≥0 → Ω → ℝ) :
    brownianTimeInversion B = fun t ω ↦ t * B (1 / t) ω := by
  funext t ω
  by_cases ht : t = 0 <;> simp [brownianTimeInversion, ht]

@[simp]
theorem brownianTimeInversion_zero (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    brownianTimeInversion B 0 ω = 0 := by
  simp [brownianTimeInversion]

theorem brownianTimeInversion_of_pos (B : ℝ≥0 → Ω → ℝ) {t : ℝ≥0} (ht : 0 < t) (ω : Ω) :
    brownianTimeInversion B t ω = t * B (1 / t) ω := by
  simp [brownianTimeInversion, ht.ne']

/-- The explicit piecewise time inversion preserves the pre-Brownian finite-dimensional law. -/
theorem IsPreBrownianReal.timeInversion (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (brownianTimeInversion B) P := by
  rw [brownianTimeInversion_eq]
  exact hB.inv

private theorem nndist_coe_add_left (s t : ℝ≥0) :
    nndist ((s + t : ℝ≥0) : ℝ) (s : ℝ) = t := by
  rw [Real.nndist_eq]
  apply NNReal.eq
  simp

private theorem nndist_coe_zero (t : ℝ≥0) :
    nndist (t : ℝ) (0 : ℝ) = t := by
  rw [Real.nndist_eq]
  apply NNReal.eq
  simp

/-- A pre-Brownian process has stationary independent increments. -/
theorem IsPreBrownianReal.hasStationaryIndependentIncrements (hB : IsPreBrownianReal B P) :
    HasStationaryIndependentIncrements B P := by
  refine ⟨?_, hB.hasIndepIncrements⟩
  intro s t
  have hlater : HasLaw (fun ω ↦ B (s + t) ω - B s ω) (gaussianReal 0 t) P := by
    have h := hB.hasLaw_sub (s + t) s
    refine ⟨?_, ?_⟩
    · change AEMeasurable (B (s + t) - B s) P
      exact h.aemeasurable
    · change P.map (B (s + t) - B s) = gaussianReal 0 t
      exact h.map_eq.trans (congrArg (gaussianReal 0) (nndist_coe_add_left s t))
  have hzero : HasLaw (fun ω ↦ B t ω - B 0 ω) (gaussianReal 0 t) P := by
    have h := hB.hasLaw_sub t 0
    refine ⟨?_, ?_⟩
    · change AEMeasurable (B t - B 0) P
      exact h.aemeasurable
    · change P.map (B t - B 0) = gaussianReal 0 t
      exact h.map_eq.trans (congrArg (gaussianReal 0) (nndist_coe_zero t))
  exact hlater.identDistrib hzero

theorem IsPreBrownianReal.hasIncrementLawFamily (hB : IsPreBrownianReal B P) :
    HasIncrementLawFamily B brownianIncrementLaw P := by
  intro t
  have h := hB.hasLaw_sub t 0
  refine ⟨?_, ?_⟩
  · change AEMeasurable (B t - B 0) P
    exact h.aemeasurable
  · change P.map (B t - B 0) = gaussianReal 0 t
    exact h.map_eq.trans (congrArg (gaussianReal 0) (nndist_coe_zero t))

/-- Brownian increment laws form a convolution semigroup. -/
theorem IsPreBrownianReal.brownianIncrementLaw_isConvolutionSemigroup
    (hB : IsPreBrownianReal B P) : IsConvolutionSemigroup brownianIncrementLaw :=
  hB.hasStationaryIndependentIncrements.isConvolutionSemigroup hB.hasIncrementLawFamily

/-- Each Brownian marginal is infinitely divisible. -/
theorem IsPreBrownianReal.brownianIncrementLaw_isInfinitelyDivisible
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ProbabilityMeasure.IsInfinitelyDivisible (brownianIncrementLaw t) :=
  hB.brownianIncrementLaw_isConvolutionSemigroup.isInfinitelyDivisible t

end ProbabilityTheory
