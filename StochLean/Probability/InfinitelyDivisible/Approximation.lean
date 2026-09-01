/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
public import StochLean.Probability.InfinitelyDivisible.Roots

/-!
# Compound-Poisson approximation of real Levy triplets

This file constructs, entirely inside StochLean, a canonical sequence of finite-intensity
compound-Poisson laws converging weakly to every law represented by a real Levy triplet.  Drift
and Gaussian terms are approximated by small jumps, while the Levy measure is restricted along
the canonical measurable exhaustion away from zero.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

namespace LevyTriplet

noncomputable def finitePointMass (x : ℝ) : FiniteMeasure ℝ :=
  (ProbabilityMeasure.pointMass x).toFiniteMeasure

/-- Drift left after compensating the finite jump restriction under the fixed truncation. -/
noncomputable def compensatedDrift (η : LevyTriplet) (n : ℕ) : ℝ :=
  η.drift - ∫ x, levyTruncation x
    ∂(η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n))

/-- A rate growing fast enough to approximate a possibly varying compensated drift by small
compound-Poisson jumps. -/
noncomputable def driftApproxRate (η : LevyTriplet) (n : ℕ) : ℝ≥0 :=
  (n + 1 : ℝ≥0) * Real.toNNReal (1 + η.compensatedDrift n ^ 2)

noncomputable def driftApproxIntensity (η : LevyTriplet) (n : ℕ) : FiniteMeasure ℝ :=
  if h : η.compensatedDrift n = 0 then 0 else
    η.driftApproxRate n •
      finitePointMass (η.compensatedDrift n / (η.driftApproxRate n : ℝ))

noncomputable def gaussianApproxIntensity (η : LevyTriplet) (n : ℕ) : FiniteMeasure ℝ :=
  if h : η.gaussianVariance = 0 then 0 else
    let a := Real.sqrt ((η.gaussianVariance : ℝ) / (n + 1 : ℝ))
    ((n + 1 : ℝ≥0) / 2) • finitePointMass a +
      ((n + 1 : ℝ≥0) / 2) • finitePointMass (-a)

noncomputable def restrictedJumpIntensity (η : LevyTriplet) (n : ℕ) : FiniteMeasure ℝ :=
  ⟨η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n),
    by simpa only [finiteRestriction] using η.finiteRestriction_jumpMeasure_finite n⟩

noncomputable def compoundPoissonApproxIntensity (η : LevyTriplet) (n : ℕ) :
    FiniteMeasure ℝ :=
  η.driftApproxIntensity n + η.gaussianApproxIntensity n + η.restrictedJumpIntensity n

theorem finitePointMass_apply_zero {x : ℝ} (hx : x ≠ 0) :
    (finitePointMass x : Measure ℝ) {0} = 0 := by
  change Measure.dirac x {0} = 0
  rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]
  simp [hx]

theorem driftApproxIntensity_apply_zero (η : LevyTriplet) (n : ℕ) :
    (η.driftApproxIntensity n : Measure ℝ) {0} = 0 := by
  by_cases h : η.compensatedDrift n = 0
  · simp [driftApproxIntensity, h]
  · rw [driftApproxIntensity, dif_neg h]
    change ((η.driftApproxRate n •
      (finitePointMass (η.compensatedDrift n / (η.driftApproxRate n : ℝ)) : Measure ℝ)) {0}) = 0
    rw [Measure.smul_apply]
    rw [finitePointMass_apply_zero]
    · simp
    · apply div_ne_zero h
      apply NNReal.coe_ne_zero.mpr
      apply ne_of_gt
      rw [driftApproxRate]
      exact mul_pos (by positivity) (Real.toNNReal_pos.mpr (by positivity))

theorem gaussianApproxIntensity_apply_zero (η : LevyTriplet) (n : ℕ) :
    (η.gaussianApproxIntensity n : Measure ℝ) {0} = 0 := by
  by_cases h : η.gaussianVariance = 0
  · simp [gaussianApproxIntensity, h]
  · rw [gaussianApproxIntensity, dif_neg h]
    let a := Real.sqrt ((η.gaussianVariance : ℝ) / (n + 1 : ℝ))
    have hv : 0 < (η.gaussianVariance : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h)
    have ha : a ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
    change ((((n + 1 : ℝ≥0) / 2) • (finitePointMass a : Measure ℝ) +
      ((n + 1 : ℝ≥0) / 2) • (finitePointMass (-a) : Measure ℝ)) {0}) = 0
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      finitePointMass_apply_zero ha, finitePointMass_apply_zero (neg_ne_zero.mpr ha)]
    simp

theorem restrictedJumpIntensity_apply_zero (η : LevyTriplet) (n : ℕ) :
    (η.restrictedJumpIntensity n : Measure ℝ) {0} = 0 := by
  change (η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)) {0} = 0
  rw [Measure.restrict_apply (MeasurableSet.singleton 0)]
  exact measure_mono_null Set.inter_subset_left η.isLevyMeasure_jumpMeasure.atom_zero

theorem compoundPoissonApproxIntensity_apply_zero (η : LevyTriplet) (n : ℕ) :
    (η.compoundPoissonApproxIntensity n : Measure ℝ) {0} = 0 := by
  change (((η.driftApproxIntensity n : Measure ℝ) +
      (η.gaussianApproxIntensity n : Measure ℝ) +
      (η.restrictedJumpIntensity n : Measure ℝ)) {0}) = 0
  rw [Measure.add_apply, Measure.add_apply,
    η.driftApproxIntensity_apply_zero, η.gaussianApproxIntensity_apply_zero,
    η.restrictedJumpIntensity_apply_zero]
  simp

noncomputable def poissonExponentIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) - 1

theorem integral_poissonExponentIntegrand_finitePointMass (t x : ℝ) :
    ∫ y, poissonExponentIntegrand t y ∂(finitePointMass x : Measure ℝ) =
      poissonExponentIntegrand t x := by
  change ∫ y, poissonExponentIntegrand t y ∂Measure.dirac x = _
  rw [integral_dirac]

theorem integral_poissonExponentIntegrand_driftApproxIntensity
    (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    ∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ) =
      if η.compensatedDrift n = 0 then 0 else
        ((η.driftApproxRate n : ℝ) : ℂ) *
          (Complex.exp ((((η.compensatedDrift n * t : ℝ) : ℂ) * Complex.I) /
            (η.driftApproxRate n : ℝ)) - 1) := by
  by_cases h : η.compensatedDrift n = 0
  · simp [driftApproxIntensity, h]
  · rw [driftApproxIntensity, dif_neg h, if_neg h]
    change ∫ x, poissonExponentIntegrand t x
      ∂(η.driftApproxRate n •
        (finitePointMass (η.compensatedDrift n / (η.driftApproxRate n : ℝ)) : Measure ℝ)) = _
    rw [integral_smul_nnreal_measure,
      integral_poissonExponentIntegrand_finitePointMass]
    simp only [NNReal.smul_def, Complex.real_smul]
    push_cast
    unfold poissonExponentIntegrand
    congr 2
    congr 1
    push_cast
    ring

theorem coe_driftApproxRate (η : LevyTriplet) (n : ℕ) :
    (η.driftApproxRate n : ℝ) =
      ((n : ℝ) + 1) * (1 + η.compensatedDrift n ^ 2) := by
  rw [driftApproxRate, NNReal.coe_mul]
  push_cast
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 1 + η.compensatedDrift n ^ 2)]

theorem norm_driftApproxIntensity_error_le (η : LevyTriplet) (n : ℕ) (t : ℝ)
    (ht : |t| ≤ (n : ℝ) + 1) :
    ‖(∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ)) -
        (((η.compensatedDrift n * t : ℝ) : ℂ) * Complex.I)‖ ≤
      t ^ 2 / ((n : ℝ) + 1) := by
  by_cases hc : η.compensatedDrift n = 0
  · simp [integral_poissonExponentIntegrand_driftApproxIntensity, hc]
    positivity
  · rw [integral_poissonExponentIntegrand_driftApproxIntensity, if_neg hc]
    let c := η.compensatedDrift n
    let r := (η.driftApproxRate n : ℝ)
    let z : ℂ := (((c * t : ℝ) : ℂ) * Complex.I) / r
    have hr : r = ((n : ℝ) + 1) * (1 + c ^ 2) := by
      simpa [c, r] using η.coe_driftApproxRate n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hrpos : 0 < r := by rw [hr]; positivity
    have hcabs : |c| ≤ 1 + c ^ 2 := by
      nlinarith [sq_nonneg (|c| - (1 / 2 : ℝ)), sq_abs c]
    have hz_norm : ‖z‖ = |c * t| / r := by
      simp [z, Real.norm_eq_abs, abs_mul]
      rw [abs_of_pos hrpos]
    have hz : ‖z‖ ≤ 1 := by
      rw [hz_norm, div_le_one hrpos]
      calc
        |c * t| = |c| * |t| := abs_mul c t
        _ ≤ (1 + c ^ 2) * ((n : ℝ) + 1) :=
          mul_le_mul hcabs ht (abs_nonneg t) (by positivity)
        _ = r := by rw [hr]; ring
    have hTaylor := Complex.norm_exp_sub_one_sub_id_le hz
    have hlin : ((r : ℂ) * z) = (((c * t : ℝ) : ℂ) * Complex.I) := by
      dsimp [z]
      push_cast
      field_simp [hrpos.ne']
    have herr :
        ((r : ℂ) * (Complex.exp z - 1) -
            (((c * t : ℝ) : ℂ) * Complex.I)) =
          (r : ℂ) * (Complex.exp z - 1 - z) := by
      rw [← hlin]
      ring
    change ‖((r : ℂ) * (Complex.exp z - 1) -
      (((c * t : ℝ) : ℂ) * Complex.I))‖ ≤ _
    rw [herr, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrpos]
    calc
      r * ‖Complex.exp z - 1 - z‖ ≤ r * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hTaylor hrpos.le
      _ = (c ^ 2 * t ^ 2) / r := by
        rw [hz_norm]
        field_simp [hrpos.ne']
        rw [sq_abs, mul_pow]
      _ ≤ t ^ 2 / ((n : ℝ) + 1) := by
        rw [hr]
        have hden : 0 < 1 + c ^ 2 := by positivity
        have hratio : c ^ 2 / (1 + c ^ 2) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        have ht2 : 0 ≤ t ^ 2 / ((n : ℝ) + 1) := div_nonneg (sq_nonneg t) hn.le
        have hmul := mul_le_mul_of_nonneg_right hratio ht2
        calc
          c ^ 2 * t ^ 2 / (((n : ℝ) + 1) * (1 + c ^ 2)) =
              (c ^ 2 / (1 + c ^ 2)) * (t ^ 2 / ((n : ℝ) + 1)) := by
                rw [div_eq_mul_inv]
                field_simp [hn.ne', hden.ne']
          _ ≤ 1 * (t ^ 2 / ((n : ℝ) + 1)) := hmul
          _ = t ^ 2 / ((n : ℝ) + 1) := one_mul _

theorem tendsto_integral_poissonExponentIntegrand_driftApproxIntensity_sub_linear
    (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n =>
      (∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ)) -
        (((η.compensatedDrift n * t : ℝ) : ℂ) * Complex.I)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop |t|)] with n hn
    exact η.norm_driftApproxIntensity_error_le n t (hn.trans (by linarith))
  · convert (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (t ^ 2)) using 1 <;>
      simp [div_eq_mul_inv]

theorem integral_poissonExponentIntegrand_gaussianApproxIntensity
    (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    ∫ x, poissonExponentIntegrand t x ∂(η.gaussianApproxIntensity n : Measure ℝ) =
      if η.gaussianVariance = 0 then 0 else
        (((n : ℝ) + 1) *
          (Real.cos (t * Real.sqrt ((η.gaussianVariance : ℝ) / ((n : ℝ) + 1))) - 1) : ℝ) := by
  by_cases h : η.gaussianVariance = 0
  · simp [gaussianApproxIntensity, h]
  · rw [gaussianApproxIntensity, dif_neg h, if_neg h]
    let a := Real.sqrt ((η.gaussianVariance : ℝ) / ((n : ℝ) + 1))
    have hplus : Integrable (poissonExponentIntegrand t)
        (((n + 1 : ℝ≥0) / 2) • (finitePointMass a : Measure ℝ)) := by
      apply (integrable_const (2 : ℂ)).mono
        (by unfold poissonExponentIntegrand; fun_prop)
      exact ae_of_all _ fun x => by
        unfold poissonExponentIntegrand
        exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp]; norm_num)
    have hminus : Integrable (poissonExponentIntegrand t)
        (((n + 1 : ℝ≥0) / 2) • (finitePointMass (-a) : Measure ℝ)) := by
      apply (integrable_const (2 : ℂ)).mono
        (by unfold poissonExponentIntegrand; fun_prop)
      exact ae_of_all _ fun x => by
        unfold poissonExponentIntegrand
        exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp]; norm_num)
    change ∫ x, poissonExponentIntegrand t x
      ∂((((n + 1 : ℝ≥0) / 2) • (finitePointMass a : Measure ℝ)) +
        (((n + 1 : ℝ≥0) / 2) • (finitePointMass (-a) : Measure ℝ))) = _
    rw [integral_add_measure hplus hminus, integral_smul_nnreal_measure,
      integral_smul_nnreal_measure,
      integral_poissonExponentIntegrand_finitePointMass,
      integral_poissonExponentIntegrand_finitePointMass]
    simp only [NNReal.smul_def, Complex.real_smul]
    dsimp only [poissonExponentIntegrand]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, Complex.cos_neg,
      Complex.sin_neg]
    push_cast
    have haeq : a = Real.sqrt ((η.gaussianVariance : ℝ) * (1 + (n : ℝ))⁻¹) := by
      dsimp [a]
      congr 1
      ring
    rw [haeq]
    ring

theorem tendsto_integral_poissonExponentIntegrand_gaussianApproxIntensity
    (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n => ∫ x, poissonExponentIntegrand t x
      ∂(η.gaussianApproxIntensity n : Measure ℝ)) atTop
      (nhds (-((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ))) := by
  by_cases h : η.gaussianVariance = 0
  · simp [integral_poissonExponentIntegrand_gaussianApproxIntensity, h]
  · have hreal := tendsto_nat_mul_cos_div_sqrt_sub_one
      (t * Real.sqrt (η.gaussianVariance : ℝ))
    have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    convert hcomplex using 1
    · funext n
      rw [integral_poissonExponentIntegrand_gaussianApproxIntensity, if_neg h]
      rw [Real.sqrt_div η.gaussianVariance.coe_nonneg]
      rw [show t * (Real.sqrt (η.gaussianVariance : ℝ) /
          Real.sqrt ((n : ℝ) + 1)) =
        (t * Real.sqrt (η.gaussianVariance : ℝ)) /
          Real.sqrt ((n : ℝ) + 1) by ring]
      rfl
    · congr 1
      rw [← Complex.ofReal_neg]
      congr 1
      rw [mul_pow]
      rw [Real.sq_sqrt η.gaussianVariance.coe_nonneg]
      ring

theorem poissonExponentIntegrand_eq_levyExponentIntegrand_add (t x : ℝ) :
    poissonExponentIntegrand t x = levyExponentIntegrand t x +
      (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) := by
  unfold poissonExponentIntegrand levyExponentIntegrand
  have harg : (((x * t : ℝ) : ℂ) * Complex.I) =
      (((t * x : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [harg]
  ring

theorem integral_poissonExponentIntegrand_restrictedJumpIntensity
    (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    ∫ x, poissonExponentIntegrand t x ∂(η.restrictedJumpIntensity n : Measure ℝ) =
      (∫ x in IsLevyMeasure.spanningLevel n,
        levyExponentIntegrand t x ∂η.jumpMeasure) +
      (((t * ∫ x in IsLevyMeasure.spanningLevel n,
        levyTruncation x ∂η.jumpMeasure : ℝ) : ℂ) * Complex.I) := by
  let νn := η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)
  letI : IsFiniteMeasure νn := η.finiteRestriction_jumpMeasure_finite n
  have hlevy : Integrable (levyExponentIntegrand t) νn :=
    (η.integrable_exponent_jump t).restrict
  have htrunc : Integrable levyTruncation νn :=
    CompoundPoisson.integrable_levyTruncation νn
  have hcorr : Integrable
      (fun x => (((t * levyTruncation x : ℝ) : ℂ) * Complex.I)) νn :=
    ((htrunc.const_mul t).ofReal.mul_const Complex.I)
  change ∫ x, poissonExponentIntegrand t x ∂νn = _
  rw [integral_congr_ae (ae_of_all _ fun x =>
    poissonExponentIntegrand_eq_levyExponentIntegrand_add t x)]
  rw [integral_add hlevy hcorr]
  have hcast :
      (∫ x, ((t * levyTruncation x : ℝ) : ℂ) ∂νn) =
        ((∫ x, t * levyTruncation x ∂νn : ℝ) : ℂ) := integral_ofReal
  rw [integral_mul_const, hcast, integral_const_mul]

theorem integral_driftApprox_add_restrictedJumpIntensity
    (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    (∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ)) +
      (∫ x, poissonExponentIntegrand t x ∂(η.restrictedJumpIntensity n : Measure ℝ)) =
      ((∫ x, poissonExponentIntegrand t x
          ∂(η.driftApproxIntensity n : Measure ℝ)) -
        (((η.compensatedDrift n * t : ℝ) : ℂ) * Complex.I)) +
      (((η.drift * t : ℝ) : ℂ) * Complex.I) +
      (∫ x in IsLevyMeasure.spanningLevel n,
        levyExponentIntegrand t x ∂η.jumpMeasure) := by
  rw [integral_poissonExponentIntegrand_restrictedJumpIntensity]
  unfold compensatedDrift
  push_cast
  ring

theorem tendsto_integral_driftApprox_add_restrictedJumpIntensity
    (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n =>
      (∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ)) +
      (∫ x, poissonExponentIntegrand t x ∂(η.restrictedJumpIntensity n : Measure ℝ)))
      atTop (nhds (
        (((η.drift * t : ℝ) : ℂ) * Complex.I) +
        ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure)) := by
  have hint := tendsto_setIntegral_of_monotone
    (fun n => IsLevyMeasure.measurableSet_spanningLevel n)
    IsLevyMeasure.monotone_spanningLevel
    ((η.integrable_exponent_jump t).integrableOn)
  rw [η.restrict_iUnion_spanningLevel] at hint
  have hright : Tendsto (fun n =>
      (((η.drift * t : ℝ) : ℂ) * Complex.I) +
        ∫ x in IsLevyMeasure.spanningLevel n,
          levyExponentIntegrand t x ∂η.jumpMeasure) atTop
      (nhds ((((η.drift * t : ℝ) : ℂ) * Complex.I) +
        ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure)) :=
    tendsto_const_nhds.add hint
  have hsum :=
    (η.tendsto_integral_poissonExponentIntegrand_driftApproxIntensity_sub_linear t).add hright
  convert hsum using 1
  · funext n
    rw [η.integral_driftApprox_add_restrictedJumpIntensity n t]
    ring
  · ring

theorem integrable_poissonExponentIntegrand (ν : Measure ℝ) [IsFiniteMeasure ν]
    (t : ℝ) : Integrable (poissonExponentIntegrand t) ν := by
  have hm : Measurable (poissonExponentIntegrand t) := by
    unfold poissonExponentIntegrand
    fun_prop
  apply (integrable_const (2 : ℝ)).mono
    hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    unfold poissonExponentIntegrand
    exact (norm_sub_le _ _).trans (by rw [Complex.norm_exp]; norm_num)

theorem integral_poissonExponentIntegrand_compoundPoissonApproxIntensity
    (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    ∫ x, poissonExponentIntegrand t x
        ∂(η.compoundPoissonApproxIntensity n : Measure ℝ) =
      (∫ x, poissonExponentIntegrand t x ∂(η.driftApproxIntensity n : Measure ℝ)) +
      (∫ x, poissonExponentIntegrand t x ∂(η.gaussianApproxIntensity n : Measure ℝ)) +
      (∫ x, poissonExponentIntegrand t x ∂(η.restrictedJumpIntensity n : Measure ℝ)) := by
  change ∫ x, poissonExponentIntegrand t x ∂((η.driftApproxIntensity n : Measure ℝ) +
      (η.gaussianApproxIntensity n : Measure ℝ) +
      (η.restrictedJumpIntensity n : Measure ℝ)) = _
  rw [integral_add_measure (integrable_poissonExponentIntegrand _ t)
      (integrable_poissonExponentIntegrand _ t),
    integral_add_measure (integrable_poissonExponentIntegrand _ t)
      (integrable_poissonExponentIntegrand _ t)]

theorem tendsto_integral_poissonExponentIntegrand_compoundPoissonApproxIntensity
    (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n => ∫ x, poissonExponentIntegrand t x
      ∂(η.compoundPoissonApproxIntensity n : Measure ℝ)) atTop
      (nhds (η.exponent t)) := by
  have hgauss :=
    η.tendsto_integral_poissonExponentIntegrand_gaussianApproxIntensity t
  have hdj := η.tendsto_integral_driftApprox_add_restrictedJumpIntensity t
  have hsum := hgauss.add hdj
  convert hsum using 1
  · funext n
    rw [η.integral_poissonExponentIntegrand_compoundPoissonApproxIntensity n t]
    ring
  · unfold exponent
    ring

/-- Canonical compound-Poisson approximation law of a real Lévy triplet. -/
noncomputable def compoundPoissonApproxLaw (η : LevyTriplet) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  CompoundPoisson.ofFiniteMeasure (η.compoundPoissonApproxIntensity n)

theorem charFun_compoundPoissonApproxLaw (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    charFun (η.compoundPoissonApproxLaw n : Measure ℝ) t =
      Complex.exp (∫ x, poissonExponentIntegrand t x
        ∂(η.compoundPoissonApproxIntensity n : Measure ℝ)) := by
  have hrep := CompoundPoisson.tripletOfFiniteMeasure_represents
    (η.compoundPoissonApproxIntensity n)
    (η.compoundPoissonApproxIntensity_apply_zero n)
  change charFun
    (CompoundPoisson.ofFiniteMeasure (η.compoundPoissonApproxIntensity n) : Measure ℝ) t = _
  rw [hrep t]
  rw [CompoundPoisson.exponent_tripletOfFiniteMeasure]
  rfl

theorem tendsto_charFun_compoundPoissonApproxLaw (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n => charFun (η.compoundPoissonApproxLaw n : Measure ℝ) t)
      atTop (nhds (Complex.exp (η.exponent t))) := by
  have h := Complex.continuous_exp.continuousAt.tendsto.comp
    (η.tendsto_integral_poissonExponentIntegrand_compoundPoissonApproxIntensity t)
  simpa [η.charFun_compoundPoissonApproxLaw, Function.comp_def] using h

/-- Every law represented by a real Lévy triplet is a weak limit of compound-Poisson laws.  This
is the constructive approximation direction of Klenke's Theorem 16.5. -/
theorem tendsto_compoundPoissonApproxLaw {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) :
    Tendsto η.compoundPoissonApproxLaw atTop (nhds μ) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [hη t]
  exact η.tendsto_charFun_compoundPoissonApproxLaw t

end LevyTriplet

/-- A real probability law is a weak limit of finite-intensity compound-Poisson laws.  The
intensity measures themselves are retained as witnesses, so this predicate cannot be satisfied by
an unrelated sequence of probability laws. -/
def IsWeakLimitOfCompoundPoisson (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ intensity : ℕ → FiniteMeasure ℝ,
    Tendsto (fun n => CompoundPoisson.ofFiniteMeasure (intensity n)) atTop (nhds μ)

/-- Constructive Theorem 16.5 direction for every law carrying a Lévy--Khintchine triplet. -/
theorem LevyTriplet.Represents.isWeakLimitOfCompoundPoisson
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ) :
    IsWeakLimitOfCompoundPoisson μ :=
  ⟨η.compoundPoissonApproxIntensity, LevyTriplet.tendsto_compoundPoissonApproxLaw hη⟩

/-! ## Root-based compound-Poisson approximation -/

/-- Finite intensity obtained by multiplying the canonical `(n+1)`st root law by `n+1`. -/
noncomputable def _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) : FiniteMeasure ℝ :=
  ((n + 1 : ℕ) : ℝ≥0) • (hμ.nthRoot (n + 1) (Nat.succ_pos n)).toFiniteMeasure

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootLaw_eq
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) :
    CompoundPoisson.ofFiniteMeasure (hμ.compoundPoissonRootIntensity n) =
      CompoundPoisson.law ((n + 1 : ℕ) : ℝ≥0)
        (hμ.nthRoot (n + 1) (Nat.succ_pos n)) := by
  exact CompoundPoisson.ofFiniteMeasure_smul_probability _ _

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_charFun_compoundPoissonRootLaw
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto
      (fun n => charFun
        (CompoundPoisson.ofFiniteMeasure (hμ.compoundPoissonRootIntensity n) : Measure ℝ) t)
      atTop (nhds (charFun (μ : Measure ℝ) t)) := by
  have hinner := tendsto_nat_mul_cexp_sub_one_div (hμ.exponent t)
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp hinner
  rw [← hμ.exp_exponent t]
  convert hexp using 1
  funext n
  rw [hμ.compoundPoissonRootLaw_eq, CompoundPoisson.charFun_law,
    hμ.charFun_nthRoot]
  push_cast
  rfl

/-- Every infinitely divisible real law is a weak limit of finite-intensity compound-Poisson
laws.  This is the difficult direction of Klenke's Theorem 16.5, obtained without importing an
external infinitely-divisible package. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.isWeakLimitOfCompoundPoisson
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    IsWeakLimitOfCompoundPoisson μ := by
  refine ⟨hμ.compoundPoissonRootIntensity, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  exact hμ.tendsto_charFun_compoundPoissonRootLaw

end ProbabilityTheory
