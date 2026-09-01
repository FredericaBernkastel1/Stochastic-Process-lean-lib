/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyMeasure
public import StochLean.Probability.InfinitelyDivisible.CompoundPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The fixed source truncation `x 1_{|x|<1}`. -/
noncomputable def levyTruncation (x : ℝ) : ℝ := if |x| < 1 then x else 0

@[simp]
theorem levyTruncation_zero : levyTruncation 0 = 0 := by
  simp [levyTruncation]

theorem levyTruncation_of_abs_lt_one {x : ℝ} (hx : |x| < 1) : levyTruncation x = x := by
  simp [levyTruncation, hx]

theorem levyTruncation_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : levyTruncation x = 0 := by
  simp [levyTruncation, not_lt.mpr hx]

theorem measurable_levyTruncation : Measurable levyTruncation := by
  unfold levyTruncation
  exact Measurable.ite (by measurability) measurable_id measurable_const

/-- The jump part of the real Lévy--Khintchine exponent, under the fixed strict truncation. -/
noncomputable def levyExponentIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
    ((t * levyTruncation x : ℝ) : ℂ) * Complex.I

/-- A simple global domination constant for the Lévy exponent integrand. -/
noncomputable def levyExponentBound (t : ℝ) : ℝ :=
  2 + (3 + |t|) * t ^ 2

theorem measurable_levyExponentIntegrand (t : ℝ) : Measurable (levyExponentIntegrand t) := by
  unfold levyExponentIntegrand
  have htrunc : Measurable levyTruncation := measurable_levyTruncation
  fun_prop

/-- The Lévy exponent integrand is globally dominated by the defining truncated second moment.
The proof uses the quadratic complex-exponential remainder for small jumps and the uniform bound
on the unit circle for large jumps. -/
theorem norm_levyExponentIntegrand_le (t x : ℝ) :
    ‖levyExponentIntegrand t x‖ ≤ levyExponentBound t * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hx]
    have htrunc : levyTruncation x = x := levyTruncation_of_abs_lt_one hx
    rw [levyExponentIntegrand, htrunc]
    by_cases hz : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ≤ 1
    · have hTaylor := Complex.norm_exp_sub_one_sub_id_le hz
      have htx : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 * x ^ 2 := by
        simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
        rw [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs, sq_abs]
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((t * x : ℝ) : ℂ) * Complex.I‖ ≤
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 := hTaylor
        _ = t ^ 2 * x ^ 2 := htx
        _ ≤ levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
    · have hz' : 1 < |t * x| := by
        simpa [abs_mul] using lt_of_not_ge hz
      have hsq : 1 < t ^ 2 * x ^ 2 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
          _ < |t * x| ^ 2 := (sq_lt_sq₀ zero_le_one (abs_nonneg (t * x))).mpr hz'
          _ = t ^ 2 * x ^ 2 := by rw [abs_mul, mul_pow, sq_abs, sq_abs]
      have hrough :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              ((t * x : ℝ) : ℂ) * Complex.I‖ ≤ 2 + |t| := by
        calc
          _ ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
              ‖((t * x : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ (1 + 1) + |t * x| := by
            gcongr
            · calc
                ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
                    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le _ _
                _ = 1 + 1 := by
                  rw [Complex.norm_exp]
                  simp [Complex.mul_re]
            · simp
          _ ≤ 2 + |t| := by
            rw [abs_mul]
            nlinarith [mul_le_mul_of_nonneg_left hx.le (abs_nonneg t)]
      calc
        _ ≤ 2 + |t| := hrough
        _ ≤ (2 + |t|) * (t ^ 2 * x ^ 2) := by
          exact le_mul_of_one_le_right (by positivity) hsq.le
        _ = ((2 + |t|) * t ^ 2) * x ^ 2 := by ring
        _ ≤ levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    rw [levyIntegrand_toReal_of_one_le_abs hx']
    have htrunc : levyTruncation x = 0 := levyTruncation_of_one_le_abs hx'
    rw [levyExponentIntegrand, htrunc]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
        norm_num
      _ ≤ levyExponentBound t := by
        unfold levyExponentBound
        nlinarith [mul_nonneg (by positivity : 0 ≤ 3 + |t|) (sq_nonneg t)]

/-- The jump integral in the Lévy exponent is well-defined for every real frequency under exactly
the minimal Lévy-measure assumptions. -/
theorem IsLevyMeasure.integrable_levyExponentIntegrand {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) (t : ℝ) : Integrable (levyExponentIntegrand t) ν := by
  have hbase : Integrable (fun x => (levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      hν.lintegral_lt_top.ne
  have hdom : Integrable (fun x => levyExponentBound t * (levyIntegrand x).toReal) ν :=
    hbase.const_mul _
  apply hdom.mono'
  · exact (measurable_levyExponentIntegrand t).aestronglyMeasurable
  · exact ae_of_all _ fun x => norm_levyExponentIntegrand_le t x

/-- The correction forced by transporting the fixed truncation under `x ↦ a*x`. -/
noncomputable def affineDriftIntegrand (a x : ℝ) : ℝ :=
  levyTruncation (a * x) - a * levyTruncation x

theorem measurable_affineDriftIntegrand (a : ℝ) : Measurable (affineDriftIntegrand a) := by
  unfold affineDriftIntegrand
  exact (measurable_levyTruncation.comp (by fun_prop)).sub
    (measurable_const.mul measurable_levyTruncation)

/-- The affine drift correction is controlled by the same minimal Lévy integrand.  In particular,
no finiteness assumption on the whole jump measure is introduced. -/
theorem norm_affineDriftIntegrand_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖affineDriftIntegrand a x‖ ≤ max 1 (a ^ 2) * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hx]
    rw [affineDriftIntegrand, levyTruncation_of_abs_lt_one hx]
    by_cases hax : |a * x| < 1
    · rw [levyTruncation_of_abs_lt_one hax]
      simp [sq_nonneg]
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hax)]
      simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos ha]
      have hone : 1 ≤ a * |x| := by
        simpa [abs_mul, abs_of_pos ha] using le_of_not_gt hax
      have hself : a * |x| ≤ (a * |x|) ^ 2 := by nlinarith
      have hmain : a * |x| ≤ a ^ 2 * x ^ 2 := by
        calc
          a * |x| ≤ (a * |x|) ^ 2 := hself
          _ = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
      exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x))
  · rw [levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hx)]
    rw [affineDriftIntegrand, levyTruncation_of_one_le_abs (le_of_not_gt hx)]
    simp only [mul_zero, sub_zero, Real.norm_eq_abs]
    by_cases hax : |a * x| < 1
    · rw [levyTruncation_of_abs_lt_one hax]
      simpa using (le_of_lt hax).trans (le_max_left (1 : ℝ) (a ^ 2))
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hax)]
      simp

theorem IsLevyMeasure.integrable_affineDriftIntegrand {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) {a : ℝ} (ha : 0 < a) : Integrable (affineDriftIntegrand a) ν := by
  have hbase : Integrable (fun x => (levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      hν.lintegral_lt_top.ne
  apply (hbase.const_mul (max 1 (a ^ 2))).mono'
  · exact (measurable_affineDriftIntegrand a).aestronglyMeasurable
  · exact ae_of_all _ (norm_affineDriftIntegrand_le ha)

/-- A real Lévy triplet under the fixed strict truncation convention. -/
structure LevyTriplet where
  gaussianVariance : ℝ≥0
  drift : ℝ
  jumpMeasure : Measure ℝ
  isLevyMeasure_jumpMeasure : IsLevyMeasure jumpMeasure

namespace LevyTriplet

/-- The real Lévy--Khintchine exponent under the fixed strict truncation convention. -/
noncomputable def exponent (η : LevyTriplet) (t : ℝ) : ℂ :=
  -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    ((η.drift * t : ℝ) : ℂ) * Complex.I +
      ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure

/-- A triplet represents a real probability law when the characteristic function is the
exponential of its fixed-truncation exponent. -/
def Represents (η : LevyTriplet) (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ t, charFun (μ : Measure ℝ) t = Complex.exp (η.exponent t)

/-- Existence and uniqueness of a representing triplet, separated from the triplet data itself. -/
def HasUniqueLevyTriplet (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃! η : LevyTriplet, η.Represents μ

theorem HasUniqueLevyTriplet.unique {μ : ProbabilityMeasure ℝ}
    (hμ : HasUniqueLevyTriplet μ) {η η' : LevyTriplet}
    (hη : η.Represents μ) (hη' : η'.Represents μ) : η = η' := by
  obtain ⟨canonical, hcanonical, hunique⟩ := hμ
  exact (hunique η hη).trans (hunique η' hη').symm

theorem Represents.charFun_ne_zero {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (h : η.Represents μ) (t : ℝ) : charFun (μ : Measure ℝ) t ≠ 0 := by
  rw [h t]
  exact Complex.exp_ne_zero _

theorem integrable_exponent_jump (η : LevyTriplet) (t : ℝ) :
    Integrable (levyExponentIntegrand t) η.jumpMeasure :=
  η.isLevyMeasure_jumpMeasure.integrable_levyExponentIntegrand t

@[simp]
theorem exponent_zero (η : LevyTriplet) : η.exponent 0 = 0 := by
  simp [exponent, levyExponentIntegrand]

/-- The zero triplet. -/
noncomputable def zero : LevyTriplet where
  gaussianVariance := 0
  drift := 0
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_zeroTriplet (t : ℝ) : zero.exponent t = 0 := by
  simp [zero, exponent]

/-- The canonical triplet of a Dirac law under the fixed truncation. -/
noncomputable def pointMass (x : ℝ) : LevyTriplet where
  gaussianVariance := 0
  drift := x
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_pointMass (x t : ℝ) : (pointMass x).exponent t =
    ((x * t : ℝ) : ℂ) * Complex.I := by
  simp [pointMass, exponent]

theorem represents_pointMass (x : ℝ) :
    (pointMass x).Represents (ProbabilityMeasure.pointMass x) := by
  intro t
  rw [ProbabilityMeasure.coe_pointMass, charFun_dirac, exponent_pointMass]
  congr 1
  rw [Real.inner_apply]

/-- The canonical probability-measure wrapper around Mathlib's real Gaussian law. -/
noncomputable def gaussianLaw (m : ℝ) (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal m v, inferInstance⟩

@[simp, norm_cast]
theorem coe_gaussianLaw (m : ℝ) (v : ℝ≥0) :
    ((gaussianLaw m v : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal m v := rfl

/-- The no-jump Gaussian triplet. -/
noncomputable def gaussian (m : ℝ) (v : ℝ≥0) : LevyTriplet where
  gaussianVariance := v
  drift := m
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_gaussian (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (gaussian m v).exponent t =
      -((((v : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) + ((m * t : ℝ) : ℂ) * Complex.I := by
  simp [gaussian, exponent]

theorem gaussian_represents_gaussianLaw (m : ℝ) (v : ℝ≥0) :
    (gaussian m v).Represents (gaussianLaw m v) := by
  intro t
  rw [coe_gaussianLaw, charFun_gaussianReal, exponent_gaussian]
  congr 1
  push_cast
  ring

/-- Addition of independent Lévy triplets. -/
noncomputable def add (η ξ : LevyTriplet) : LevyTriplet where
  gaussianVariance := η.gaussianVariance + ξ.gaussianVariance
  drift := η.drift + ξ.drift
  jumpMeasure := η.jumpMeasure + ξ.jumpMeasure
  isLevyMeasure_jumpMeasure :=
    η.isLevyMeasure_jumpMeasure.add ξ.isLevyMeasure_jumpMeasure

@[simp]
theorem exponent_add (η ξ : LevyTriplet) (t : ℝ) :
    (η.add ξ).exponent t = η.exponent t + ξ.exponent t := by
  simp only [exponent, add, NNReal.coe_add]
  rw [integral_add_measure (η.integrable_exponent_jump t) (ξ.integrable_exponent_jump t)]
  push_cast
  ring

theorem Represents.add {η ξ : LevyTriplet} {μ ν : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) (hξ : ξ.Represents ν) :
    (η.add ξ).Represents (ProbabilityMeasure.conv μ ν) := by
  intro t
  rw [ProbabilityMeasure.coe_conv, charFun_conv, hη t, hξ t, exponent_add,
    Complex.exp_add]

/-- Nonnegative-real scaling of all triplet components. -/
noncomputable def nnrealSMul (r : ℝ≥0) (η : LevyTriplet) : LevyTriplet where
  gaussianVariance := r * η.gaussianVariance
  drift := (r : ℝ) * η.drift
  jumpMeasure := r • η.jumpMeasure
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.smul r

@[simp]
theorem exponent_nnrealSMul (r : ℝ≥0) (η : LevyTriplet) (t : ℝ) :
    (η.nnrealSMul r).exponent t = (r : ℂ) * η.exponent t := by
  simp only [exponent, nnrealSMul, NNReal.coe_mul,
    MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [Complex.real_smul]
  push_cast
  ring

@[simp]
theorem nnrealSMul_zero (η : LevyTriplet) : η.nnrealSMul 0 = zero := by
  cases η
  simp [nnrealSMul, zero]

@[simp]
theorem nnrealSMul_one (η : LevyTriplet) : η.nnrealSMul 1 = η := by
  cases η
  simp [nnrealSMul]

theorem nnrealSMul_add (r s : ℝ≥0) (η : LevyTriplet) :
    η.nnrealSMul (r + s) = (η.nnrealSMul r).add (η.nnrealSMul s) := by
  cases η
  simp [nnrealSMul, add, add_smul, add_mul]

/-- Convolution-power scaling of triplet data. -/
noncomputable def nsmul (n : ℕ) (η : LevyTriplet) : LevyTriplet where
  gaussianVariance := n • η.gaussianVariance
  drift := n • η.drift
  jumpMeasure := (n : ℝ≥0) • η.jumpMeasure
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.smul n

@[simp]
theorem nsmul_gaussianVariance (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).gaussianVariance = n • η.gaussianVariance := rfl

@[simp]
theorem nsmul_drift (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).drift = n • η.drift := rfl

@[simp]
theorem nsmul_jumpMeasure (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).jumpMeasure = (n : ℝ≥0) • η.jumpMeasure := rfl

/-- Convolution-power scaling multiplies the full Lévy exponent by the same natural number. -/
theorem exponent_nsmul (n : ℕ) (η : LevyTriplet) (t : ℝ) :
    (η.nsmul n).exponent t = (n : ℂ) * η.exponent t := by
  simp only [exponent, nsmul_gaussianVariance, nsmul_drift, nsmul_jumpMeasure,
    MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem Represents.nsmul {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (h : η.Represents μ) (n : ℕ) :
    (η.nsmul n).Represents (ProbabilityMeasure.convPow μ n) := by
  intro t
  rw [CompoundPoisson.charFun_convPow, h t, exponent_nsmul, ← Complex.exp_nat_mul]

/-- The canonical triplet of the positive affine image `a*X+d` under the fixed strict
truncation.  The integral term is essential: omitting it changes the characteristic exponent. -/
noncomputable def affine (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) : LevyTriplet where
  gaussianVariance := (Real.toNNReal a) ^ 2 * η.gaussianVariance
  drift := a * η.drift + d + ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure
  jumpMeasure := η.jumpMeasure.map (fun x => a * x)
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.map_mul ha.ne'

@[simp]
theorem affine_gaussianVariance (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).gaussianVariance =
      (Real.toNNReal a) ^ 2 * η.gaussianVariance := rfl

@[simp]
theorem affine_drift (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).drift =
      a * η.drift + d + ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure := rfl

@[simp]
theorem affine_jumpMeasure (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).jumpMeasure = η.jumpMeasure.map (fun x => a * x) := rfl

theorem levyExponentIntegrand_mul (a t x : ℝ) :
    levyExponentIntegrand t (a * x) = levyExponentIntegrand (a * t) x -
      (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I) := by
  unfold levyExponentIntegrand affineDriftIntegrand
  have hexpArg : (((t * (a * x) : ℝ) : ℂ) * Complex.I) =
      ((((a * t) * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexpArg]
  push_cast
  ring

/-- Positive affine transport of a triplet has the expected exponent.  The proof displays the
cancellation between the transported jump truncation and `affineDriftIntegrand`. -/
theorem exponent_affine (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) (t : ℝ) :
    (η.affine a d ha).exponent t =
      η.exponent (a * t) + ((d * t : ℝ) : ℂ) * Complex.I := by
  have hmap :
      (∫ x, levyExponentIntegrand t x ∂(η.jumpMeasure.map fun x => a * x)) =
        ∫ x, levyExponentIntegrand t (a * x) ∂η.jumpMeasure := by
    rw [integral_map (by fun_prop)
      (measurable_levyExponentIntegrand t).aestronglyMeasurable]
  have hcorr := η.isLevyMeasure_jumpMeasure.integrable_affineDriftIntegrand ha
  have hexp := η.isLevyMeasure_jumpMeasure.integrable_levyExponentIntegrand (a * t)
  have hcorrC : Integrable
      (fun x => (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) η.jumpMeasure :=
    ((hcorr.const_mul t).ofReal.mul_const Complex.I)
  have hcast :
      (∫ x, ((t * affineDriftIntegrand a x : ℝ) : ℂ) ∂η.jumpMeasure) =
        ((∫ x, t * affineDriftIntegrand a x ∂η.jumpMeasure : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * affineDriftIntegrand a x ∂η.jumpMeasure) =
        t * ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure :=
    integral_const_mul _ _
  simp only [LevyTriplet.exponent, LevyTriplet.affine]
  rw [hmap]
  rw [show (fun x => levyExponentIntegrand t (a * x)) =
      (fun x => levyExponentIntegrand (a * t) x -
        (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) by
    funext x
    exact levyExponentIntegrand_mul a t x]
  rw [integral_sub hexp hcorrC]
  rw [integral_mul_const, hcast, hreal]
  simp only [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ ha.le]
  simp only [Complex.ofReal_mul]
  push_cast
  ring

end LevyTriplet

namespace CompoundPoisson

/-- The fixed-truncation triplet of a compound Poisson law whose jump law has no atom at zero.
The drift is derived from the truncation convention rather than guessed. -/
noncomputable def triplet (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) : LevyTriplet where
  gaussianVariance := 0
  drift := ∫ x, levyTruncation x ∂(r • (μ : Measure ℝ))
  jumpMeasure := r • (μ : Measure ℝ)
  isLevyMeasure_jumpMeasure := IsLevyMeasure.of_isFiniteMeasure (by
    simp [Measure.smul_apply, hzero])

theorem integrable_levyTruncation (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable levyTruncation ν := by
  apply (integrable_const (1 : ℝ)).mono measurable_levyTruncation.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    by_cases hx : |x| < 1
    · rw [levyTruncation_of_abs_lt_one hx, Real.norm_eq_abs]
      simpa using hx.le
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hx)]
      simp

/-- The compound Poisson triplet has exactly the Poisson characteristic exponent. -/
theorem exponent_triplet (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) (t : ℝ) :
    (triplet r μ hzero).exponent t =
      (r : ℂ) * (charFun (μ : Measure ℝ) t - 1) := by
  have htruncμ : Integrable levyTruncation (μ : Measure ℝ) :=
    integrable_levyTruncation _
  have hlevyμ : Integrable (levyExponentIntegrand t) (μ : Measure ℝ) :=
    (IsLevyMeasure.of_isFiniteMeasure hzero).integrable_levyExponentIntegrand t
  have hcorrμ : Integrable
      (fun x => (((t * levyTruncation x : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) :=
    ((htruncμ.const_mul t).ofReal.mul_const Complex.I)
  have hpoint (x : ℝ) :
      levyExponentIntegrand t x + (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) - 1 := by
    rw [Real.inner_apply]
    unfold levyExponentIntegrand
    have harg : (((t * x : ℝ) : ℂ) * Complex.I) =
        (((x * t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [harg]
    ring
  have hchar : Integrable
      (fun x => Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) := by
    apply ((hlevyμ.add hcorrμ).add (integrable_const 1)).congr
    exact ae_of_all _ fun x => by
      change levyExponentIntegrand t x +
          (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) + 1 = _
      rw [hpoint x]
      ring
  have hsum :
      (∫ x, levyExponentIntegrand t x ∂(μ : Measure ℝ)) +
          (∫ x, (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) =
        (∫ x, Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) - 1 := by
    rw [← integral_add hlevyμ hcorrμ]
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    rw [integral_sub hchar (integrable_const 1)]
    simp
  have hcast :
      (∫ x, ((t * levyTruncation x : ℝ) : ℂ) ∂(μ : Measure ℝ)) =
        ((∫ x, t * levyTruncation x ∂(μ : Measure ℝ) : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * levyTruncation x ∂(μ : Measure ℝ)) =
        t * ∫ x, levyTruncation x ∂(μ : Measure ℝ) :=
    integral_const_mul _ _
  simp only [LevyTriplet.exponent, triplet, NNReal.coe_zero, zero_div, zero_mul,
    Complex.ofReal_zero, neg_zero, zero_add]
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [charFun_apply]
  push_cast
  rw [← hsum]
  rw [integral_mul_const, hcast, hreal]
  push_cast
  simp only [smul_eq_mul]
  rw [Complex.ofReal_mul]
  ring

theorem triplet_represents_law (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) :
    (triplet r μ hzero).Represents (law r μ) := by
  intro t
  rw [charFun_law, exponent_triplet]

end CompoundPoisson

end ProbabilityTheory
