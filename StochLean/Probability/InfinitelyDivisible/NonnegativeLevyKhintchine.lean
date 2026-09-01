/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevySemigroup
public import StochLean.Probability.InfinitelyDivisible.Nonnegative

/-!
# Nonnegative Levy--Khintchine parameters

The canonical parameters of a subordinator consist of a nonnegative deterministic part and a
positive jump measure integrating `min 1 x`.  This file embeds those parameters into StochLean's
fixed-truncation real Levy triplets and proves the constructive half of the nonnegative
Levy--Khintchine theorem, including nonnegative support of the resulting law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

structure NonnegativeLevyPair where
  deterministicPart : NNReal
  jumpMeasure : Measure ℝ
  supportedPositive : ∀ᵐ x ∂jumpMeasure, 0 < x
  integrable_min_one : Integrable (fun x : ℝ ↦ min 1 x) jumpMeasure

namespace NonnegativeLevyPair

theorem atom_zero (η : NonnegativeLevyPair) : η.jumpMeasure {0} = 0 := by
  have hs := η.supportedPositive
  rw [ae_iff] at hs
  apply measure_mono_null (s := ({0} : Set ℝ)) (t := {x | ¬ 0 < x})
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp
  · exact hs

theorem isLevyMeasure_jumpMeasure (η : NonnegativeLevyPair) :
    IsLevyMeasure η.jumpMeasure := by
  refine ⟨η.atom_zero, ?_⟩
  have hbound : ∀ᵐ x ∂η.jumpMeasure,
      levyIntegrand x ≤ ENNReal.ofReal (min 1 x) := by
    filter_upwards [η.supportedPositive] with x hx
    by_cases hsmall : x < 1
    · have habs : |x| < 1 := by simpa [abs_of_pos hx] using hsmall
      rw [levyIntegrand_of_abs_lt_one habs, min_eq_right hsmall.le]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    · have hone : 1 ≤ |x| := by simpa [abs_of_pos hx] using le_of_not_gt hsmall
      rw [levyIntegrand_of_one_le_abs hone, min_eq_left (le_of_not_gt hsmall)]
      norm_num
  have hlin : ∫⁻ x, ENNReal.ofReal (min 1 x) ∂η.jumpMeasure < ∞ := by
    have hi := (hasFiniteIntegral_iff_norm (fun x : ℝ ↦ min 1 x)).mp
      η.integrable_min_one.hasFiniteIntegral
    convert hi using 1
    apply lintegral_congr_ae
    filter_upwards [η.supportedPositive] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (lt_min zero_lt_one hx)]
  exact lt_of_le_of_lt (lintegral_mono_ae hbound) hlin

theorem integrable_levyTruncation (η : NonnegativeLevyPair) :
    Integrable levyTruncation η.jumpMeasure := by
  apply η.integrable_min_one.mono (measurable_levyTruncation.aestronglyMeasurable)
  filter_upwards [η.supportedPositive] with x hx
  by_cases hsmall : x < 1
  · have habs : |x| < 1 := by simpa [abs_of_pos hx] using hsmall
    rw [levyTruncation_of_abs_lt_one habs, Real.norm_eq_abs, abs_of_pos hx,
      min_eq_right hsmall.le, Real.norm_eq_abs, abs_of_pos hx]
  · have hone : 1 ≤ |x| := by simpa [abs_of_pos hx] using le_of_not_gt hsmall
    rw [levyTruncation_of_one_le_abs hone]
    simp

noncomputable def toLevyTriplet (η : NonnegativeLevyPair) : LevyTriplet where
  gaussianVariance := 0
  drift := η.deterministicPart + ∫ x, levyTruncation x ∂η.jumpMeasure
  jumpMeasure := η.jumpMeasure
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure

theorem toLevyTriplet_gaussianVariance (η : NonnegativeLevyPair) :
    η.toLevyTriplet.gaussianVariance = 0 := rfl

theorem toLevyTriplet_jumpMeasure (η : NonnegativeLevyPair) :
    η.toLevyTriplet.jumpMeasure = η.jumpMeasure := rfl

theorem toLevyTriplet_drift (η : NonnegativeLevyPair) :
    η.toLevyTriplet.drift = η.deterministicPart +
      ∫ x, levyTruncation x ∂η.jumpMeasure := rfl

/-- The embedding of nonnegative Lévy parameters into fixed-truncation real triplets is
injective.  In particular the deterministic part is not confused with the fixed-truncation
drift: it is recovered after subtracting the small-jump compensation integral. -/
theorem eq_of_toLevyTriplet_eq {η ξ : NonnegativeLevyPair}
    (h : η.toLevyTriplet = ξ.toLevyTriplet) : η = ξ := by
  have hjump : η.jumpMeasure = ξ.jumpMeasure :=
    congrArg LevyTriplet.jumpMeasure h
  have hdrift : η.toLevyTriplet.drift = ξ.toLevyTriplet.drift :=
    congrArg LevyTriplet.drift h
  have hdet : η.deterministicPart = ξ.deterministicPart := by
    apply NNReal.eq
    rw [toLevyTriplet_drift, toLevyTriplet_drift, hjump] at hdrift
    exact_mod_cast add_right_cancel hdrift
  cases η
  cases ξ
  simp_all

theorem toLevyTriplet_injective : Function.Injective toLevyTriplet :=
  fun _ _ => eq_of_toLevyTriplet_eq

noncomputable def uncompensatedJumpIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1

theorem uncompensatedJumpIntegrand_eq (t x : ℝ) :
    uncompensatedJumpIntegrand t x = levyExponentIntegrand t x +
      (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) := by
  simp only [uncompensatedJumpIntegrand, levyExponentIntegrand]
  push_cast
  ring

theorem integrable_uncompensatedJumpIntegrand (η : NonnegativeLevyPair) (t : ℝ) :
    Integrable (uncompensatedJumpIntegrand t) η.jumpMeasure := by
  rw [show uncompensatedJumpIntegrand t = fun x ↦ levyExponentIntegrand t x +
      (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) by
    funext x
    exact uncompensatedJumpIntegrand_eq t x]
  exact (η.toLevyTriplet.integrable_exponent_jump t).add
    ((η.integrable_levyTruncation.const_mul t).ofReal.mul_const Complex.I)

theorem exponent_toLevyTriplet (η : NonnegativeLevyPair) (t : ℝ) :
    η.toLevyTriplet.exponent t =
      (((η.deterministicPart : ℝ) * t : ℝ) : ℂ) * Complex.I +
        ∫ x, uncompensatedJumpIntegrand t x ∂η.jumpMeasure := by
  rw [show (∫ x, uncompensatedJumpIntegrand t x ∂η.jumpMeasure) =
      (∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) +
        ∫ x, (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) ∂η.jumpMeasure by
    rw [show uncompensatedJumpIntegrand t = fun x ↦ levyExponentIntegrand t x +
        (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) by
      funext x
      exact uncompensatedJumpIntegrand_eq t x]
    exact integral_add (η.toLevyTriplet.integrable_exponent_jump t)
      ((η.integrable_levyTruncation.const_mul t).ofReal.mul_const Complex.I)]
  rw [integral_mul_const]
  have hcast : (∫ x, ((t * levyTruncation x : ℝ) : ℂ) ∂η.jumpMeasure) =
      ((∫ x, t * levyTruncation x ∂η.jumpMeasure : ℝ) : ℂ) := integral_ofReal
  rw [hcast, integral_const_mul]
  simp only [toLevyTriplet, LevyTriplet.exponent, NNReal.coe_zero, zero_div, zero_mul,
    Complex.ofReal_zero, neg_zero, zero_add, NNReal.coe_add]
  push_cast
  ring

theorem gaussianLaw_zero_zero : LevyTriplet.gaussianLaw 0 0 =
    ProbabilityMeasure.pointMass 0 := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [LevyTriplet.coe_gaussianLaw, ProbabilityMeasure.coe_pointMass,
    gaussianReal_zero_var]

noncomputable def law (η : NonnegativeLevyPair) : ProbabilityMeasure ℝ :=
  η.toLevyTriplet.law

theorem represents_law (η : NonnegativeLevyPair) : η.toLevyTriplet.Represents η.law :=
  η.toLevyTriplet.represents_law

/-- Uniqueness of the nonnegative Lévy parameters for a represented law. -/
theorem eq_of_represents {η ξ : NonnegativeLevyPair} {μ : ProbabilityMeasure ℝ}
    (hη : η.toLevyTriplet.Represents μ) (hξ : ξ.toLevyTriplet.Represents μ) : η = ξ :=
  eq_of_toLevyTriplet_eq (hη.unique hξ)

theorem isInfinitelyDivisible_law (η : NonnegativeLevyPair) :
    η.law.IsInfinitelyDivisible :=
  η.toLevyTriplet.isInfinitelyDivisible_law

theorem nonnegative_restriction_integral_le (η : NonnegativeLevyPair) (n : ℕ) :
    (∫ x, levyTruncation x ∂η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)) ≤
      ∫ x, levyTruncation x ∂η.jumpMeasure := by
  apply integral_mono_measure Measure.restrict_le_self
  · filter_upwards [η.supportedPositive] with x hx
    simp only [levyTruncation]
    split <;> positivity
  · exact η.integrable_levyTruncation

theorem isNonnegativeLaw_finiteRestrictionLaw (η : NonnegativeLevyPair) (n : ℕ) :
    (η.toLevyTriplet.finiteRestrictionLaw n).IsNonnegativeLaw := by
  let ξ := η.toLevyTriplet.finiteRestriction n
  letI : IsFiniteMeasure ξ.jumpMeasure :=
    η.toLevyTriplet.finiteRestriction_jumpMeasure_finite n
  change (ξ.finiteJumpLaw).IsNonnegativeLaw
  change ProbabilityMeasure.IsNonnegativeLaw
    (ProbabilityMeasure.conv
      (ProbabilityMeasure.conv
        (ProbabilityMeasure.pointMass
          (ξ.drift - ∫ x, levyTruncation x ∂ξ.jumpMeasure))
        (LevyTriplet.gaussianLaw 0 ξ.gaussianVariance))
      (CompoundPoisson.ofFiniteMeasure
        (⟨ξ.jumpMeasure, inferInstance⟩ : FiniteMeasure ℝ)))
  apply ProbabilityMeasure.IsNonnegativeLaw.conv
  · apply ProbabilityMeasure.IsNonnegativeLaw.conv
    · rw [ProbabilityMeasure.isNonnegativeLaw_pointMass_iff]
      have hle := η.nonnegative_restriction_integral_le n
      have hd : 0 ≤ (η.deterministicPart : ℝ) := NNReal.coe_nonneg _
      dsimp [ξ, LevyTriplet.finiteRestriction, toLevyTriplet]
      push_cast
      linarith
    · rw [show ξ.gaussianVariance = 0 by rfl, gaussianLaw_zero_zero]
      exact (ProbabilityMeasure.isNonnegativeLaw_pointMass_iff 0).2 le_rfl
  · apply CompoundPoisson.isNonnegativeLaw_ofFiniteMeasure
    exact ae_restrict_of_ae (η.supportedPositive.mono fun x hx ↦ hx.le)

theorem isNonnegativeLaw_law (η : NonnegativeLevyPair) : η.law.IsNonnegativeLaw := by
  apply ProbabilityMeasure.IsNonnegativeLaw.tendsto
    (μn := fun n ↦ η.toLevyTriplet.finiteRestrictionLaw n)
  · apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    rw [η.represents_law t]
    exact η.toLevyTriplet.tendsto_charFun_finiteRestrictionLaw t
  · exact η.isNonnegativeLaw_finiteRestrictionLaw

end NonnegativeLevyPair
end ProbabilityTheory
