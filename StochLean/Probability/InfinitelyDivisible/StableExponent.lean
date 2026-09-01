/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import StochLean.Probability.InfinitelyDivisible.StableGaussian

/-!
# Source-safe closed forms for real stable exponents

This module records the Gamma/trigonometric expression in Klenke's Remark 16.23 without turning
the printed shorthand into a false theorem.  A Levy measure does not determine the linear
imaginary part of a Levy exponent: translating a law leaves its jump measure unchanged and adds
`i d t` to the exponent.  Consequently the printed expression is the exponent of a chosen
location-normalized representative, while every translate has the explicitly recorded linear
correction.

The exceptional index-one formula uses `signedLogAbs`, whose value at zero is defined by a genuine
piecewise branch.  In particular, none of the zero-frequency results below relies on the
totalized value of `log 0` or on simplifying an informal product `0 * log 0`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

/-- The continuous product `|t| * sign(t) * log |t|`, with its value at zero inherited from the
source-safe `signedLogAbs` helper. -/
noncomputable def stableSignedLogTerm (t : ℝ) : ℝ :=
  |t| * signedLogAbs t

@[simp]
theorem stableSignedLogTerm_zero : stableSignedLogTerm 0 = 0 := by
  simp [stableSignedLogTerm]

/-- Algebraic identification away from the piecewise definition.  The proof first opens the
explicit zero branch and only then uses the ordinary real-log identity. -/
theorem stableSignedLogTerm_eq_mul_log (t : ℝ) :
    stableSignedLogTerm t = t * Real.log t := by
  by_cases ht : t = 0
  · subst t
    simp [stableSignedLogTerm]
  · rw [stableSignedLogTerm, signedLogAbs_of_ne ht]
    calc
      |t| * ((SignType.sign t : ℝ) * Real.log |t|) =
          (|t| * (SignType.sign t : ℝ)) * Real.log |t| := by ring
      _ = t * Real.log |t| := by rw [abs_mul_sign]
      _ = t * Real.log t := by rw [Real.log_abs]

/-- The index-one logarithmic term is continuous at zero (and everywhere). -/
theorem continuous_stableSignedLogTerm : Continuous stableSignedLogTerm := by
  rw [show stableSignedLogTerm = fun t : ℝ => t * Real.log t by
    funext t
    exact stableSignedLogTerm_eq_mul_log t]
  exact Real.continuous_mul_log

/-- The `alpha != 1` Gamma/trigonometric expression in Remark 16.23.  The coefficient order is
negative half-line first and positive half-line second, matching `stableLevyMeasure`. -/
noncomputable def stableExponentAwayOne
    (alpha cMinus cPlus t : ℝ) : ℂ :=
  if t = 0 then 0 else
    Complex.ofReal (|t| ^ alpha * Real.Gamma (-alpha) *
      ((cPlus + cMinus) * Real.cos (Real.pi * alpha / 2))) -
    Complex.ofReal (|t| ^ alpha * Real.Gamma (-alpha) *
      ((SignType.sign t : ℝ) * (cPlus - cMinus) *
        Real.sin (Real.pi * alpha / 2))) * Complex.I

/-- The ordinary Gamma/trigonometric display away from zero frequency. -/
theorem stableExponentAwayOne_of_ne
    (alpha cMinus cPlus : ℝ) {t : ℝ} (ht : t ≠ 0) :
    stableExponentAwayOne alpha cMinus cPlus t =
      Complex.ofReal (|t| ^ alpha * Real.Gamma (-alpha) *
        ((cPlus + cMinus) * Real.cos (Real.pi * alpha / 2))) -
      Complex.ofReal (|t| ^ alpha * Real.Gamma (-alpha) *
        ((SignType.sign t : ℝ) * (cPlus - cMinus) *
          Real.sin (Real.pi * alpha / 2))) * Complex.I := by
  simp [stableExponentAwayOne, ht]

/-- The exceptional `alpha = 1` expression.  `stableSignedLogTerm` makes the zero-frequency
semantics explicit. -/
noncomputable def stableExponentAtOne (cMinus cPlus t : ℝ) : ℂ :=
  -(Complex.ofReal (|t| * (cPlus + cMinus) * Real.pi / 2) +
      Complex.ofReal ((cPlus - cMinus) * stableSignedLogTerm t) * Complex.I)

/-- Source-facing stable exponent expression, separated into the mathematically correct
`alpha = 1` and `alpha != 1` branches. -/
noncomputable def stableExponentClosedForm
    (alpha cMinus cPlus t : ℝ) : ℂ :=
  if alpha = 1 then stableExponentAtOne cMinus cPlus t
  else stableExponentAwayOne alpha cMinus cPlus t

/-- Add the location parameter omitted by the shorthand statement of Remark 16.23. -/
noncomputable def stableExponentWithLocation
    (alpha cMinus cPlus location t : ℝ) : ℂ :=
  stableExponentClosedForm alpha cMinus cPlus t +
    Complex.ofReal (location * t) * Complex.I

@[simp]
theorem stableExponentAwayOne_zero (alpha cMinus cPlus : ℝ) :
    stableExponentAwayOne alpha cMinus cPlus 0 = 0 := by
  simp [stableExponentAwayOne]

@[simp]
theorem stableExponentAtOne_zero (cMinus cPlus : ℝ) :
    stableExponentAtOne cMinus cPlus 0 = 0 := by
  simp [stableExponentAtOne]

@[simp]
theorem stableExponentClosedForm_zero (alpha cMinus cPlus : ℝ) :
    stableExponentClosedForm alpha cMinus cPlus 0 = 0 := by
  simp [stableExponentClosedForm]

@[simp]
theorem stableExponentWithLocation_zero
    (alpha cMinus cPlus location : ℝ) :
    stableExponentWithLocation alpha cMinus cPlus location 0 = 0 := by
  simp [stableExponentWithLocation]

theorem stableExponentClosedForm_of_ne_one
    {alpha : ℝ} (halpha : alpha ≠ 1) (cMinus cPlus t : ℝ) :
    stableExponentClosedForm alpha cMinus cPlus t =
      stableExponentAwayOne alpha cMinus cPlus t := by
  simp [stableExponentClosedForm, halpha]

@[simp]
theorem stableExponentClosedForm_one (cMinus cPlus t : ℝ) :
    stableExponentClosedForm 1 cMinus cPlus t =
      stableExponentAtOne cMinus cPlus t := by
  simp [stableExponentClosedForm]

/-- The index-one branch is continuous, including at `t = 0`. -/
theorem continuous_stableExponentAtOne (cMinus cPlus : ℝ) :
    Continuous (stableExponentAtOne cMinus cPlus) := by
  unfold stableExponentAtOne
  have hreal : Continuous (fun t : ℝ => |t| * (cPlus + cMinus) * Real.pi / 2) := by
    fun_prop
  have himag : Continuous (fun t : ℝ =>
      (cPlus - cMinus) * stableSignedLogTerm t) :=
    continuous_const.mul continuous_stableSignedLogTerm
  exact ((Complex.continuous_ofReal.comp hreal).add
    ((Complex.continuous_ofReal.comp himag).mul continuous_const)).neg

/-- The located index-one branch remains continuous. -/
theorem continuous_stableExponentWithLocation_one
    (cMinus cPlus location : ℝ) :
    Continuous (stableExponentWithLocation 1 cMinus cPlus location) := by
  unfold stableExponentWithLocation
  simp only [stableExponentClosedForm_one]
  exact (continuous_stableExponentAtOne cMinus cPlus).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const)

namespace LevyTriplet

/-- Translation leaves the Levy measure unchanged. -/
@[simp]
theorem affine_one_jumpMeasure (eta : LevyTriplet) (d : ℝ) :
    (eta.affine 1 d zero_lt_one).jumpMeasure = eta.jumpMeasure := by
  rw [affine_jumpMeasure]
  simpa using Measure.map_id eta.jumpMeasure

/-- Translation adds exactly the missing location term to the characteristic exponent. -/
theorem exponent_affine_one (eta : LevyTriplet) (d t : ℝ) :
    (eta.affine 1 d zero_lt_one).exponent t =
      eta.exponent t + Complex.ofReal (d * t) * Complex.I := by
  simpa using eta.exponent_affine 1 d zero_lt_one t

/-- A nonzero translation really changes the exponent, despite preserving the jump measure.  This
is the formal obstruction to reading Remark 16.23 as a theorem determined by the Levy measure
alone. -/
theorem exponent_affine_one_ne (eta : LevyTriplet) {d : ℝ} (hd : d ≠ 0) :
    (eta.affine 1 d zero_lt_one).exponent ≠ eta.exponent := by
  intro h
  have h1 := congrFun h 1
  rw [exponent_affine_one] at h1
  have h1' : eta.exponent 1 + Complex.ofReal d * Complex.I = eta.exponent 1 := by
    simpa using h1
  have hzero : Complex.ofReal d * Complex.I = 0 := by
    calc
      Complex.ofReal d * Complex.I =
          (eta.exponent 1 + Complex.ofReal d * Complex.I) - eta.exponent 1 := by ring
      _ = 0 := by rw [h1']; ring
  have hdC : Complex.ofReal d = 0 :=
    (mul_eq_zero.mp hzero).resolve_right Complex.I_ne_zero
  exact hd (Complex.ofReal_eq_zero.mp hdC)

end LevyTriplet

/-- Moving the chosen location by `d` adds `i d t` to the source-facing expression. -/
theorem stableExponentWithLocation_add
    (alpha cMinus cPlus location d t : ℝ) :
    stableExponentWithLocation alpha cMinus cPlus (location + d) t =
      stableExponentWithLocation alpha cMinus cPlus location t +
        Complex.ofReal (d * t) * Complex.I := by
  simp only [stableExponentWithLocation]
  push_cast
  ring

end ProbabilityTheory
