/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyMeasure

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

/-- A real Lévy triplet under the fixed strict truncation convention. -/
structure LevyTriplet where
  gaussianVariance : ℝ≥0
  drift : ℝ
  jumpMeasure : Measure ℝ
  isLevyMeasure_jumpMeasure : IsLevyMeasure jumpMeasure

namespace LevyTriplet

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

end LevyTriplet

end ProbabilityTheory
