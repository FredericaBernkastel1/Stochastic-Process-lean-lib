/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.CDF
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Empirical probability measures

The sample-size parameter is `n`, but the sample contains the first `n + 1` observations. Thus the
empty-sample case is absent from the type-level API, matching `empiricalCDF`.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace E]

/-- The empirical probability measure of the first `n + 1` observations. -/
noncomputable def empiricalProbabilityMeasure (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Measure E :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), Measure.dirac (X k ω)

theorem empiricalProbabilityMeasure_apply (X : ℕ → Ω → E) (n : ℕ) (ω : Ω)
    {s : Set E} (hs : MeasurableSet s) :
    empiricalProbabilityMeasure X n ω s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), s.indicator 1 (X k ω) := by
  simp [empiricalProbabilityMeasure, Measure.smul_apply, hs, Measure.dirac_apply']

instance empiricalProbabilityMeasure.instIsProbabilityMeasure
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (empiricalProbabilityMeasure X n ω) where
  measure_univ := by
    rw [empiricalProbabilityMeasure_apply X n ω MeasurableSet.univ]
    simp only [Nat.cast_add, Nat.cast_one, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- Integrating a real test function against the empirical measure is the finite sample average.

No measurability or ambient integrability hypothesis on `f` is needed: the measure has finite
support and measurable singletons make every point evaluation at a Dirac mass integrable. -/
theorem integral_empiricalProbabilityMeasure [MeasurableSingletonClass E]
    (X : ℕ → Ω → E) (f : E → ℝ) (n : ℕ) (ω : Ω) :
    ∫ x, f x ∂empiricalProbabilityMeasure X n ω =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), f (X k ω) := by
  rw [empiricalProbabilityMeasure, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul]
  · intro k hk
    exact integrable_dirac (by simp)

/-- Evaluating the empirical measure of a real sample on `(-∞, t]` recovers its empirical CDF. -/
theorem empiricalProbabilityMeasure_Iic (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    (empiricalProbabilityMeasure X n ω (Set.Iic t)).toReal =
      empiricalCDFSequence X n ω t := by
  rw [empiricalProbabilityMeasure_apply X n ω measurableSet_Iic]
  rw [empiricalCDFSequence, empiricalCDF_eq_average_indicator]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_sum (by
    intro k hk
    simp only [Set.indicator_apply]
    split <;> simp)]
  simp only [ENNReal.toReal_natCast]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
  split <;> simp

end ProbabilityTheory
