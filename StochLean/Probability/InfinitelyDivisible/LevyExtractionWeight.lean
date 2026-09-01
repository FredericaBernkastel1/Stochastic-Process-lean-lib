/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The finite extraction weight for the converse Lévy--Khintchine theorem

The weight `1 - sinc x` is strictly positive away from zero and is globally comparable with
`min (1, x²)`.  Consequently, weighting a Lévy measure produces a finite measure, and dividing a
finite measure with no mass at zero by this weight produces a Lévy measure.  These estimates are
the analytic core of the finite-measure extraction argument.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology ProbabilityTheory Interval

namespace ProbabilityTheory
namespace LevyTriplet

/-- Klenke's finite extraction weight `1 - sinc x`, bundled as a nonnegative real. -/
noncomputable def extractionWeight (x : ℝ) : ℝ≥0 :=
  ⟨1 - Real.sinc x, sub_nonneg.mpr (Real.sinc_le_one x)⟩

@[simp, norm_cast]
theorem extractionWeight_coe (x : ℝ) :
    (extractionWeight x : ℝ) = 1 - Real.sinc x := rfl

@[simp]
theorem extractionWeight_zero : extractionWeight 0 = 0 := by
  apply NNReal.coe_injective
  simp [extractionWeight_coe]

theorem continuous_extractionWeight : Continuous extractionWeight := by
  exact (continuous_const.sub Real.continuous_sinc).subtype_mk _

theorem measurable_extractionWeight : Measurable extractionWeight :=
  continuous_extractionWeight.measurable

/-- Near zero, the extraction weight controls the quadratic Lévy integrand. -/
theorem extractionWeight_sq_le (x : ℝ) (hx : |x| < 1) :
    x ^ 2 ≤ 2 * Real.pi ^ 2 * (extractionWeight x : ℝ) := by
  wlog hxnonneg : 0 ≤ x generalizing x
  · have hneg : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hxnonneg)
    have habs : |-x| < 1 := by simpa using hx
    simpa [Real.sinc_neg] using this (-x) habs hneg
  rcases hxnonneg.eq_or_lt with rfl | hxpos
  · simp
  · have hxone : x < 1 := (le_abs_self x).trans_lt hx
    have hxpi : x / 2 < Real.pi / 2 := by
      have : (1 : ℝ) < Real.pi := lt_of_lt_of_le (by norm_num) Real.two_le_pi
      linarith
    have hhalfpos : 0 < x / 2 := by positivity
    have hhalfne : x / 2 ≠ 0 := ne_of_gt hhalfpos
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hsinpos : 0 < Real.sin (x / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hhalfpos (hxpi.trans (half_lt_self Real.pi_pos))
    have hsincnonneg : 0 ≤ Real.sinc (x / 2) := by
      rw [Real.sinc_of_ne_zero hhalfne]
      positivity
    have hcosnonneg : 0 ≤ Real.cos (x / 2) := by
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxpi⟩).le
    have hfactor : Real.sinc x = Real.sinc (x / 2) * Real.cos (x / 2) := by
      rw [Real.sinc_of_ne_zero hxne, Real.sinc_of_ne_zero hhalfne]
      rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]
      field_simp
    have hsinc_le_cos : Real.sinc x ≤ Real.cos (x / 2) := by
      rw [hfactor]
      exact mul_le_of_le_one_left hcosnonneg (Real.sinc_le_one (x / 2))
    have hhalfpi : |x / 2| ≤ Real.pi := by
      rw [abs_of_pos hhalfpos]
      linarith [Real.pi_pos]
    have hcosbound := Real.cos_le_one_sub_mul_cos_sq hhalfpi
    have hden : 0 < 2 * Real.pi ^ 2 := by positivity
    have hfrac : x ^ 2 / (2 * Real.pi ^ 2) ≤ 1 - Real.cos (x / 2) := by
      calc
        x ^ 2 / (2 * Real.pi ^ 2) = 2 / Real.pi ^ 2 * (x / 2) ^ 2 := by
          field_simp [Real.pi_ne_zero]
        _ ≤ 1 - Real.cos (x / 2) := by linarith
    have hscaled : x ^ 2 ≤ 2 * Real.pi ^ 2 * (1 - Real.cos (x / 2)) := by
      have := (div_le_iff₀ hden).mp hfrac
      simpa [mul_comm] using this
    rw [extractionWeight_coe]
    exact hscaled.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hsinc_le_cos 1)
      hden.le)

theorem extractionWeight_pos {x : ℝ} (hx : x ≠ 0) : 0 < extractionWeight x := by
  rw [← NNReal.coe_pos, extractionWeight_coe, sub_pos]
  have habs : |Real.sinc x| < 1 := by
    rw [Real.sinc_of_ne_zero hx, abs_div]
    exact (div_lt_one (abs_pos.mpr hx)).mpr (Real.abs_sin_lt_abs hx)
  exact (le_abs_self _).trans_lt habs

theorem extractionWeight_eq_zero_iff {x : ℝ} : extractionWeight x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (extractionWeight_pos hx).ne' h
  · rintro rfl
    exact extractionWeight_zero

theorem extractionWeight_le_two (x : ℝ) : (extractionWeight x : ℝ) ≤ 2 := by
  rw [extractionWeight_coe]
  linarith [Real.neg_one_le_sinc x]

/-- The extraction weight is bounded above by twice the canonical Lévy integrand. -/
theorem extractionWeight_le_two_mul_levyIntegrand (x : ℝ) :
    (extractionWeight x : ℝ) ≤ 2 * (levyIntegrand x).toReal := by
  by_cases hxsmall : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hxsmall]
    by_cases hx0 : x = 0
    · subst x
      rw [extractionWeight_coe]
      norm_num
    · have hweightnonneg : 0 ≤ (extractionWeight x : ℝ) := NNReal.coe_nonneg _
      have hweightabs : |(extractionWeight x : ℝ)| = (extractionWeight x : ℝ) :=
        abs_of_nonneg hweightnonneg
      have hidentity : |(extractionWeight x : ℝ)| = |x - Real.sin x| / |x| := by
        rw [extractionWeight_coe, Real.sinc_of_ne_zero hx0]
        rw [← abs_div]
        congr 1
        field_simp
      have hbound := Real.abs_sub_sin_le x
      have hxabspos : 0 < |x| := abs_pos.mpr hx0
      rw [← hweightabs, hidentity]
      calc
        |x - Real.sin x| / |x| ≤ (|x| ^ 3 / 6) / |x| :=
          div_le_div_of_nonneg_right hbound hxabspos.le
        _ = x ^ 2 / 6 := by
          field_simp [hxabspos.ne']
          rw [sq_abs]
        _ ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
  · rw [levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hxsmall)]
    simpa using extractionWeight_le_two x

/-- The canonical Lévy integrand is bounded by a fixed multiple of the extraction weight. -/
theorem levyIntegrand_toReal_le_extractionWeight (x : ℝ) :
    (levyIntegrand x).toReal ≤ 2 * Real.pi ^ 2 * (extractionWeight x : ℝ) := by
  by_cases hxsmall : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hxsmall]
    exact extractionWeight_sq_le x hxsmall
  · rw [levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hxsmall)]
    let y := |x|
    have hyone : 1 ≤ y := le_of_not_gt hxsmall
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hyone
    have hyne : y ≠ 0 := ne_of_gt hypos
    have hweight : extractionWeight x = extractionWeight y := by
      apply NNReal.coe_injective
      simp only [extractionWeight_coe, y]
      rcases le_total 0 x with hxnonneg | hxnonpos
      · rw [abs_of_nonneg hxnonneg]
      · rw [abs_of_nonpos hxnonpos, Real.sinc_neg]
    rw [hweight]
    by_cases hytwo : 2 ≤ y
    · have hsinc : Real.sinc y ≤ (1 / 2 : ℝ) := by
        calc
          Real.sinc y ≤ |y|⁻¹ := Real.sinc_le_inv_abs hyne
          _ = y⁻¹ := by rw [abs_of_pos hypos]
          _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hypos (by norm_num)).mpr hytwo
          _ = 1 / 2 := by norm_num
      rw [extractionWeight_coe]
      have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
      nlinarith
    · have hylt : y < 2 := lt_of_not_ge hytwo
      have hyhalfpos : 0 < y / 2 := by positivity
      have hyhalfne : y / 2 ≠ 0 := ne_of_gt hyhalfpos
      have hyhalfpi : y / 2 < Real.pi / 2 := by
        linarith [Real.two_le_pi]
      have hsincnonneg : 0 ≤ Real.sinc (y / 2) := by
        rw [Real.sinc_of_ne_zero hyhalfne]
        have hsin : 0 < Real.sin (y / 2) :=
          Real.sin_pos_of_pos_of_lt_pi hyhalfpos
            (hyhalfpi.trans (half_lt_self Real.pi_pos))
        positivity
      have hcosnonneg : 0 ≤ Real.cos (y / 2) :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hyhalfpi⟩).le
      have hfactor : Real.sinc y = Real.sinc (y / 2) * Real.cos (y / 2) := by
        rw [Real.sinc_of_ne_zero hyne, Real.sinc_of_ne_zero hyhalfne]
        rw [show y = 2 * (y / 2) by ring, Real.sin_two_mul]
        field_simp
      have hsinc_le_cos : Real.sinc y ≤ Real.cos (y / 2) := by
        rw [hfactor]
        exact mul_le_of_le_one_left hcosnonneg (Real.sinc_le_one (y / 2))
      have hhalfpiabs : |y / 2| ≤ Real.pi := by
        rw [abs_of_pos hyhalfpos]
        linarith [Real.pi_pos]
      have hcosbound := Real.cos_le_one_sub_mul_cos_sq hhalfpiabs
      have hyoneSq : (1 : ℝ) ≤ y ^ 2 := by nlinarith
      rw [extractionWeight_coe]
      have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      have hfrac : 1 / (2 * Real.pi ^ 2) ≤ 1 - Real.sinc y := by
        have hmain : 1 / (2 * Real.pi ^ 2) ≤ 2 / Real.pi ^ 2 * (y / 2) ^ 2 := by
          rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
          field_simp [Real.pi_ne_zero]
          nlinarith
        linarith
      have := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)).mp hfrac
      simpa [mul_comm] using this

end LevyTriplet
end ProbabilityTheory
