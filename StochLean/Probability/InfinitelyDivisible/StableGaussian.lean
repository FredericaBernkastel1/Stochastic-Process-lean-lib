/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.StableIndex

/-!
# Gaussian endpoint of stable-law classification

This module closes the index-two endpoint of Klenke's Theorem 16.22.  It proves from the
project-owned power-law Levy measure that the jump coefficients vanish at index two, and then
identifies the represented law with the project-owned wrapper around Mathlib's real Gaussian law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem stablePositiveLevyMeasure_not_isLevyMeasure_two
    {c : ℝ} (hc : 0 < c) :
    ¬ IsLevyMeasure (stablePositiveLevyMeasure 2 c) := by
  intro hlevy
  have hsmall :
      (∫⁻ x in Set.Ioo (0 : ℝ) 1, levyIntegrand x ∂stablePositiveLevyMeasure 2 c) < ∞ :=
    lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl)
      hlevy.lintegral_lt_top
  have hdensity : Measurable (fun x : ℝ =>
      if 0 < x then ENNReal.ofReal (c * x ^ (-(2 : ℝ) - 1)) else 0) := by
    have hrpow : Measurable (fun x : ℝ => x ^ (-3 : ℝ)) := by
      have hi : Measurable (fun x : ℝ => (x ^ (3 : ℕ))⁻¹) := by fun_prop
      convert hi using 1
      funext x
      rw [show (-3 : ℝ) = (-(3 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg_natCast]
      simp
    apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
    · apply ENNReal.measurable_ofReal.comp
      have hm := (measurable_const : Measurable (fun _ : ℝ => c)).mul hrpow
      rw [show (-(2 : ℝ) - 1) = (-3 : ℝ) by norm_num]
      have heq : ((fun _ : ℝ => c) * fun x : ℝ => x ^ (-3 : ℝ)) =
          (fun x : ℝ => c * x ^ (-3 : ℝ)) := by
        funext x
        rfl
      rw [← heq]
      exact hm
    · exact measurable_const
  rw [stablePositiveLevyMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul volume hdensity
      measurable_levyIntegrand measurableSet_Ioo] at hsmall
  have hcongr :
      (fun x : ℝ =>
          (if 0 < x then ENNReal.ofReal (c * x ^ (-(2 : ℝ) - 1)) else 0) *
            levyIntegrand x) =ᵐ[volume.restrict (Set.Ioo 0 1)]
        (fun x : ℝ => ENNReal.ofReal (c * x ^ (-1 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [if_pos hx.1, levyIntegrand_of_abs_lt_one]
    · rw [← ENNReal.ofReal_mul (mul_nonneg hc.le (Real.rpow_nonneg hx.1.le _))]
      congr 1
      rw [show -(2 : ℝ) - 1 = (-3 : ℝ) by norm_num]
      rw [← Real.rpow_natCast x 2]
      calc
        c * x ^ (-3 : ℝ) * x ^ (2 : ℝ) =
            c * (x ^ (-3 : ℝ) * x ^ (2 : ℝ)) := by ring
        _ = c * x ^ ((-3 : ℝ) + 2) := by rw [← Real.rpow_add hx.1]
        _ = c * x ^ (-1 : ℝ) := by norm_num
    · rw [abs_of_pos hx.1]
      exact hx.2
  change (∫⁻ x in Set.Ioo (0 : ℝ) 1,
      (if 0 < x then ENNReal.ofReal (c * x ^ (-(2 : ℝ) - 1)) else 0) *
        levyIntegrand x) < ∞ at hsmall
  rw [lintegral_congr_ae hcongr] at hsmall
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      (fun x : ℝ => c * x ^ (-1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg hc.le (Real.rpow_nonneg hx.1.le _)
  have hfinite : HasFiniteIntegral (fun x : ℝ => c * x ^ (-1 : ℝ))
      (volume.restrict (Set.Ioo 0 1)) :=
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hsmall
  have hintegrable : IntegrableOn (fun x : ℝ => c * x ^ (-1 : ℝ)) (Set.Ioo 0 1) :=
    ⟨(continuousOn_const.mul
        (continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable
          measurableSet_Ioo,
      hfinite⟩
  have hinv : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioo 0 1) := by
    have hscaled := hintegrable.const_mul c⁻¹
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioo
    intro x hx
    field_simp [hc.ne']
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (by norm_num : (0 : ℝ) < 1)).1 hinv
  norm_num at this

theorem stableLevyMeasure_coefficients_eq_zero_of_index_two
    {cMinus cPlus : ℝ} (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hlevy : IsLevyMeasure (stableLevyMeasure 2 cMinus cPlus)) :
    cMinus = 0 ∧ cPlus = 0 := by
  constructor
  · apply le_antisymm _ hcMinus
    by_contra hnot
    have hpos : 0 < cMinus := lt_of_not_ge hnot
    apply stablePositiveLevyMeasure_not_isLevyMeasure_two hpos
    have hle : (stablePositiveLevyMeasure 2 cMinus).map (fun x : ℝ => -x) ≤
        stableLevyMeasure 2 cMinus cPlus := by
      rw [stableLevyMeasure]
      exact Measure.le_add_left le_rfl
    have hmapped : IsLevyMeasure
        ((stablePositiveLevyMeasure 2 cMinus).map (fun x : ℝ => -x)) := by
      exact ⟨by
        rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0)]
        simp [stablePositiveLevyMeasure],
        lt_of_le_of_lt (lintegral_mono' hle le_rfl) hlevy.lintegral_lt_top⟩
    have hmapback := hmapped.map_mul (a := -1) (by norm_num)
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at hmapback
    have hident : ((fun x : ℝ => -1 * x) ∘ fun x : ℝ => -x) = id := by
      funext x
      simp
    rw [hident, Measure.map_id] at hmapback
    exact hmapback
  · apply le_antisymm _ hcPlus
    by_contra hnot
    have hpos : 0 < cPlus := lt_of_not_ge hnot
    apply stablePositiveLevyMeasure_not_isLevyMeasure_two hpos
    exact ⟨by
      simpa [stablePositiveLevyMeasure] using
        (stableLevyMeasure_singleton_zero 2 cMinus cPlus),
      lt_of_le_of_lt (lintegral_mono'
        (by rw [stableLevyMeasure]; exact Measure.le_add_right le_rfl) le_rfl)
        hlevy.lintegral_lt_top⟩

theorem LevyTriplet.jumpMeasure_eq_zero_of_stable_index_two
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex 2) (hη : η.Represents μ) :
    η.jumpMeasure = 0 := by
  let cMinus : ℝ := 2 * (η.jumpMeasure (Set.Iio (-1))).toReal
  let cPlus : ℝ := 2 * (η.jumpMeasure (Set.Ioi 1)).toReal
  have hcMinus : 0 ≤ cMinus := mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have hcPlus : 0 ≤ cPlus := mul_nonneg (by norm_num) ENNReal.toReal_nonneg
  have hjump : η.jumpMeasure = stableLevyMeasure 2 cMinus cPlus := by
    simpa [cMinus, cPlus] using
      LevyTriplet.jumpMeasure_eq_stableLevyMeasure hstable hη
  have hlevy : IsLevyMeasure (stableLevyMeasure 2 cMinus cPlus) := by
    rw [← hjump]
    exact η.isLevyMeasure_jumpMeasure
  obtain ⟨hcMinus0, hcPlus0⟩ :=
    stableLevyMeasure_coefficients_eq_zero_of_index_two hcMinus hcPlus hlevy
  rw [hjump, hcMinus0, hcPlus0, stableLevyMeasure]
  simp [stablePositiveLevyMeasure]

theorem LevyTriplet.eq_gaussianLaw_of_jumpMeasure_eq_zero
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ)
    (hjump : η.jumpMeasure = 0) :
    μ = LevyTriplet.gaussianLaw η.drift η.gaussianVariance := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  ext t
  rw [hη t, LevyTriplet.gaussian_represents_gaussianLaw η.drift η.gaussianVariance t]
  congr 1
  simp [LevyTriplet.exponent, LevyTriplet.gaussian, hjump]

theorem IsStableInBroadSenseWithIndex.eq_gaussianLaw_of_index_two
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSenseWithIndex 2) :
    ∃ η : LevyTriplet, η.Represents μ ∧
      μ = LevyTriplet.gaussianLaw η.drift η.gaussianVariance := by
  obtain ⟨η, hη⟩ := hstable.isStableInBroadSense.isInfinitelyDivisible.exists_representingTriplet
  exact ⟨η, hη, LevyTriplet.eq_gaussianLaw_of_jumpMeasure_eq_zero hη
    (LevyTriplet.jumpMeasure_eq_zero_of_stable_index_two hstable hη)⟩

theorem LevyTriplet.eq_pointMass_of_gaussianVariance_eq_zero_of_jumpMeasure_eq_zero
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ)
    (hgaussian : η.gaussianVariance = 0) (hjump : η.jumpMeasure = 0) :
    μ = ProbabilityMeasure.pointMass η.drift := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  ext t
  rw [hη t, LevyTriplet.represents_pointMass η.drift t]
  congr 1
  simp [LevyTriplet.exponent, LevyTriplet.pointMass, hgaussian, hjump]

/-- In the jump branch `α < 2`, the two power-law coefficients cannot both vanish. -/
theorem LevyTriplet.stable_coefficients_not_both_zero_of_index_lt_two
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (hα : α < 2) :
    let cMinus := α * (η.jumpMeasure (Set.Iio (-1))).toReal
    let cPlus := α * (η.jumpMeasure (Set.Ioi 1)).toReal
    cMinus ≠ 0 ∨ cPlus ≠ 0 := by
  let cMinus : ℝ := α * (η.jumpMeasure (Set.Iio (-1))).toReal
  let cPlus : ℝ := α * (η.jumpMeasure (Set.Ioi 1)).toReal
  have hjump : η.jumpMeasure = stableLevyMeasure α cMinus cPlus := by
    simpa [cMinus, cPlus] using
      LevyTriplet.jumpMeasure_eq_stableLevyMeasure hstable hη
  change cMinus ≠ 0 ∨ cPlus ≠ 0
  by_contra hzero
  push Not at hzero
  have hjump0 : η.jumpMeasure = 0 := by
    rw [hjump, hzero.1, hzero.2, stableLevyMeasure]
    simp [stablePositiveLevyMeasure]
  have hgaussian : η.gaussianVariance = 0 :=
    IsStableInBroadSenseWithIndex.gaussianVariance_eq_zero_of_index_lt_two
      hstable hα hη
  have hpoint :=
    LevyTriplet.eq_pointMass_of_gaussianVariance_eq_zero_of_jumpMeasure_eq_zero
      hη hgaussian hjump0
  exact hstable.2.1 η.drift hpoint

/-- Full `0 < α < 2` jump classification, including nontriviality of the two density
coefficients. -/
theorem IsStableInBroadSenseWithIndex.exists_jump_classification_of_index_lt_two
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hα : α < 2) :
    ∃ (η : LevyTriplet) (cMinus cPlus : ℝ),
      η.Represents μ ∧ 0 ≤ cMinus ∧ 0 ≤ cPlus ∧
        (cMinus ≠ 0 ∨ cPlus ≠ 0) ∧
        η.gaussianVariance = 0 ∧
        η.jumpMeasure = stableLevyMeasure α cMinus cPlus := by
  obtain ⟨η, hη⟩ :=
    hstable.isStableInBroadSense.isInfinitelyDivisible.exists_representingTriplet
  let cMinus : ℝ := α * (η.jumpMeasure (Set.Iio (-1))).toReal
  let cPlus : ℝ := α * (η.jumpMeasure (Set.Ioi 1)).toReal
  refine ⟨η, cMinus, cPlus, hη,
    mul_nonneg hstable.1.le ENNReal.toReal_nonneg,
    mul_nonneg hstable.1.le ENNReal.toReal_nonneg, ?_,
    IsStableInBroadSenseWithIndex.gaussianVariance_eq_zero_of_index_lt_two
      hstable hα hη, ?_⟩
  · exact LevyTriplet.stable_coefficients_not_both_zero_of_index_lt_two
      hstable hη hα
  · simpa [cMinus, cPlus] using
      LevyTriplet.jumpMeasure_eq_stableLevyMeasure hstable hη

end ProbabilityTheory
