/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyTripletExtraction
public import Mathlib.Analysis.Calculus.LHopital

/-!
# Sine-truncation extraction for the converse Lévy--Khintchine theorem

This module constructs the bounded continuous quotient associated with the admissible truncation
`sin x`.  Its value at zero is the exact Gaussian extraction coefficient `-3t²`.  The construction
avoids cutoff discontinuities and is the analytic bridge from weak convergence of the finite
extraction measures to convergence of Lévy exponents.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory
namespace LevyTriplet

private noncomputable def ratioReNum (t x : ℝ) : ℝ := x * (Real.cos (t * x) - 1)
private noncomputable def ratioReNum1 (t x : ℝ) : ℝ :=
  Real.cos (t * x) - 1 - t * x * Real.sin (t * x)
private noncomputable def ratioReNum2 (t x : ℝ) : ℝ :=
  -2 * t * Real.sin (t * x) - t ^ 2 * x * Real.cos (t * x)
private noncomputable def ratioReNum3 (t x : ℝ) : ℝ :=
  -3 * t ^ 2 * Real.cos (t * x) + t ^ 3 * x * Real.sin (t * x)

private noncomputable def ratioImNum (t x : ℝ) : ℝ :=
  x * (Real.sin (t * x) - t * Real.sin x)
private noncomputable def ratioImNum1 (t x : ℝ) : ℝ :=
  Real.sin (t * x) - t * Real.sin x +
    x * (t * Real.cos (t * x) - t * Real.cos x)
private noncomputable def ratioImNum2 (t x : ℝ) : ℝ :=
  2 * t * Real.cos (t * x) - 2 * t * Real.cos x +
    x * (-t ^ 2 * Real.sin (t * x) + t * Real.sin x)
private noncomputable def ratioImNum3 (t x : ℝ) : ℝ :=
  -3 * t ^ 2 * Real.sin (t * x) + 3 * t * Real.sin x +
    x * (-t ^ 3 * Real.cos (t * x) + t * Real.cos x)

private noncomputable def ratioDen (x : ℝ) : ℝ := x - Real.sin x
private noncomputable def ratioDen1 (x : ℝ) : ℝ := 1 - Real.cos x
private noncomputable def ratioDen2 (x : ℝ) : ℝ := Real.sin x
private noncomputable def ratioDen3 (x : ℝ) : ℝ := Real.cos x

private theorem hasDerivAt_ratioReNum (t x : ℝ) :
    HasDerivAt (ratioReNum t) (ratioReNum1 t x) x := by
  unfold ratioReNum ratioReNum1
  convert (hasDerivAt_id x).mul
    (((Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t)).sub_const 1) using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq]; ring)

private theorem hasDerivAt_ratioReNum1 (t x : ℝ) :
    HasDerivAt (ratioReNum1 t) (ratioReNum2 t x) x := by
  unfold ratioReNum1 ratioReNum2
  convert (((Real.hasDerivAt_cos (t * x)).comp x
      ((hasDerivAt_id x).const_mul t)).sub_const 1).sub
    (((hasDerivAt_const x t).mul (hasDerivAt_id x)).mul
      ((Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t))) using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq]; ring)

private theorem hasDerivAt_ratioReNum2 (t x : ℝ) :
    HasDerivAt (ratioReNum2 t) (ratioReNum3 t x) x := by
  unfold ratioReNum2 ratioReNum3
  have h₁ := (hasDerivAt_const x (-2 * t)).mul
    ((Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t))
  have h₂ := ((hasDerivAt_const x (t ^ 2)).mul (hasDerivAt_id x)).mul
    ((Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t))
  convert h₁.sub h₂ using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq]; ring)

private theorem hasDerivAt_ratioImNum (t x : ℝ) :
    HasDerivAt (ratioImNum t) (ratioImNum1 t x) x := by
  unfold ratioImNum ratioImNum1
  convert (hasDerivAt_id x).mul
    (((Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t)).sub
      ((hasDerivAt_const x t).mul (Real.hasDerivAt_sin x))) using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq]; ring)

private theorem hasDerivAt_ratioImNum1 (t x : ℝ) :
    HasDerivAt (ratioImNum1 t) (ratioImNum2 t x) x := by
  unfold ratioImNum1 ratioImNum2
  convert ((((Real.hasDerivAt_sin (t * x)).comp x
      ((hasDerivAt_id x).const_mul t)).sub
        ((hasDerivAt_const x t).mul (Real.hasDerivAt_sin x))).add
    ((hasDerivAt_id x).mul
      (((hasDerivAt_const x t).mul
          ((Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t))).sub
        ((hasDerivAt_const x t).mul (Real.hasDerivAt_cos x))))) using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]; ring)

private theorem hasDerivAt_ratioImNum2 (t x : ℝ) :
    HasDerivAt (ratioImNum2 t) (ratioImNum3 t x) x := by
  unfold ratioImNum2 ratioImNum3
  convert ((((hasDerivAt_const x (2 * t)).mul
      ((Real.hasDerivAt_cos (t * x)).comp x ((hasDerivAt_id x).const_mul t))).sub
        ((hasDerivAt_const x (2 * t)).mul (Real.hasDerivAt_cos x))).add
    ((hasDerivAt_id x).mul
      (((hasDerivAt_const x (-t ^ 2)).mul
          ((Real.hasDerivAt_sin (t * x)).comp x ((hasDerivAt_id x).const_mul t))).add
        ((hasDerivAt_const x t).mul (Real.hasDerivAt_sin x))))) using 1
  all_goals first | rfl |
    (simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]; ring)

private theorem hasDerivAt_ratioDen (x : ℝ) : HasDerivAt ratioDen (ratioDen1 x) x := by
  unfold ratioDen ratioDen1
  convert (hasDerivAt_id x).sub (Real.hasDerivAt_sin x) using 1
  all_goals first | rfl | (try simp only [Pi.sub_apply, id_eq]; ring)

private theorem hasDerivAt_ratioDen1 (x : ℝ) : HasDerivAt ratioDen1 (ratioDen2 x) x := by
  unfold ratioDen1 ratioDen2
  convert (hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x) using 1
  all_goals first | rfl | simp only [Pi.sub_apply, zero_sub, neg_neg]

private theorem hasDerivAt_ratioDen2 (x : ℝ) : HasDerivAt ratioDen2 (ratioDen3 x) x := by
  exact Real.hasDerivAt_sin x

private theorem eventually_ratioDen1_ne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ratioDen1 x ≠ 0 := by
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ Set.Ioo (-Real.pi) Real.pi :=
    Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear,
    self_mem_nhdsWithin] with x hx hx0
  intro h
  have hcos : Real.cos x = 1 := by simpa [ratioDen1] using (sub_eq_zero.mp h).symm
  have hsin : Real.sin x = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hcos)
  have : x = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hx.1 hx.2).mp hsin
  exact hx0 (by simpa using this)

private theorem eventually_ratioDen2_ne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ratioDen2 x ≠ 0 := by
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ Set.Ioo (-Real.pi) Real.pi :=
    Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear,
    self_mem_nhdsWithin] with x hx hx0
  have hne : x ≠ 0 := by simpa using hx0
  simpa [ratioDen2, Real.sin_eq_zero_iff_of_lt_of_lt hx.1 hx.2] using hne

private theorem eventually_ratioDen3_ne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ratioDen3 x ≠ 0 := by
  have h : ∀ᶠ x in 𝓝 (0 : ℝ), Real.cos x ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne (by norm_num)
  exact eventually_nhdsWithin_of_eventually_nhds (by simpa [ratioDen3] using h)

private theorem tendsto_ratio_re (t : ℝ) :
    Tendsto (fun x => ratioReNum t x / ratioDen x) (𝓝[≠] 0) (𝓝 (-3 * t ^ 2)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioReNum t x
  · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen x
  · exact eventually_ratioDen1_ne
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [ratioReNum] using (hasDerivAt_ratioReNum t 0).continuousAt.tendsto)
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [ratioDen] using (hasDerivAt_ratioDen 0).continuousAt.tendsto)
  · apply HasDerivAt.lhopital_zero_nhdsNE
    · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioReNum1 t x
    · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen1 x
    · exact eventually_ratioDen2_ne
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa [ratioReNum1] using (hasDerivAt_ratioReNum1 t 0).continuousAt.tendsto)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa [ratioDen1] using (hasDerivAt_ratioDen1 0).continuousAt.tendsto)
    · apply HasDerivAt.lhopital_zero_nhdsNE
      · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioReNum2 t x
      · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen2 x
      · exact eventually_ratioDen3_ne
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa [ratioReNum2] using (hasDerivAt_ratioReNum2 t 0).continuousAt.tendsto)
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa [ratioDen2] using (hasDerivAt_ratioDen2 0).continuousAt.tendsto)
      · have hc : ContinuousAt (fun x : ℝ => ratioReNum3 t x / ratioDen3 x) 0 := by
          apply ContinuousAt.div₀
          · unfold ratioReNum3
            fun_prop
          · unfold ratioDen3
            fun_prop
          · simp [ratioDen3]
        simpa [ratioReNum3, ratioDen3] using
          tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

private theorem tendsto_ratio_im (t : ℝ) :
    Tendsto (fun x => ratioImNum t x / ratioDen x) (𝓝[≠] 0) (𝓝 0) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioImNum t x
  · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen x
  · exact eventually_ratioDen1_ne
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [ratioImNum] using (hasDerivAt_ratioImNum t 0).continuousAt.tendsto)
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [ratioDen] using (hasDerivAt_ratioDen 0).continuousAt.tendsto)
  · apply HasDerivAt.lhopital_zero_nhdsNE
    · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioImNum1 t x
    · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen1 x
    · exact eventually_ratioDen2_ne
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa [ratioImNum1] using (hasDerivAt_ratioImNum1 t 0).continuousAt.tendsto)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa [ratioDen1] using (hasDerivAt_ratioDen1 0).continuousAt.tendsto)
    · apply HasDerivAt.lhopital_zero_nhdsNE
      · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioImNum2 t x
      · exact Filter.Eventually.of_forall fun x => hasDerivAt_ratioDen2 x
      · exact eventually_ratioDen3_ne
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa [ratioImNum2] using (hasDerivAt_ratioImNum2 t 0).continuousAt.tendsto)
      · exact tendsto_nhdsWithin_of_tendsto_nhds
          (by simpa [ratioDen2] using (hasDerivAt_ratioDen2 0).continuousAt.tendsto)
      · have hc : ContinuousAt (fun x : ℝ => ratioImNum3 t x / ratioDen3 x) 0 := by
          apply ContinuousAt.div₀
          · unfold ratioImNum3
            fun_prop
          · unfold ratioDen3
            fun_prop
          · simp [ratioDen3]
        simpa [ratioImNum3, ratioDen3] using
          tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

private theorem sineQuotient_eq_re_add_im (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    levyExponentIntegrandWithTruncation Real.sin t x / (extractionWeight x : ℝ) =
      (ratioReNum t x / ratioDen x : ℂ) +
        (ratioImNum t x / ratioDen x : ℂ) * Complex.I := by
  rw [levyExponentIntegrandWithTruncation, Complex.exp_ofReal_mul_I]
  have hden : ratioDen x ≠ 0 := by
    intro h
    have hsin : Real.sin x = x := by
      simpa [ratioDen] using (sub_eq_zero.mp h).symm
    have hsinc : Real.sinc x = 1 := by
      rw [Real.sinc_of_ne_zero hx, hsin, div_self hx]
    have hw0 : extractionWeight x = 0 := by
      apply NNReal.eq
      simp [extractionWeight_coe, hsinc]
    exact (extractionWeight_pos hx).ne' hw0
  have hweight : (extractionWeight x : ℝ) = ratioDen x / x := by
    rw [extractionWeight_coe, Real.sinc_of_ne_zero hx]
    simp only [ratioDen]
    field_simp
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hdenC : ((ratioDen x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden
  simp only [ratioReNum, ratioImNum]
  rw [hweight]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one]
  field_simp [hxC, hdenC]
  ring

private theorem tendsto_sineQuotient (t : ℝ) :
    Tendsto
      (fun x => levyExponentIntegrandWithTruncation Real.sin t x /
        (extractionWeight x : ℝ))
      (𝓝[≠] 0) (𝓝 ((-3 * t ^ 2 : ℝ) : ℂ)) := by
  have hmain := (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_ratio_re t)).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_ratio_im t)).mul_const
      Complex.I)
  have hmain' : Tendsto
      (fun x => (ratioReNum t x / ratioDen x : ℂ) +
        (ratioImNum t x / ratioDen x : ℂ) * Complex.I)
      (𝓝[≠] 0) (𝓝 ((-3 * t ^ 2 : ℝ) : ℂ)) := by
    simpa using hmain
  apply Tendsto.congr' _ hmain'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (sineQuotient_eq_re_add_im t (by simpa using hx)).symm

noncomputable def sineTruncationRatio (t x : ℝ) : ℂ :=
  if x = 0 then ((-3 * t ^ 2 : ℝ) : ℂ)
  else levyExponentIntegrandWithTruncation Real.sin t x / (extractionWeight x : ℝ)

theorem continuous_sineTruncationRatio (t : ℝ) : Continuous (sineTruncationRatio t) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [show sineTruncationRatio t = Function.update
        (fun y => levyExponentIntegrandWithTruncation Real.sin t y /
          (extractionWeight y : ℝ)) 0 (((-3 * t ^ 2 : ℝ) : ℂ)) by
      funext y
      simp [sineTruncationRatio, Function.update_apply]]
    rw [continuousAt_update_same]
    exact tendsto_sineQuotient t
  · have hweight : (extractionWeight x : ℝ) ≠ 0 := by
      exact_mod_cast (extractionWeight_pos hx).ne'
    have hlocal : sineTruncationRatio t =ᶠ[𝓝 x]
        fun y => levyExponentIntegrandWithTruncation Real.sin t y /
          (extractionWeight y : ℝ) := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [sineTruncationRatio, hy]
    have hquot : ContinuousAt
        (fun y => levyExponentIntegrandWithTruncation Real.sin t y /
          (extractionWeight y : ℝ)) x := by
      apply ContinuousAt.div₀
      · unfold levyExponentIntegrandWithTruncation
        fun_prop
      · have hr : Continuous (fun y : ℝ => (extractionWeight y : ℝ)) :=
          continuous_subtype_val.comp continuous_extractionWeight
        exact (Complex.continuous_ofReal.comp hr).continuousAt
      · exact Complex.ofReal_ne_zero.mpr hweight
    exact hquot.congr_of_eventuallyEq hlocal

theorem isAdmissibleLevyTruncation_sin : IsAdmissibleLevyTruncation Real.sin := by
  refine ⟨Real.measurable_sin, 1, zero_le_one, ?_⟩
  intro x
  by_cases hx : |x| < 1
  · rw [levyTruncation_of_abs_lt_one hx, levyIntegrand_toReal_of_abs_lt_one hx]
    rw [Real.norm_eq_abs, abs_sub_comm]
    calc
      |x - Real.sin x| ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
      _ ≤ 1 * x ^ 2 := by
        rw [one_mul, ← sq_abs]
        nlinarith [abs_nonneg x]
  · rw [levyTruncation_of_one_le_abs (le_of_not_gt hx),
      levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hx)]
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x

theorem norm_sin_sub_levyTruncation_le (x : ℝ) :
    ‖Real.sin x - levyTruncation x‖ ≤ (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [levyTruncation_of_abs_lt_one hx, levyIntegrand_toReal_of_abs_lt_one hx]
    rw [Real.norm_eq_abs, abs_sub_comm]
    calc
      |x - Real.sin x| ≤ |x| ^ 3 / 6 := Real.abs_sub_sin_le x
      _ ≤ x ^ 2 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg x]
  · rw [levyTruncation_of_one_le_abs (le_of_not_gt hx),
      levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hx)]
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x

theorem norm_sineLevyExponentIntegrand_le (t x : ℝ) :
    ‖levyExponentIntegrandWithTruncation Real.sin t x‖ ≤
      (levyExponentBound t + |t|) * (levyIntegrand x).toReal := by
  have hdiff := norm_sin_sub_levyTruncation_le x
  have hid : levyExponentIntegrandWithTruncation Real.sin t x =
      levyExponentIntegrand t x -
        (((t * (Real.sin x - levyTruncation x) : ℝ) : ℂ) * Complex.I) := by
    simp only [levyExponentIntegrandWithTruncation, levyExponentIntegrand]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖levyExponentIntegrand t x‖ +
        ‖(((t * (Real.sin x - levyTruncation x) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sub_le _ _
    _ ≤ levyExponentBound t * (levyIntegrand x).toReal +
        |t| * (levyIntegrand x).toReal := by
      gcongr
      · exact norm_levyExponentIntegrand_le t x
      · have hcorr :
            ‖(((t * (Real.sin x - levyTruncation x) : ℝ) : ℂ) * Complex.I)‖ =
              |t| * ‖Real.sin x - levyTruncation x‖ := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I,
              mul_one, Real.norm_eq_abs, abs_mul]
            rw [Real.norm_eq_abs]
        rw [hcorr]
        exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    _ = (levyExponentBound t + |t|) * (levyIntegrand x).toReal := by ring

theorem norm_sineTruncationRatio_le (t x : ℝ) :
    ‖sineTruncationRatio t x‖ ≤
      max (3 * t ^ 2) ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)) := by
  by_cases hx : x = 0
  · subst x
    simp [sineTruncationRatio, sq_nonneg, le_max_left]
  · rw [sineTruncationRatio, if_neg hx, norm_div]
    have hwpos : 0 < (extractionWeight x : ℝ) := by
      exact_mod_cast extractionWeight_pos hx
    have hnum := norm_sineLevyExponentIntegrand_le t x
    have hweight := levyIntegrand_toReal_le_extractionWeight x
    have hA : 0 ≤ levyExponentBound t + |t| := by
      unfold levyExponentBound
      positivity
    have hscaled :
        (levyExponentBound t + |t|) * (levyIntegrand x).toReal ≤
          ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)) *
            (extractionWeight x : ℝ) := by
      calc
        _ ≤ (levyExponentBound t + |t|) *
            (2 * Real.pi ^ 2 * (extractionWeight x : ℝ)) := by gcongr
        _ = _ := by ring
    have hdiv :
        ‖levyExponentIntegrandWithTruncation Real.sin t x‖ /
            (extractionWeight x : ℝ) ≤
          (levyExponentBound t + |t|) * (2 * Real.pi ^ 2) := by
      exact (div_le_iff₀ hwpos).2 (hnum.trans hscaled)
    rw [Complex.norm_real, Real.norm_of_nonneg hwpos.le]
    exact hdiv.trans (le_max_right _ _)

noncomputable def sineTruncationRatioBCF (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨sineTruncationRatio t, continuous_sineTruncationRatio t⟩
    (2 * max (3 * t ^ 2) ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)))
    (fun x y => by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans <| by
        calc
          ‖sineTruncationRatio t x‖ + ‖sineTruncationRatio t y‖ ≤
              max (3 * t ^ 2) ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)) +
                max (3 * t ^ 2) ((levyExponentBound t + |t|) * (2 * Real.pi ^ 2)) := by
            gcongr <;> exact norm_sineTruncationRatio_le t _
          _ = _ := by ring)

end LevyTriplet
end ProbabilityTheory
