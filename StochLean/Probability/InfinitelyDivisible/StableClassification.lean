/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.StableBounds
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Classification tools for real stable laws

This file develops the measure-theoretic part of Klenke's Theorem 16.22 from the project-owned
stable-law and Lévy-triplet interfaces.  In particular, power-law tails are consequences of
triplet scaling; they are not built into the definition of stability.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace ProbabilityTheory

/-- The two-sided stable Lévy density.  The coefficient order follows the negative/positive
half-lines and the value at zero is fixed to zero. -/
noncomputable def stableLevyDensity
    (α cMinus cPlus x : ℝ) : ℝ≥0∞ :=
  if x < 0 then ENNReal.ofReal (cMinus * (-x) ^ (-α - 1))
  else if 0 < x then ENNReal.ofReal (cPlus * x ^ (-α - 1))
  else 0

/-- The project-owned two-sided power-law Lévy measure. -/
noncomputable def stablePositiveLevyMeasure (α c : ℝ) : Measure ℝ :=
  volume.withDensity fun x =>
    if 0 < x then ENNReal.ofReal (c * x ^ (-α - 1)) else 0

/-- The project-owned two-sided power-law Lévy measure.  The negative component is the reflection
of the corresponding positive measure, which keeps all change-of-variable arguments explicit. -/
noncomputable def stableLevyMeasure
    (α cMinus cPlus : ℝ) : Measure ℝ :=
  stablePositiveLevyMeasure α cPlus +
    (stablePositiveLevyMeasure α cMinus).map (fun x : ℝ => -x)

theorem stableLevyMeasure_Ioi
    {α cMinus cPlus x : ℝ} (hα : 0 < α) (hcPlus : 0 ≤ cPlus) (hx : 0 < x) :
    stableLevyMeasure α cMinus cPlus (Set.Ioi x) =
      ENNReal.ofReal ((cPlus / α) / (x ^ α)) := by
  rw [stableLevyMeasure, Measure.add_apply, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ioi x = Set.Iio (-x) := by
    ext y
    simp
  rw [hpre, stablePositiveLevyMeasure, withDensity_apply _ measurableSet_Ioi,
    stablePositiveLevyMeasure, withDensity_apply _ measurableSet_Iio]
  have hzero :
      (∫⁻ y in Set.Iio (-x),
        if 0 < y then ENNReal.ofReal (cMinus * y ^ (-α - 1)) else 0) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change (if 0 < y then ENNReal.ofReal (cMinus * y ^ (-α - 1)) else 0) =
      (0 : ℝ≥0∞)
    simp only [if_neg (not_lt.mpr (le_of_lt (hy.trans (neg_neg_of_pos hx))))]
  rw [hzero, add_zero]
  have hint : IntegrableOn (fun y : ℝ => cPlus * y ^ (-α - 1)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul cPlus
  have hnonneg : ∀ᵐ y ∂volume.restrict (Set.Ioi x),
      0 ≤ cPlus * y ^ (-α - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg hcPlus (Real.rpow_nonneg (le_of_lt (hx.trans hy)) _)
  have hdensity :
      (fun y => if 0 < y then ENNReal.ofReal (cPlus * y ^ (-α - 1)) else 0)
        =ᵐ[volume.restrict (Set.Ioi x)]
        (fun y => ENNReal.ofReal (cPlus * y ^ (-α - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp [hx.trans hy]
  rw [lintegral_congr_ae hdensity]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx]
  congr 1
  have hxpow : x ^ (-α) = (x ^ α)⁻¹ := by
    simpa only [neg_neg] using Real.rpow_neg hx.le α
  rw [show -α - 1 + 1 = -α by ring, hxpow]
  field_simp [hα.ne']

theorem stableLevyMeasure_Iio_neg
    {α cMinus cPlus x : ℝ} (hα : 0 < α) (hcMinus : 0 ≤ cMinus) (hx : 0 < x) :
    stableLevyMeasure α cMinus cPlus (Set.Iio (-x)) =
      ENNReal.ofReal ((cMinus / α) / (x ^ α)) := by
  rw [stableLevyMeasure, Measure.add_apply, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun y : ℝ => -y) ⁻¹' Set.Iio (-x) = Set.Ioi x := by
    ext y
    simp
  rw [hpre, stablePositiveLevyMeasure, withDensity_apply _ measurableSet_Iio,
    stablePositiveLevyMeasure, withDensity_apply _ measurableSet_Ioi]
  have hzero :
      (∫⁻ y in Set.Iio (-x),
        if 0 < y then ENNReal.ofReal (cPlus * y ^ (-α - 1)) else 0) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change (if 0 < y then ENNReal.ofReal (cPlus * y ^ (-α - 1)) else 0) =
      (0 : ℝ≥0∞)
    simp only [if_neg (not_lt.mpr (le_of_lt (hy.trans (neg_neg_of_pos hx))))]
  rw [hzero, zero_add]
  have hint : IntegrableOn (fun y : ℝ => cMinus * y ^ (-α - 1)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul cMinus
  have hnonneg : ∀ᵐ y ∂volume.restrict (Set.Ioi x),
      0 ≤ cMinus * y ^ (-α - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg hcMinus (Real.rpow_nonneg (le_of_lt (hx.trans hy)) _)
  have hdensity :
      (fun y => if 0 < y then ENNReal.ofReal (cMinus * y ^ (-α - 1)) else 0)
        =ᵐ[volume.restrict (Set.Ioi x)]
        (fun y => ENNReal.ofReal (cMinus * y ^ (-α - 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp [hx.trans hy]
  rw [lintegral_congr_ae hdensity]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx]
  congr 1
  have hxpow : x ^ (-α) = (x ^ α)⁻¹ := by
    simpa only [neg_neg] using Real.rpow_neg hx.le α
  rw [show -α - 1 + 1 = -α by ring, hxpow]
  field_simp [hα.ne']

@[simp]
theorem stablePositiveLevyMeasure_singleton_zero (α c : ℝ) :
    stablePositiveLevyMeasure α c ({0} : Set ℝ) = 0 := by
  rw [stablePositiveLevyMeasure, withDensity_apply _ (MeasurableSet.singleton 0)]
  simp

@[simp]
theorem stableLevyMeasure_singleton_zero (α cMinus cPlus : ℝ) :
    stableLevyMeasure α cMinus cPlus ({0} : Set ℝ) = 0 := by
  rw [stableLevyMeasure, Measure.add_apply,
    Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0)]
  have hpre : (fun x : ℝ => -x) ⁻¹' ({0} : Set ℝ) = {0} := by ext x; simp
  rw [hpre]
  simp

/-- Equality of all finite positive tails determines the restrictions to the positive half-line. -/
theorem restrict_Ioi_zero_eq_of_Ioi_eq
    {ν ξ : Measure ℝ}
    (hfinite : ∀ x : ℝ, 0 < x → ν (Set.Ioi x) < ∞)
    (htail : ∀ x : ℝ, 0 < x → ν (Set.Ioi x) = ξ (Set.Ioi x)) :
    ν.restrict (Set.Ioi 0) = ξ.restrict (Set.Ioi 0) := by
  have hrestrict (r : ℝ) (hr : 0 < r) :
      ν.restrict (Set.Ioi r) = ξ.restrict (Set.Ioi r) := by
    letI : IsFiniteMeasure (ν.restrict (Set.Ioi r)) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hfinite r hr⟩
    apply Measure.ext_of_Iic
    intro a
    have htotal :
        (ν.restrict (Set.Ioi r)) Set.univ =
          (ξ.restrict (Set.Ioi r)) Set.univ := by
      simpa [Measure.restrict_apply_univ] using htail r hr
    have hupper :
        (ν.restrict (Set.Ioi r)) (Set.Ioi a) =
          (ξ.restrict (Set.Ioi r)) (Set.Ioi a) := by
      rw [Measure.restrict_apply measurableSet_Ioi,
        Measure.restrict_apply measurableSet_Ioi]
      simpa only [Set.Ioi_inter_Ioi] using
        htail (max a r) (hr.trans_le (le_max_right a r))
    have hνpartition := measure_add_measure_compl
      (μ := ν.restrict (Set.Ioi r)) (s := Set.Iic a) measurableSet_Iic
    have hξpartition := measure_add_measure_compl
      (μ := ξ.restrict (Set.Ioi r)) (s := Set.Iic a) measurableSet_Iic
    rw [Set.compl_Iic] at hνpartition hξpartition
    have hsum :
        (ν.restrict (Set.Ioi r)) (Set.Iic a) +
            (ξ.restrict (Set.Ioi r)) (Set.Ioi a) =
          (ξ.restrict (Set.Ioi r)) (Set.Iic a) +
            (ξ.restrict (Set.Ioi r)) (Set.Ioi a) := by
      calc
        _ = (ν.restrict (Set.Ioi r)) (Set.Iic a) +
            (ν.restrict (Set.Ioi r)) (Set.Ioi a) := by rw [hupper]
        _ = (ν.restrict (Set.Ioi r)) Set.univ := hνpartition
        _ = (ξ.restrict (Set.Ioi r)) Set.univ := htotal
        _ = _ := hξpartition.symm
    have hsum' :
        (ξ.restrict (Set.Ioi r)) (Set.Ioi a) +
            (ν.restrict (Set.Ioi r)) (Set.Iic a) =
          (ξ.restrict (Set.Ioi r)) (Set.Ioi a) +
            (ξ.restrict (Set.Ioi r)) (Set.Iic a) := by
      calc
        _ = (ν.restrict (Set.Ioi r)) (Set.Iic a) +
            (ξ.restrict (Set.Ioi r)) (Set.Ioi a) := add_comm _ _
        _ = _ := hsum
        _ = _ := add_comm _ _
    have hfin : (ξ.restrict (Set.Ioi r)) (Set.Ioi a) ≠ ∞ := by
      rw [← hupper]
      exact measure_ne_top _ _
    exact (ENNReal.add_right_inj hfin).mp hsum'
  have hunion : (⋃ n : ℕ, Set.Ioi (1 / ((n + 1 : ℕ) : ℝ))) = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (by positivity : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ)).trans hn
    · intro hy
      obtain ⟨m, hmpos, hm⟩ := Real.exists_nat_pos_inv_lt hy
      refine ⟨m, ?_⟩
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hle : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) := by
        apply one_div_le_one_div_of_le hmR
        norm_num
      exact hle.trans_lt (by simpa [one_div] using hm)
  rw [← hunion]
  apply (Measure.restrict_iUnion_congr (μ := ν) (ν := ξ)
    (s := fun n : ℕ => Set.Ioi (1 / ((n + 1 : ℕ) : ℝ)))).2
  intro n
  apply hrestrict
  positivity

/-- Equality of all finite negative tails determines the restrictions to the negative half-line. -/
theorem restrict_Iio_zero_eq_of_Iio_eq
    {ν ξ : Measure ℝ}
    (hfinite : ∀ x : ℝ, x < 0 → ν (Set.Iio x) < ∞)
    (htail : ∀ x : ℝ, x < 0 → ν (Set.Iio x) = ξ (Set.Iio x)) :
    ν.restrict (Set.Iio 0) = ξ.restrict (Set.Iio 0) := by
  have hrestrict (r : ℝ) (hr : r < 0) :
      ν.restrict (Set.Iio r) = ξ.restrict (Set.Iio r) := by
    letI : IsFiniteMeasure (ν.restrict (Set.Iio r)) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hfinite r hr⟩
    apply Measure.ext_of_Ici
    intro a
    have htotal :
        (ν.restrict (Set.Iio r)) Set.univ =
          (ξ.restrict (Set.Iio r)) Set.univ := by
      simpa [Measure.restrict_apply_univ] using htail r hr
    have hlower :
        (ν.restrict (Set.Iio r)) (Set.Iio a) =
          (ξ.restrict (Set.Iio r)) (Set.Iio a) := by
      rw [Measure.restrict_apply measurableSet_Iio,
        Measure.restrict_apply measurableSet_Iio]
      simpa only [Set.Iio_inter_Iio] using
        htail (min a r) ((min_le_right a r).trans_lt hr)
    have hνpartition := measure_add_measure_compl
      (μ := ν.restrict (Set.Iio r)) (s := Set.Ici a) measurableSet_Ici
    have hξpartition := measure_add_measure_compl
      (μ := ξ.restrict (Set.Iio r)) (s := Set.Ici a) measurableSet_Ici
    rw [Set.compl_Ici] at hνpartition hξpartition
    have hsum :
        (ν.restrict (Set.Iio r)) (Set.Ici a) +
            (ξ.restrict (Set.Iio r)) (Set.Iio a) =
          (ξ.restrict (Set.Iio r)) (Set.Ici a) +
            (ξ.restrict (Set.Iio r)) (Set.Iio a) := by
      calc
        _ = (ν.restrict (Set.Iio r)) (Set.Ici a) +
            (ν.restrict (Set.Iio r)) (Set.Iio a) := by rw [hlower]
        _ = (ν.restrict (Set.Iio r)) Set.univ := hνpartition
        _ = (ξ.restrict (Set.Iio r)) Set.univ := htotal
        _ = _ := hξpartition.symm
    have hsum' :
        (ξ.restrict (Set.Iio r)) (Set.Iio a) +
            (ν.restrict (Set.Iio r)) (Set.Ici a) =
          (ξ.restrict (Set.Iio r)) (Set.Iio a) +
            (ξ.restrict (Set.Iio r)) (Set.Ici a) := by
      calc
        _ = (ν.restrict (Set.Iio r)) (Set.Ici a) +
            (ξ.restrict (Set.Iio r)) (Set.Iio a) := add_comm _ _
        _ = _ := hsum
        _ = _ := add_comm _ _
    have hfin : (ξ.restrict (Set.Iio r)) (Set.Iio a) ≠ ∞ := by
      rw [← hlower]
      exact measure_ne_top _ _
    exact (ENNReal.add_right_inj hfin).mp hsum'
  have hunion : (⋃ n : ℕ, Set.Iio (-(1 / ((n + 1 : ℕ) : ℝ)))) = Set.Iio 0 := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      exact hn.trans (neg_lt_zero.mpr (by positivity))
    · intro hy
      obtain ⟨m, hmpos, hm⟩ := Real.exists_nat_pos_inv_lt (neg_pos.mpr hy)
      refine ⟨m, ?_⟩
      have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
      have hle : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) := by
        apply one_div_le_one_div_of_le hmR
        norm_num
      have hsmall : 1 / ((m + 1 : ℕ) : ℝ) < -y :=
        hle.trans_lt (by simpa [one_div] using hm)
      linarith
  rw [← hunion]
  apply (Measure.restrict_iUnion_congr (μ := ν) (ν := ξ)
    (s := fun n : ℕ => Set.Iio (-(1 / ((n + 1 : ℕ) : ℝ))))).2
  intro n
  apply hrestrict
  exact neg_neg_of_pos (by positivity)

namespace IsLevyMeasure

/-- A real Lévy measure is finite on every positive tail bounded away from zero. -/
theorem measure_Ioi_lt_top {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {x : ℝ} (hx : 0 < x) : ν (Set.Ioi x) < ∞ := by
  let c : ℝ≥0∞ := levyIntegrand x
  have hc0 : c ≠ 0 := ne_of_gt (levyIntegrand_pos hx.ne')
  have hsubset : Set.Ioi x ⊆ {y | c ≤ levyIntegrand y} := by
    intro y hy
    dsimp [c, levyIntegrand]
    apply min_le_min le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ hx.le (hx.le.trans hy.le)).mpr hy.le
  have hmul : c * ν (Set.Ioi x) < ∞ :=
    lt_of_le_of_lt
      (by
        calc
          c * ν (Set.Ioi x) ≤ c * ν {y | c ≤ levyIntegrand y} := by gcongr
          _ ≤ ∫⁻ y, levyIntegrand y ∂ν :=
            mul_meas_ge_le_lintegral measurable_levyIntegrand c)
      hν.lintegral_lt_top
  rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
  · exact h.2
  · exact (hc0 h).elim
  · simp [h]

/-- A real Lévy measure is finite on every negative tail bounded away from zero. -/
theorem measure_Iio_lt_top {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {x : ℝ} (hx : x < 0) : ν (Set.Iio x) < ∞ := by
  let c : ℝ≥0∞ := levyIntegrand x
  have hc0 : c ≠ 0 := ne_of_gt (levyIntegrand_pos hx.ne)
  have hsubset : Set.Iio x ⊆ {y | c ≤ levyIntegrand y} := by
    intro y hy
    have hyx : y < x := hy
    dsimp [c, levyIntegrand]
    apply min_le_min le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hyneg : y < 0 := hy.trans hx
    have habs : |x| ≤ |y| := by
      rw [abs_of_neg hx, abs_of_neg hyneg]
      linarith
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg x) (abs_nonneg y)).mpr habs
  have hmul : c * ν (Set.Iio x) < ∞ :=
    lt_of_le_of_lt
      (by
        calc
          c * ν (Set.Iio x) ≤ c * ν {y | c ≤ levyIntegrand y} := by gcongr
          _ ≤ ∫⁻ y, levyIntegrand y ∂ν :=
            mul_meas_ge_le_lintegral measurable_levyIntegrand c)
      hν.lintegral_lt_top
  rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
  · exact h.2
  · exact (hc0 h).elim
  · simp [h]

end IsLevyMeasure

/-! ## Exact affine truncation correction for the stable jump measure -/

/-- For a dilation by `a ≥ 1`, the strict-truncation drift correction is supported exactly on
the annulus `1 / a ≤ |x| < 1`. -/
theorem affineDriftIntegrand_of_one_le {a : ℝ} (ha : 1 ≤ a) (x : ℝ) :
    affineDriftIntegrand a x =
      if 1 / a ≤ |x| ∧ |x| < 1 then -a * x else 0 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  by_cases hx : |x| < 1
  · rw [affineDriftIntegrand, levyTruncation_of_abs_lt_one hx]
    by_cases hring : 1 / a ≤ |x|
    · have hax : 1 ≤ |a * x| := by
        rw [abs_mul, abs_of_pos ha0]
        exact (div_le_iff₀' ha0).mp hring
      rw [if_pos ⟨hring, hx⟩, levyTruncation_of_one_le_abs hax]
      ring
    · have hax : |a * x| < 1 := by
        rw [abs_mul, abs_of_pos ha0]
        exact (lt_div_iff₀' ha0).mp (lt_of_not_ge hring)
      rw [if_neg (fun h => hring h.1), levyTruncation_of_abs_lt_one hax]
      ring
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    have hax : 1 ≤ |a * x| := by
      rw [abs_mul, abs_of_pos ha0]
      nlinarith [abs_nonneg x]
    rw [affineDriftIntegrand, levyTruncation_of_one_le_abs hx',
      levyTruncation_of_one_le_abs hax, if_neg (fun h => hx h.2)]
    ring

/-- Positive-half-line contribution to the affine drift correction of the stable jump measure. -/
theorem stablePositiveLevyMeasure_affineDriftIntegrand
    {α c a : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ a) :
    ∫ x, affineDriftIntegrand a x ∂(stablePositiveLevyMeasure α c) =
      -a * c * ∫ x in Set.Ico (1 / a) 1, x ^ (-α) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hrpow : Measurable (fun x : ℝ => x ^ (-α - 1)) :=
    measurable_of_continuousOn_compl_singleton 0 fun x hx =>
      (Real.continuousAt_rpow_const x (-α - 1) (.inl hx)).continuousWithinAt
  let d : ℝ → ℝ≥0∞ := fun x =>
    if 0 < x then ENNReal.ofReal (c * x ^ (-α - 1)) else 0
  have hd : Measurable d := Measurable.ite measurableSet_Ioi
    ((measurable_const.mul hrpow).ennreal_ofReal) measurable_const
  have hdtop : ∀ᵐ x ∂volume, d x < ∞ := by
    filter_upwards with x
    dsimp [d]
    split_ifs <;> simp
  change ∫ x, affineDriftIntegrand a x ∂(volume.withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd hdtop]
  simp only [smul_eq_mul]
  rw [show
      (fun x : ℝ => (d x).toReal * affineDriftIntegrand a x) =
        (Set.Ico (1 / a) 1).indicator (fun x => -a * c * x ^ (-α)) by
    funext x
    rw [affineDriftIntegrand_of_one_le ha]
    by_cases hx : x ∈ Set.Ico (1 / a) 1
    · have hx0 : 0 < x := (div_pos zero_lt_one ha0).trans_le hx.1
      have habs : |x| = x := abs_of_pos hx0
      rw [Set.indicator_of_mem hx]
      simp only [d, if_pos hx0]
      rw [if_pos]
      · rw [ENNReal.toReal_ofReal]
        · have hpow : x ^ (-α - 1) * x = x ^ (-α) := by
            calc
              x ^ (-α - 1) * x = x ^ (-α - 1) * x ^ (1 : ℝ) := by
                rw [Real.rpow_one]
              _ = x ^ ((-α - 1) + 1) := (Real.rpow_add hx0 _ _).symm
              _ = x ^ (-α) := by congr 1 <;> ring
          calc
            c * x ^ (-α - 1) * (-a * x) =
                (-a * c) * (x ^ (-α - 1) * x) := by ring
            _ = -a * c * x ^ (-α) := by rw [hpow]
        · exact mul_nonneg hc (Real.rpow_nonneg hx0.le _)
      · simpa [habs] using hx
    · rw [Set.indicator_of_notMem hx]
      by_cases hx0 : 0 < x
      · simp only [d, if_pos hx0]
        have hnot : ¬(1 / a ≤ |x| ∧ |x| < 1) := by
          simpa [abs_of_pos hx0] using hx
        rw [if_neg hnot, mul_zero]
      · simp [d, hx0]]
  rw [integral_indicator measurableSet_Ico, integral_const_mul]

theorem levyTruncation_neg (x : ℝ) : levyTruncation (-x) = -levyTruncation x := by
  unfold levyTruncation
  simp only [abs_neg]
  by_cases hx : |x| < 1 <;> simp [hx]

theorem affineDriftIntegrand_neg (a x : ℝ) :
    affineDriftIntegrand a (-x) = -affineDriftIntegrand a x := by
  unfold affineDriftIntegrand
  rw [show a * -x = -(a * x) by ring, levyTruncation_neg, levyTruncation_neg]
  ring

/-- Negative-half-line contribution, obtained internally by reflecting the positive measure. -/
theorem stableNegativeLevyMeasure_affineDriftIntegrand
    {α c a : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ a) :
    ∫ x, affineDriftIntegrand a x
        ∂((stablePositiveLevyMeasure α c).map (fun x : ℝ => -x)) =
      a * c * ∫ x in Set.Ico (1 / a) 1, x ^ (-α) := by
  rw [integral_map (by fun_prop)
    (measurable_affineDriftIntegrand a).aestronglyMeasurable]
  simp_rw [affineDriftIntegrand_neg]
  rw [integral_neg, stablePositiveLevyMeasure_affineDriftIntegrand hc ha]
  ring

/-- The exact annulus-integral formula for the two-sided stable jump measure. -/
theorem stableLevyMeasure_affineDriftIntegrand
    {α cMinus cPlus a : ℝ} (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (ha : 1 ≤ a) (hν : IsLevyMeasure (stableLevyMeasure α cMinus cPlus)) :
    ∫ x, affineDriftIntegrand a x ∂(stableLevyMeasure α cMinus cPlus) =
      a * (cMinus - cPlus) * ∫ x in Set.Ico (1 / a) 1, x ^ (-α) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hsum := hν.integrable_affineDriftIntegrand ha0
  have hplusLe : stablePositiveLevyMeasure α cPlus ≤
      stableLevyMeasure α cMinus cPlus := by
    rw [stableLevyMeasure]
    exact Measure.le_add_right (le_refl _)
  have hminusLe : (stablePositiveLevyMeasure α cMinus).map (fun x : ℝ => -x) ≤
      stableLevyMeasure α cMinus cPlus := by
    rw [stableLevyMeasure]
    exact Measure.le_add_left (le_refl _)
  have hplus : Integrable (affineDriftIntegrand a) (stablePositiveLevyMeasure α cPlus) :=
    hsum.mono_measure hplusLe
  have hminus : Integrable (affineDriftIntegrand a)
      ((stablePositiveLevyMeasure α cMinus).map (fun x : ℝ => -x)) :=
    hsum.mono_measure hminusLe
  rw [stableLevyMeasure, integral_add_measure hplus hminus,
    stablePositiveLevyMeasure_affineDriftIntegrand hcPlus ha,
    stableNegativeLevyMeasure_affineDriftIntegrand hcMinus ha]
  ring

theorem integral_Ico_rpow_neg_of_ne_one
    {α a : ℝ} (hα : α ≠ 1) (ha : 1 ≤ a) :
    ∫ x in Set.Ico (1 / a) 1, x ^ (-α) =
      (1 - (1 / a) ^ (1 - α)) / (1 - α) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlow : 0 < 1 / a := div_pos zero_lt_one ha0
  have hle : 1 / a ≤ 1 := (div_le_one₀ ha0).mpr ha
  have hrne : -α ≠ -1 := by
    intro h
    apply hα
    linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (1 / a) 1 := by
    rw [Set.uIcc_of_le hle]
    simp only [Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hlow)
  have hformula := integral_rpow
    (a := 1 / a) (b := 1) (r := -α) (Or.inr ⟨hrne, hzero⟩)
  rw [intervalIntegral.integral_of_le hle, ← integral_Ico_eq_integral_Ioc] at hformula
  rw [hformula, Real.one_rpow]
  have hexp : -α + 1 = 1 - α := by ring
  rw [hexp]

theorem integral_Ico_rpow_neg_one {a : ℝ} (ha : 1 ≤ a) :
    ∫ x in Set.Ico (1 / a) 1, x ^ (-1 : ℝ) = Real.log a := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlow : 0 < 1 / a := div_pos zero_lt_one ha0
  have hle : 1 / a ≤ 1 := (div_le_one₀ ha0).mpr ha
  simp_rw [Real.rpow_neg_one]
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, integral_inv_of_pos hlow zero_lt_one]
  rw [one_div_div]
  simp

/-- Closed truncation correction for the `α ≠ 1` branch of Lemma 16.25. -/
theorem stableLevyMeasure_affineDriftIntegrand_of_ne_one
    {α cMinus cPlus a : ℝ} (hα : α ≠ 1)
    (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus) (ha : 1 ≤ a)
    (hν : IsLevyMeasure (stableLevyMeasure α cMinus cPlus)) :
    ∫ x, affineDriftIntegrand a x ∂(stableLevyMeasure α cMinus cPlus) =
      (cPlus - cMinus) * (a - a ^ α) / (α - 1) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  rw [stableLevyMeasure_affineDriftIntegrand hcMinus hcPlus ha hν,
    integral_Ico_rpow_neg_of_ne_one hα ha]
  have hinv : (1 / a) ^ (1 - α) = a ^ (α - 1) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hmul : a * a ^ (α - 1) = a ^ α := by
    calc
      a * a ^ (α - 1) = a ^ (1 : ℝ) * a ^ (α - 1) := by rw [Real.rpow_one]
      _ = a ^ ((1 : ℝ) + (α - 1)) := (Real.rpow_add ha0 _ _).symm
      _ = a ^ α := by congr 1 <;> ring
  rw [hinv]
  field_simp [sub_ne_zero.mpr hα]
  calc
    a * (cMinus - cPlus) * (α - 1) * (1 - a ^ (α - 1)) =
        (α - 1) * (cMinus - cPlus) * (a - a * a ^ (α - 1)) := by ring
    _ = (α - 1) * (cMinus - cPlus) * (a - a ^ α) := by rw [hmul]
    _ = (1 - α) * (cPlus - cMinus) * (a - a ^ α) := by ring

/-- Closed logarithmic truncation correction for the `α = 1` branch of Lemma 16.25. -/
theorem stableLevyMeasure_affineDriftIntegrand_one
    {cMinus cPlus a : ℝ} (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (ha : 1 ≤ a) (hν : IsLevyMeasure (stableLevyMeasure 1 cMinus cPlus)) :
    ∫ x, affineDriftIntegrand a x ∂(stableLevyMeasure 1 cMinus cPlus) =
      (cMinus - cPlus) * a * Real.log a := by
  rw [stableLevyMeasure_affineDriftIntegrand hcMinus hcPlus ha hν]
  simp only [integral_Ico_rpow_neg_one ha]
  ring

namespace LevyTriplet

/-- Positive-tail form of the jump-measure scaling identity for an indexed stable law. -/
theorem jumpMeasure_Ioi_scaling_of_indexed
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (n : ℝ≥0∞) * η.jumpMeasure (Set.Ioi x) =
      η.jumpMeasure (Set.Ioi (x / ((n : ℝ) ^ (1 / α)))) := by
  obtain ⟨d, hpow⟩ := hstable.2.2 n hn
  let a : ℝ := (n : ℝ) ^ (1 / α)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hmeasure := jumpMeasure_scaling_of_convPow_eq_affine
    n a d ha hη hpow
  have happly := congrArg (fun m : Measure ℝ => m (Set.Ioi x)) hmeasure
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) measurableSet_Ioi] at happly
  have hpre : (fun y : ℝ => a * y) ⁻¹' Set.Ioi x = Set.Ioi (x / a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi]
    simpa [mul_comm] using (div_lt_iff₀ ha).symm
  rw [hpre] at happly
  simpa [a] using happly

theorem jumpMeasure_Ioi_scaling_toReal_of_indexed
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (n : ℝ) * (η.jumpMeasure (Set.Ioi x)).toReal =
      (η.jumpMeasure (Set.Ioi (x / ((n : ℝ) ^ (1 / α))))).toReal := by
  have h := congrArg ENNReal.toReal
    (jumpMeasure_Ioi_scaling_of_indexed hstable hη n hn hx)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

/-- Negative-tail form of the jump-measure scaling identity for an indexed stable law. -/
theorem jumpMeasure_Iio_scaling_of_indexed
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x < 0) :
    (n : ℝ≥0∞) * η.jumpMeasure (Set.Iio x) =
      η.jumpMeasure (Set.Iio (x / ((n : ℝ) ^ (1 / α)))) := by
  obtain ⟨d, hpow⟩ := hstable.2.2 n hn
  let a : ℝ := (n : ℝ) ^ (1 / α)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hmeasure := jumpMeasure_scaling_of_convPow_eq_affine
    n a d ha hη hpow
  have happly := congrArg (fun m : Measure ℝ => m (Set.Iio x)) hmeasure
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) measurableSet_Iio] at happly
  have hpre : (fun y : ℝ => a * y) ⁻¹' Set.Iio x = Set.Iio (x / a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iio]
    simpa [mul_comm] using (lt_div_iff₀ ha).symm
  rw [hpre] at happly
  simpa [a] using happly

theorem jumpMeasure_Iio_scaling_toReal_of_indexed
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : x < 0) :
    (n : ℝ) * (η.jumpMeasure (Set.Iio x)).toReal =
      (η.jumpMeasure (Set.Iio (x / ((n : ℝ) ^ (1 / α))))).toReal := by
  have h := congrArg ENNReal.toReal
    (jumpMeasure_Iio_scaling_of_indexed hstable hη n hn hx)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h

end LevyTriplet

/-- A monotone function which has the prescribed power values at every positive rational scale
has that power form everywhere.  The two one-sided rational approximations deliberately avoid
assuming continuity of the monotone function. -/
theorem antitone_eq_div_rpow_of_rat
    (F : ℝ → ℝ) (α c : ℝ) (hα : 0 < α)
    (hanti : AntitoneOn F (Set.Ioi 0))
    (hrat : ∀ q : ℚ, 0 < (q : ℝ) →
      F ((q : ℝ) ^ (1 / α)) = c / (q : ℝ))
    {x : ℝ} (hx : 0 < x) :
    F x = c / (x ^ α) := by
  let y : ℝ := x ^ α
  have hy : 0 < y := Real.rpow_pos_of_pos hx α
  have hroot : y ^ (1 / α) = x := by
    dsimp [y]
    rw [← Real.rpow_mul hx.le]
    field_simp
    exact Real.rpow_one x
  apply le_antisymm
  · obtain ⟨u, _huMono, hu_lt, hu_lim⟩ := Real.exists_seq_rat_strictMono_tendsto y
    have hu_pos_ev : ∀ᶠ n : ℕ in atTop, 0 < (u n : ℝ) :=
      hu_lim.eventually (Ioi_mem_nhds hy)
    rw [eventually_atTop] at hu_pos_ev
    obtain ⟨N, hN⟩ := hu_pos_ev
    let q : ℕ → ℚ := fun n => u (n + N)
    have hq_pos (n : ℕ) : 0 < (q n : ℝ) := hN (n + N) (Nat.le_add_left N n)
    have hq_lt (n : ℕ) : (q n : ℝ) < y := hu_lt (n + N)
    have hq_lim : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 y) := by
      exact hu_lim.comp (tendsto_add_atTop_nat N)
    have hle (n : ℕ) : F x ≤ c / (q n : ℝ) := by
      rw [← hrat (q n) (hq_pos n)]
      apply hanti
      · exact Real.rpow_pos_of_pos (hq_pos n) _
      · exact hx
      · rw [← hroot]
        exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (one_div_pos.mpr hα)).monotoneOn
          (le_of_lt (hq_pos n)) hy.le (le_of_lt (hq_lt n))
    have hright : Tendsto (fun n => c / (q n : ℝ)) atTop (𝓝 (c / y)) :=
      tendsto_const_nhds.div hq_lim hy.ne'
    simpa [y] using le_of_tendsto_of_tendsto tendsto_const_nhds hright
      (Eventually.of_forall hle)
  · obtain ⟨u, _huAnti, hu_gt, hu_lim⟩ := Real.exists_seq_rat_strictAnti_tendsto y
    have hq_pos (n : ℕ) : 0 < (u n : ℝ) := hy.trans (hu_gt n)
    have hle (n : ℕ) : c / (u n : ℝ) ≤ F x := by
      rw [← hrat (u n) (hq_pos n)]
      apply hanti
      · exact hx
      · exact Real.rpow_pos_of_pos (hq_pos n) _
      · rw [← hroot]
        exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos (one_div_pos.mpr hα)).monotoneOn
          hy.le (le_of_lt (hq_pos n)) (le_of_lt (hu_gt n))
    have hleft : Tendsto (fun n => c / (u n : ℝ)) atTop (𝓝 (c / y)) :=
      tendsto_const_nhds.div hu_lim hy.ne'
    simpa [y] using le_of_tendsto hleft (Eventually.of_forall hle)

namespace LevyTriplet

/-- The positive tail of the Lévy measure of an indexed stable law is an exact power law. -/
theorem jumpMeasure_Ioi_toReal_eq_rpow
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    {x : ℝ} (hx : 0 < x) :
    (η.jumpMeasure (Set.Ioi x)).toReal =
      (η.jumpMeasure (Set.Ioi 1)).toReal / (x ^ α) := by
  let F : ℝ → ℝ := fun z => (η.jumpMeasure (Set.Ioi z)).toReal
  let c : ℝ := F 1
  have hanti : AntitoneOn F (Set.Ioi 0) := by
    intro z hz w hw hzw
    dsimp [F]
    apply ENNReal.toReal_mono
    · exact ne_of_lt (η.isLevyMeasure_jumpMeasure.measure_Ioi_lt_top hz)
    · exact measure_mono (Ioi_subset_Ioi hzw)
  have hnat (n : ℕ) (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
      (n : ℝ) * F z = F (z / ((n : ℝ) ^ (1 / α))) := by
    exact jumpMeasure_Ioi_scaling_toReal_of_indexed hstable hη n hn hz
  have hrat (q : ℚ) (hq : 0 < (q : ℝ)) :
      F ((q : ℝ) ^ (1 / α)) = c / (q : ℝ) := by
    have hqQ : 0 < q := by exact_mod_cast hq
    let m : ℕ := q.num.natAbs
    let n : ℕ := q.den
    have hnum : 0 < q.num := Rat.num_pos.mpr hqQ
    have hm : 0 < m := Int.natAbs_pos.mpr hnum.ne'
    have hn : 0 < n := q.den_pos
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmcast : (m : ℝ) = (q.num : ℝ) := by
      have hmInt : (m : ℤ) = q.num := by
        dsimp [m]
        exact Int.natAbs_of_nonneg hnum.le
      exact_mod_cast hmInt
    have hqrepr : (q : ℝ) = (m : ℝ) / (n : ℝ) := by
      rw [Rat.cast_def]
      simpa [m, n, hmcast]
    let am : ℝ := (m : ℝ) ^ (1 / α)
    let an : ℝ := (n : ℝ) ^ (1 / α)
    have ham : 0 < am := Real.rpow_pos_of_pos hmR _
    have han : 0 < an := Real.rpow_pos_of_pos hnR _
    have hmScale := hnat m hm (z := am / an) (div_pos ham han)
    have hnScale := hnat n hn (z := 1) zero_lt_one
    have hmarg : (am / an) / am = 1 / an := by field_simp
    have hnarg : 1 / an = 1 / ((n : ℝ) ^ (1 / α)) := rfl
    rw [hmarg] at hmScale
    rw [hnarg] at hnScale
    have hlinear : (m : ℝ) * F (am / an) = (n : ℝ) * c := by
      exact hmScale.trans hnScale.symm
    have hscale : am / an = (q : ℝ) ^ (1 / α) := by
      dsimp [am, an]
      rw [hqrepr, Real.div_rpow hmR.le hnR.le]
    rw [← hscale]
    rw [hqrepr]
    field_simp [hmR.ne', hnR.ne']
    nlinarith
  simpa [F, c] using antitone_eq_div_rpow_of_rat F α c hstable.1 hanti hrat hx

/-- The negative tail of the Lévy measure of an indexed stable law is an exact power law. -/
theorem jumpMeasure_Iio_neg_toReal_eq_rpow
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    {x : ℝ} (hx : 0 < x) :
    (η.jumpMeasure (Set.Iio (-x))).toReal =
      (η.jumpMeasure (Set.Iio (-1))).toReal / (x ^ α) := by
  let F : ℝ → ℝ := fun z => (η.jumpMeasure (Set.Iio (-z))).toReal
  let c : ℝ := F 1
  have hanti : AntitoneOn F (Set.Ioi 0) := by
    intro z hz w hw hzw
    dsimp [F]
    apply ENNReal.toReal_mono
    · exact ne_of_lt (η.isLevyMeasure_jumpMeasure.measure_Iio_lt_top (neg_neg_of_pos hz))
    · exact measure_mono (Iio_subset_Iio (neg_le_neg hzw))
  have hnat (n : ℕ) (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
      (n : ℝ) * F z = F (z / ((n : ℝ) ^ (1 / α))) := by
    have h := jumpMeasure_Iio_scaling_toReal_of_indexed
      hstable hη n hn (x := -z) (neg_neg_of_pos hz)
    simpa only [F, neg_div] using h
  have hrat (q : ℚ) (hq : 0 < (q : ℝ)) :
      F ((q : ℝ) ^ (1 / α)) = c / (q : ℝ) := by
    have hqQ : 0 < q := by exact_mod_cast hq
    let m : ℕ := q.num.natAbs
    let n : ℕ := q.den
    have hnum : 0 < q.num := Rat.num_pos.mpr hqQ
    have hm : 0 < m := Int.natAbs_pos.mpr hnum.ne'
    have hn : 0 < n := q.den_pos
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmcast : (m : ℝ) = (q.num : ℝ) := by
      have hmInt : (m : ℤ) = q.num := by
        dsimp [m]
        exact Int.natAbs_of_nonneg hnum.le
      exact_mod_cast hmInt
    have hqrepr : (q : ℝ) = (m : ℝ) / (n : ℝ) := by
      rw [Rat.cast_def]
      simpa [m, n, hmcast]
    let am : ℝ := (m : ℝ) ^ (1 / α)
    let an : ℝ := (n : ℝ) ^ (1 / α)
    have ham : 0 < am := Real.rpow_pos_of_pos hmR _
    have han : 0 < an := Real.rpow_pos_of_pos hnR _
    have hmScale := hnat m hm (z := am / an) (div_pos ham han)
    have hnScale := hnat n hn (z := 1) zero_lt_one
    have hmarg : (am / an) / am = 1 / an := by field_simp
    have hnarg : 1 / an = 1 / ((n : ℝ) ^ (1 / α)) := rfl
    rw [hmarg] at hmScale
    rw [hnarg] at hnScale
    have hlinear : (m : ℝ) * F (am / an) = (n : ℝ) * c := by
      exact hmScale.trans hnScale.symm
    have hscale : am / an = (q : ℝ) ^ (1 / α) := by
      dsimp [am, an]
      rw [hqrepr, Real.div_rpow hmR.le hnR.le]
    rw [← hscale]
    rw [hqrepr]
    field_simp [hmR.ne', hnR.ne']
    nlinarith
  simpa [F, c] using antitone_eq_div_rpow_of_rat F α c hstable.1 hanti hrat hx

/-- Homogeneous jump-measure classification in Theorem 16.22 for an indexed stable law.  The
coefficients are nonnegative and are normalized as density coefficients, namely `α` times the
two unit-tail masses. -/
theorem jumpMeasure_eq_stableLevyMeasure
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ) :
    let cMinus := α * (η.jumpMeasure (Set.Iio (-1))).toReal
    let cPlus := α * (η.jumpMeasure (Set.Ioi 1)).toReal
    η.jumpMeasure = stableLevyMeasure α cMinus cPlus := by
  let CMinus : ℝ := (η.jumpMeasure (Set.Iio (-1))).toReal
  let CPlus : ℝ := (η.jumpMeasure (Set.Ioi 1)).toReal
  let cMinus : ℝ := α * CMinus
  let cPlus : ℝ := α * CPlus
  have hCMinus : 0 ≤ CMinus := ENNReal.toReal_nonneg
  have hCPlus : 0 ≤ CPlus := ENNReal.toReal_nonneg
  have hcMinus : 0 ≤ cMinus := mul_nonneg hstable.1.le hCMinus
  have hcPlus : 0 ≤ cPlus := mul_nonneg hstable.1.le hCPlus
  have hcandidate_pos (x : ℝ) (hx : 0 < x) :
      stableLevyMeasure α cMinus cPlus (Set.Ioi x) =
        ENNReal.ofReal (CPlus / (x ^ α)) := by
    rw [stableLevyMeasure_Ioi hstable.1 hcPlus hx]
    congr 1
    dsimp [cPlus]
    field_simp [hstable.1.ne']
  have hcandidate_neg (x : ℝ) (hx : 0 < x) :
      stableLevyMeasure α cMinus cPlus (Set.Iio (-x)) =
        ENNReal.ofReal (CMinus / (x ^ α)) := by
    rw [stableLevyMeasure_Iio_neg hstable.1 hcMinus hx]
    congr 1
    dsimp [cMinus]
    field_simp [hstable.1.ne']
  have htail_pos (x : ℝ) (hx : 0 < x) :
      η.jumpMeasure (Set.Ioi x) = stableLevyMeasure α cMinus cPlus (Set.Ioi x) := by
    have hcandTop : stableLevyMeasure α cMinus cPlus (Set.Ioi x) ≠ ∞ := by
      rw [hcandidate_pos x hx]
      exact ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_eq_toReal_iff'
      (ne_of_lt (η.isLevyMeasure_jumpMeasure.measure_Ioi_lt_top hx)) hcandTop).mp
    rw [jumpMeasure_Ioi_toReal_eq_rpow hstable hη hx, hcandidate_pos x hx,
      ENNReal.toReal_ofReal]
    exact div_nonneg hCPlus (Real.rpow_nonneg hx.le _)
  have htail_neg (x : ℝ) (hx : x < 0) :
      η.jumpMeasure (Set.Iio x) = stableLevyMeasure α cMinus cPlus (Set.Iio x) := by
    let y : ℝ := -x
    have hy : 0 < y := neg_pos.mpr hx
    have hxneg : -y = x := by dsimp [y]; ring
    have hcandTop : stableLevyMeasure α cMinus cPlus (Set.Iio x) ≠ ∞ := by
      rw [← hxneg, hcandidate_neg y hy]
      exact ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_eq_toReal_iff'
      (ne_of_lt (η.isLevyMeasure_jumpMeasure.measure_Iio_lt_top hx)) hcandTop).mp
    rw [← hxneg, jumpMeasure_Iio_neg_toReal_eq_rpow hstable hη hy,
      hcandidate_neg y hy, ENNReal.toReal_ofReal]
    exact div_nonneg hCMinus (Real.rpow_nonneg hy.le _)
  have hpos :
      η.jumpMeasure.restrict (Set.Ioi 0) =
        (stableLevyMeasure α cMinus cPlus).restrict (Set.Ioi 0) :=
    restrict_Ioi_zero_eq_of_Ioi_eq
      (fun x hx => η.isLevyMeasure_jumpMeasure.measure_Ioi_lt_top hx) htail_pos
  have hneg :
      η.jumpMeasure.restrict (Set.Iio 0) =
        (stableLevyMeasure α cMinus cPlus).restrict (Set.Iio 0) :=
    restrict_Iio_zero_eq_of_Iio_eq
      (fun x hx => η.isLevyMeasure_jumpMeasure.measure_Iio_lt_top hx) htail_neg
  let S : Fin 3 → Set ℝ := fun i =>
    if i = 0 then Set.Iio 0 else if i = 1 then {0} else Set.Ioi 0
  have hSuniv : (⋃ i, S i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exact ⟨0, by simp [S, hx]⟩
    · exact ⟨1, by simp [S, hx]⟩
    · exact ⟨2, by simp [S, hx]⟩
  apply Measure.ext_of_iUnion_eq_univ (μ := η.jumpMeasure)
    (ν := stableLevyMeasure α cMinus cPlus) hSuniv
  intro i
  fin_cases i
  · simpa [S] using hneg
  · apply Measure.ext
    intro s hs
    simp [S, Measure.restrict_apply hs, η.isLevyMeasure_jumpMeasure.atom_zero]
  · simpa [S] using hpos

/-! ## Lemma 16.25: exact stable centerings -/

/-- In the indexed `α ≠ 1` jump branch, triplet uniqueness and the project-owned power-law
measure give the exact affine centering from Klenke's Lemma 16.25. -/
theorem stable_center_eq_of_ne_one
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (hα : α ≠ 1) (n : ℕ) (hn : 0 < n) :
    ∃ d : ℝ,
      ProbabilityMeasure.convPow μ n =
        ProbabilityMeasure.affineMap ((n : ℝ) ^ (1 / α)) d μ ∧
      d =
        (η.drift +
          ((α * (η.jumpMeasure (Set.Ioi 1)).toReal) -
              (α * (η.jumpMeasure (Set.Iio (-1))).toReal)) / (α - 1)) *
          ((n : ℝ) - (n : ℝ) ^ (1 / α)) := by
  obtain ⟨d, hpow⟩ := hstable.2.2 n hn
  let a : ℝ := (n : ℝ) ^ (1 / α)
  let cMinus : ℝ := α * (η.jumpMeasure (Set.Iio (-1))).toReal
  let cPlus : ℝ := α * (η.jumpMeasure (Set.Ioi 1)).toReal
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha1 : 1 ≤ a := Real.one_le_rpow hnR (one_div_pos.mpr hstable.1).le
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hcMinus : 0 ≤ cMinus :=
    mul_nonneg hstable.1.le ENNReal.toReal_nonneg
  have hcPlus : 0 ≤ cPlus :=
    mul_nonneg hstable.1.le ENNReal.toReal_nonneg
  have hjump : η.jumpMeasure = stableLevyMeasure α cMinus cPlus := by
    simpa [cMinus, cPlus] using jumpMeasure_eq_stableLevyMeasure hstable hη
  have hlevy : IsLevyMeasure (stableLevyMeasure α cMinus cPlus) := by
    rw [← hjump]
    exact η.isLevyMeasure_jumpMeasure
  have hpower : a ^ α = (n : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    have hexp : 1 / α * α = 1 := by field_simp [hstable.1.ne']
    rw [hexp, Real.rpow_one]
  have hcorr :
      ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure =
        (cPlus - cMinus) * (a - (n : ℝ)) / (α - 1) := by
    rw [hjump, stableLevyMeasure_affineDriftIntegrand_of_ne_one
      hα hcMinus hcPlus ha1 hlevy, hpower]
  have hdrift := drift_scaling_of_convPow_eq_affine n a d ha0 hη
    (by simpa [a] using hpow)
  rw [hcorr] at hdrift
  refine ⟨d, hpow, ?_⟩
  dsimp [a, cMinus, cPlus] at hdrift ⊢
  field_simp [sub_ne_zero.mpr hα] at hdrift ⊢
  linarith

/-- The exceptional indexed `α = 1` branch has logarithmic centering. -/
theorem stable_center_eq_one
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex 1) (hη : η.Represents μ)
    (n : ℕ) (hn : 0 < n) :
    ∃ d : ℝ,
      ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap (n : ℝ) d μ ∧
      d = ((η.jumpMeasure (Set.Ioi 1)).toReal -
          (η.jumpMeasure (Set.Iio (-1))).toReal) * n * Real.log n := by
  obtain ⟨d, hpow⟩ := hstable.2.2 n hn
  let cMinus : ℝ := (η.jumpMeasure (Set.Iio (-1))).toReal
  let cPlus : ℝ := (η.jumpMeasure (Set.Ioi 1)).toReal
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcMinus : 0 ≤ cMinus := ENNReal.toReal_nonneg
  have hcPlus : 0 ≤ cPlus := ENNReal.toReal_nonneg
  have hjump : η.jumpMeasure = stableLevyMeasure 1 cMinus cPlus := by
    simpa [cMinus, cPlus] using jumpMeasure_eq_stableLevyMeasure hstable hη
  have hlevy : IsLevyMeasure (stableLevyMeasure 1 cMinus cPlus) := by
    rw [← hjump]
    exact η.isLevyMeasure_jumpMeasure
  have hcorr :
      ∫ x, affineDriftIntegrand (n : ℝ) x ∂η.jumpMeasure =
        (cMinus - cPlus) * n * Real.log n := by
    rw [hjump, stableLevyMeasure_affineDriftIntegrand_one hcMinus hcPlus hnR hlevy]
  have hpow' : ProbabilityMeasure.convPow μ n =
      ProbabilityMeasure.affineMap (n : ℝ) d μ := by
    simpa using hpow
  have hdrift := drift_scaling_of_convPow_eq_affine n (n : ℝ) d hn0 hη hpow'
  rw [hcorr] at hdrift
  refine ⟨d, hpow', ?_⟩
  dsimp [cMinus, cPlus] at hdrift ⊢
  linarith

end LevyTriplet

/-- For `α ≠ 1`, translating by the triplet-determined fixed center turns an indexed broad
stable law into a strictly indexed stable law. -/
theorem IsStableInBroadSenseWithIndex.shift_isStableWithIndex_of_triplet
    {α : ℝ} {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hη : η.Represents μ)
    (hα : α ≠ 1) :
    let center := η.drift +
      ((α * (η.jumpMeasure (Set.Ioi 1)).toReal) -
          (α * (η.jumpMeasure (Set.Iio (-1))).toReal)) / (α - 1)
    (ProbabilityMeasure.affineMap 1 (-center) μ).IsStableWithIndex α := by
  let center := η.drift +
    ((α * (η.jumpMeasure (Set.Ioi 1)).toReal) -
        (α * (η.jumpMeasure (Set.Iio (-1))).toReal)) / (α - 1)
  apply hstable.shift_isStableWithIndex (b := center)
  intro n hn
  simpa [center] using LevyTriplet.stable_center_eq_of_ne_one hstable hη hα n hn

/-- In the symmetric `α = 1` case the logarithmic centering vanishes, hence the law is
strictly one-stable (the structural Cauchy branch). -/
theorem IsStableInBroadSenseWithIndex.one_isStableWithIndex_of_symmetric_jumpTails
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex 1) (hη : η.Represents μ)
    (hsymmetric : (η.jumpMeasure (Set.Ioi 1)).toReal =
      (η.jumpMeasure (Set.Iio (-1))).toReal) :
    μ.IsStableWithIndex 1 := by
  apply hstable.one_isStableWithIndex_of_logCenter
    (η.jumpMeasure (Set.Ioi 1)).toReal
    (η.jumpMeasure (Set.Iio (-1))).toReal hsymmetric
  intro n hn
  simpa using LevyTriplet.stable_center_eq_one hstable hη n hn

end ProbabilityTheory
