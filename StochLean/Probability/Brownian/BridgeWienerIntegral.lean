/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.DeterministicWienerIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Deterministic Wiener representation of the Brownian bridge

This file implements the singular-kernel representation
`(1 - t) ∫₀ᵗ (1 - s)⁻¹ dBₛ` on `t < 1`.  The value at `t = 1` is defined and
proved separately, so no division-by-zero convention is used as a substitute for the boundary
argument.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

noncomputable def bridgeWienerKernel (t s : ℝ) : ℝ := (1 - t) / (1 - s)

theorem integral_one_sub_inv_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫ s in (0 : ℝ)..t, ((1 - s)⁻¹) ^ 2 = t / (1 - t) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹ ^ 2) 1]
  simp only [sub_zero]
  have hzero : (0 : ℝ) ∉ uIcc (1 - t) 1 := by
    rw [uIcc_of_le (sub_le_self 1 ht0)]
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inl (sub_pos.mpr ht1)
  have hz := integral_zpow (a := 1 - t) (b := 1) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hzero⟩)
  rw [show (fun x : ℝ => x⁻¹ ^ 2) = fun x : ℝ => x ^ (-2 : ℤ) by
    funext x
    simp [zpow_neg]]
  rw [hz]
  have hne : 1 - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht1)
  norm_num [hne]
  field_simp [hne]
  ring

theorem integral_bridgeWienerKernel_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫ s in Ioc (0 : ℝ) t, (bridgeWienerKernel t s) ^ 2 = t * (1 - t) := by
  rw [← intervalIntegral.integral_of_le ht0]
  simp only [bridgeWienerKernel, div_eq_mul_inv, mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_one_sub_inv_sq ht0 ht1]
  have hne : 1 - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht1)
  field_simp [hne]

theorem memLp_bridgeWienerKernel {t : ℝ} (ht1 : t < 1) :
    MemLp (bridgeWienerKernel t) 2 (volume.restrict (Ioc (0 : ℝ) t)) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [bridgeWienerKernel, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    · exact (div_le_one (by linarith [hs.2])).2 (sub_le_sub_left hs.2 1)
    · exact div_nonneg (by linarith) (by linarith [hs.2])

/-- The deterministic bridge kernel as an element of the genuine restricted `L²` quotient. -/
noncomputable def bridgeWienerKernelLp (t : ℝ≥0) (ht : t < 1) :
    Lp ℝ 2 (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) :=
  (memLp_bridgeWienerKernel (show (t : ℝ) < 1 by exact_mod_cast ht)).toLp
    (bridgeWienerKernel (t : ℝ))

theorem integral_bridgeWienerKernelLp_sq (t : ℝ≥0) (ht : t < 1) :
    ∫ s in Ioc (0 : ℝ) (t : ℝ), (bridgeWienerKernelLp t ht s) ^ 2 =
      (t : ℝ) * (1 - (t : ℝ)) := by
  rw [integral_congr_ae]
  · exact integral_bridgeWienerKernel_sq t.coe_nonneg (by exact_mod_cast ht)
  · filter_upwards [(memLp_bridgeWienerKernel
      (show (t : ℝ) < 1 by exact_mod_cast ht)).coeFn_toLp] with s hs
    simpa only [bridgeWienerKernelLp] using congrArg (fun x : ℝ ↦ x ^ 2) hs

/-- Klenke's deterministic Wiener representation of a Brownian bridge on `[0,1]`.
The terminal value is defined separately, so the singular kernel is never evaluated at `t = 1`. -/
noncomputable def IsPreBrownianReal.deterministicWienerBridge
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) : Lp ℝ 2 P :=
  if ht : t < 1 then
    hB.deterministicWienerIntegral t (bridgeWienerKernelLp t ht)
  else 0

@[simp]
theorem IsPreBrownianReal.deterministicWienerBridge_of_lt
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t < 1) :
    hB.deterministicWienerBridge t =
      hB.deterministicWienerIntegral t (bridgeWienerKernelLp t ht) := by
  simp [IsPreBrownianReal.deterministicWienerBridge, ht]

@[simp]
theorem IsPreBrownianReal.deterministicWienerBridge_one
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) :
    hB.deterministicWienerBridge 1 = 0 := by
  simp [IsPreBrownianReal.deterministicWienerBridge]

theorem IsPreBrownianReal.hasLaw_deterministicWienerBridge
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (ht : t < 1) :
    HasLaw (fun ω ↦ hB.deterministicWienerBridge t ω)
      (gaussianReal 0 (((t : ℝ) * (1 - (t : ℝ))).toNNReal)) P := by
  rw [hB.deterministicWienerBridge_of_lt t ht]
  simpa only [integral_bridgeWienerKernelLp_sq] using
    hB.hasLaw_deterministicWienerIntegral t (bridgeWienerKernelLp t ht)

end ProbabilityTheory
