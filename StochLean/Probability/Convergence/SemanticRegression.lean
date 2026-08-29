/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureLocal
public import StochLean.ForMathlib.MeasureTheory.Function.LocalConvergenceMetric
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Semantic regression tests for convergence modes

These declarations are mathematical counterexamples used as compile-time regression tests.  In
particular, they prevent local convergence in measure on a sigma-finite space from being silently
identified with Mathlib's global `TendstoInMeasure`.
-/

@[expose] public section

open Filter Set
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory

noncomputable section

/-- The indicator of the unit interval `(n, n + 1]`; its mass escapes to infinity. -/
def escapingUnitInterval (n : ℕ) : ℝ → ℝ :=
  (Ioc (n : ℝ) (n + 1)).indicator (fun _ ↦ 1)

theorem escapingUnitInterval_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (escapingUnitInterval n) :=
  stronglyMeasurable_const.indicator measurableSet_Ioc

/-- Escaping unit intervals converge locally in Lebesgue measure to zero. -/
theorem escapingUnitInterval_tendstoLocallyInMeasure :
    TendstoLocallyInMeasure volume escapingUnitInterval atTop 0 := by
  apply tendstoLocallyInMeasure_of_tendsto_ae
  · exact fun n ↦ (escapingUnitInterval_stronglyMeasurable n).aestronglyMeasurable
  · filter_upwards [] with x
    obtain ⟨N, hN⟩ := exists_nat_ge x
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn ↦ ?_
    have hx : x ∉ Ioc (n : ℝ) (n + 1) := fun hx ↦
      (not_lt_of_ge (hN.trans (mod_cast hn))) hx.1
    simp [escapingUnitInterval, hx]

/-- The same sequence does not converge globally in Lebesgue measure. -/
theorem escapingUnitInterval_not_tendstoInMeasure :
    ¬ TendstoInMeasure volume escapingUnitInterval atTop 0 := by
  intro h
  have ht := h (ENNReal.ofReal (1 / 2 : ℝ)) (ENNReal.ofReal_pos.mpr (by norm_num))
  have hset (n : ℕ) :
      {x | ENNReal.ofReal (1 / 2 : ℝ) ≤ edist (escapingUnitInterval n x) (0 : ℝ)} =
        Ioc (n : ℝ) (n + 1) := by
    ext x
    by_cases hx : x ∈ Ioc (n : ℝ) (n + 1)
    · simp [escapingUnitInterval, hx, edist_dist]
    · simp [escapingUnitInterval, hx, edist_dist]
  have ht' : Tendsto (fun n : ℕ ↦ volume (Ioc (n : ℝ) (n + 1))) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, hset] using ht
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [Real.volume_Ioc, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
      ENNReal.ofReal_one] using ht'
  have hone' : Tendsto (fun _ : ℕ ↦ (1 : ℝ≥0∞)) atTop (𝓝 1) := tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hone' hone)

/-- Null modifications remain different as raw maps but have zero exhaustion pseudodistance. -/
theorem exists_ne_zero_localConvergencePseudodist_eq_zero :
    ∃ f g : StronglyMeasurableMap ℝ ℝ, f ≠ g ∧
      localConvergencePseudodist (μ := volume) f g = 0 := by
  let f : StronglyMeasurableMap ℝ ℝ := ⟨fun _ ↦ 0, stronglyMeasurable_const⟩
  let g : StronglyMeasurableMap ℝ ℝ :=
    ⟨({0} : Set ℝ).indicator (fun _ ↦ 1),
      stronglyMeasurable_const.indicator (measurableSet_singleton 0)⟩
  refine ⟨f, g, ?_, localConvergencePseudodist_eq_zero_of_ae_eq f g ?_⟩
  · intro hfg
    have := congrArg (fun h : StronglyMeasurableMap ℝ ℝ ↦ h 0) hfg
    simp [f, g] at this
  · filter_upwards [volume.ae_ne 0] with x hx
    simp [f, g, hx]

end

end MeasureTheory
