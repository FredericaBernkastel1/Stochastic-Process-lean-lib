/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureLocal
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Fast convergence on sigma-finite measure spaces

These are the local Borel--Cantelli criteria from Klenke, Theorem 6.12.  All summability
hypotheses are imposed after restriction to an arbitrary measurable finite-measure set.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [SigmaFinite μ] [PseudoEMetricSpace E]

/-- Klenke 6.12(ii), in the local sigma-finite form.  Summability of every fixed-distance bad
event on every finite-measure restriction yields almost-everywhere convergence. -/
theorem tendsto_ae_of_summable_measure_edist_local {f : ℕ → α → E} {g : α → E}
    (hsum : ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → ∀ ε : ENNReal, 0 < ε →
      (∑' n, (μ.restrict s) {x | ε ≤ edist (f n x) (g x)}) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  let bad (k n : ℕ) : Set α :=
    {x | (2 : ENNReal)⁻¹ ^ k ≤ edist (f n x) (g x)}
  have hnull (m k : ℕ) :
      μ (limsup (fun n ↦ bad k n ∩ spanningSets μ m) atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    have hs := hsum (spanningSets μ m) (measurableSet_spanningSets μ m)
      (measure_spanningSets_lt_top μ m).ne ((2 : ENNReal)⁻¹ ^ k)
        (ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) _)
    simpa only [bad, Measure.restrict_apply' (measurableSet_spanningSets μ m)] using hs
  have hgood : ∀ᵐ x ∂μ, ∀ m k : ℕ,
      x ∉ limsup (fun n ↦ bad k n ∩ spanningSets μ m) atTop := by
    apply eventually_countable_forall.mpr
    intro m
    apply eventually_countable_forall.mpr
    intro k
    rw [ae_iff]
    rw [show {x | ¬x ∉ limsup (fun n ↦ bad k n ∩ spanningSets μ m) atTop} =
      limsup (fun n ↦ bad k n ∩ spanningSets μ m) atTop by ext x; simp]
    exact hnull m k
  filter_upwards [hgood] with x hx
  rw [EMetric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
  obtain ⟨m, hm⟩ := eventually_atTop.1 (eventually_mem_spanningSets μ x)
  have hxlim := hx m k
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hxlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 hxlim
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnot := hN n hn
  have hxspan := hm m le_rfl
  have hdist : edist (f n x) (g x) < (2 : ENNReal)⁻¹ ^ k := by
    exact lt_of_not_ge (fun hge ↦ hnot ⟨hge, hxspan⟩)
  exact hdist.trans hk

/-- Klenke 6.12(iii).  If adjacent distances exceed a summable real threshold only summably
often on each finite restriction, then a sequence in a complete metric target has a strongly
measurable almost-everywhere limit. -/
theorem exists_stronglyMeasurable_tendsto_ae_of_fast_cauchy_local
    {F : Type*} [MetricSpace F] [CompleteSpace F] [Nonempty F]
    {f : ℕ → α → F} {ε : ℕ → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (hε : Summable ε)
    (hsum : ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ →
      (∑' n, (μ.restrict s) {x | ε n < dist (f n x) (f (n + 1) x)}) ≠ ∞) :
    ∃ g : α → F, StronglyMeasurable g ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  let bad (n : ℕ) : Set α := {x | ε n < dist (f n x) (f (n + 1) x)}
  have hnull (m : ℕ) :
      μ (limsup (fun n ↦ bad n ∩ spanningSets μ m) atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    have hs := hsum (spanningSets μ m) (measurableSet_spanningSets μ m)
      (measure_spanningSets_lt_top μ m).ne
    simpa only [bad, Measure.restrict_apply' (measurableSet_spanningSets μ m)] using hs
  have hgood : ∀ᵐ x ∂μ, ∀ m : ℕ,
      x ∉ limsup (fun n ↦ bad n ∩ spanningSets μ m) atTop := by
    apply eventually_countable_forall.mpr
    intro m
    rw [ae_iff]
    rw [show {x | ¬x ∉ limsup (fun n ↦ bad n ∩ spanningSets μ m) atTop} =
      limsup (fun n ↦ bad n ∩ spanningSets μ m) atTop by ext x; simp]
    exact hnull m
  let g : α → F := fun x ↦ limUnder atTop (fun n ↦ f n x)
  refine ⟨g, StronglyMeasurable.limUnder hf, ?_⟩
  filter_upwards [hgood] with x hx
  obtain ⟨m, hm⟩ := eventually_atTop.1 (eventually_mem_spanningSets μ x)
  have hxlim := hx m
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hxlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 hxlim
  have hdist (n : ℕ) (hn : N ≤ n) : dist (f n x) (f (n + 1) x) ≤ ε n := by
    have hnot := hN n hn
    have hxspan := hm m le_rfl
    exact not_lt.mp (fun hlt ↦ hnot ⟨hlt, hxspan⟩)
  let d : ℕ → ℝ := fun n ↦ if N ≤ n then ε n else dist (f n x) (f (n + 1) x)
  have hd : Summable d := by
    apply hε.congr_atTop
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [d, if_pos hn]
  have hcauchy : CauchySeq (fun n ↦ f n x) := by
    apply cauchySeq_of_dist_le_of_summable d _ hd
    intro n
    by_cases hn : N ≤ n
    · simpa only [d, if_pos hn] using hdist n hn
    · simp only [d, if_neg hn, Nat.succ_eq_add_one]
      exact le_rfl
  exact hcauchy.tendsto_limUnder

/-- Diagonal version of the fast-Cauchy criterion.  It is enough to control the `n`-th adjacent
increment on the `n`-th canonical sigma-finite spanning set.  This is the form used to prove
completeness of local convergence in measure. -/
theorem exists_stronglyMeasurable_tendsto_ae_of_fast_cauchy_spanning
    {F : Type*} [MetricSpace F] [CompleteSpace F] [Nonempty F]
    {f : ℕ → α → F} {ε : ℕ → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (hε : Summable ε)
    (hsum : (∑' n, (μ.restrict (spanningSets μ n))
      {x | ε n < dist (f n x) (f (n + 1) x)}) ≠ ∞) :
    ∃ g : α → F, StronglyMeasurable g ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  let bad (n : ℕ) : Set α := {x | ε n < dist (f n x) (f (n + 1) x)}
  have hnull : μ (limsup (fun n ↦ bad n ∩ spanningSets μ n) atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    simpa only [bad, Measure.restrict_apply' (measurableSet_spanningSets μ _)] using hsum
  have hgood : ∀ᵐ x ∂μ, x ∉ limsup (fun n ↦ bad n ∩ spanningSets μ n) atTop := by
    rw [ae_iff]
    rw [show {x | ¬x ∉ limsup (fun n ↦ bad n ∩ spanningSets μ n) atTop} =
      limsup (fun n ↦ bad n ∩ spanningSets μ n) atTop by ext x; simp]
    exact hnull
  let g : α → F := fun x ↦ limUnder atTop (fun n ↦ f n x)
  refine ⟨g, StronglyMeasurable.limUnder hf, ?_⟩
  filter_upwards [hgood] with x hx
  rw [mem_limsup_iff_frequently_mem, not_frequently] at hx
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hx
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (eventually_mem_spanningSets μ x)
  let N := max N₁ N₂
  have hdist (n : ℕ) (hn : N ≤ n) : dist (f n x) (f (n + 1) x) ≤ ε n := by
    have hnot := hN₁ n ((le_max_left _ _).trans hn)
    have hxspan := hN₂ n ((le_max_right _ _).trans hn)
    exact not_lt.mp (fun hlt ↦ hnot ⟨hlt, hxspan⟩)
  let d : ℕ → ℝ := fun n ↦ if N ≤ n then ε n else dist (f n x) (f (n + 1) x)
  have hd : Summable d := by
    apply hε.congr_atTop
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [d, if_pos hn]
  have hcauchy : CauchySeq (fun n ↦ f n x) := by
    apply cauchySeq_of_dist_le_of_summable d _ hd
    intro n
    by_cases hn : N ≤ n
    · simpa only [d, if_pos hn] using hdist n hn
    · simp only [d, if_neg hn, Nat.succ_eq_add_one]
      exact le_rfl
  exact hcauchy.tendsto_limUnder

end MeasureTheory
