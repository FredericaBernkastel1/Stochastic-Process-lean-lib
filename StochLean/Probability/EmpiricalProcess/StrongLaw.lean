/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.CDF
public import Mathlib.Probability.StrongLaw

import Mathlib.Probability.CDF

/-!
# Strong laws for empirical cumulative distribution functions

For every fixed threshold, the empirical CDF of pairwise independent identically distributed
real random variables converges almost surely to the corresponding population probability.
Countability of the discontinuity set of a monotone CDF upgrades the rational-threshold event to
one common full-measure event on which convergence holds at every real threshold. Uniform
convergence remains a separate deterministic bracketing step.
-/

@[expose] public section

open Filter Finset MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

noncomputable section

/-- At a fixed threshold, the empirical CDF converges almost surely to the population CDF.

Etemadi's pairwise-independent strong law from Mathlib is sufficient: apply it to the indicators of
the lower half-line `Set.Iic t`, then pass from sample size `n` to the nonempty convention `n + 1`.
-/
theorem tendsto_empiricalCDFSequence_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (t : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empiricalCDFSequence X n ω t) atTop
      (nhds (P.real ((X 0) ⁻¹' Set.Iic t))) := by
  let F : ℝ → ℝ := Set.indicator (Set.Iic t) (fun _ ↦ 1)
  let Y : ℕ → Ω → ℝ := fun i ↦ F ∘ X i
  have hF : Measurable F := (measurable_indicator_const_iff 1).2 measurableSet_Iic
  have hYint : Integrable (Y 0) P := by
    exact (integrable_const (1 : ℝ)).mono (hF.comp (hX 0)).aestronglyMeasurable (by
      filter_upwards [] with ω
      by_cases h : X 0 ω ∈ Set.Iic t <;> simp [Y, F, Set.indicator, h])
  have hYindep : Pairwise (fun i j ↦ IndepFun (Y i) (Y j) P) := fun i j hij ↦
    IndepFun.comp (hindep hij) hF hF
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i ↦
    (hident i).comp hF
  filter_upwards [strong_law_ae Y hYint hYindep hYident] with ω hω
  have hsub := hω.comp (tendsto_add_atTop_nat 1)
  have hmean : ∫ ω, Y 0 ω ∂P = P.real ((X 0) ⁻¹' Set.Iic t) := by
    rw [← MeasureTheory.integral_indicator_one (measurableSet_Iic.preimage (hX 0))]
    congr 1
  rw [hmean] at hsub
  apply Tendsto.congr' _ hsub
  filter_upwards [] with n
  rw [empiricalCDFSequence, empiricalCDF_eq_average_indicator]
  simp only [Y, Function.comp_apply, smul_eq_mul]
  congr 1
  symm
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F (X i ω)) (n + 1)

/-- The pointwise strong law holds at every rational threshold on one common full-measure event.

The countability of `ℚ` is essential here. This is the form used by the deterministic monotonicity
and approximation step in a Glivenko–Cantelli proof.
-/
theorem tendsto_empiricalCDFSequence_rat_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ q : ℚ,
      Tendsto (fun n ↦ empiricalCDFSequence X n ω (q : ℝ)) atTop
        (nhds (P.real ((X 0) ⁻¹' Set.Iic (q : ℝ)))) :=
  ae_all_iff.2 fun q ↦ tendsto_empiricalCDFSequence_ae P X hX hindep hident (q : ℝ)

/-- The empirical CDF converges pointwise at every real threshold on one common full-measure
event.

The event first intersects the strong laws at rational thresholds and at the countable set of
discontinuities of the population CDF. At every remaining (continuous) threshold, rational points
on either side and monotonicity squeeze the empirical values to the population value. -/
theorem tendsto_empiricalCDFSequence_all_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun n ↦ empiricalCDFSequence X n ω t) atTop
        (nhds (P.real ((X 0) ⁻¹' Set.Iic t))) := by
  let μ : Measure ℝ := Measure.map (X 0) P
  let _ : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hF (t : ℝ) : cdf μ t = P.real ((X 0) ⁻¹' Set.Iic t) := by
    rw [cdf_eq_real, map_measureReal_apply (hX 0) measurableSet_Iic]
  let D : Set ℝ := {t | ¬ContinuousAt (cdf μ) t}
  have hD : D.Countable := (monotone_cdf μ).countable_not_continuousAt
  let _ : Countable D := hD.to_subtype
  have hrat := tendsto_empiricalCDFSequence_rat_ae P X hX hindep hident
  have hdisc : ∀ᵐ ω ∂P, ∀ t : D,
      Tendsto (fun n ↦ empiricalCDFSequence X n ω t) atTop (nhds (cdf μ t)) := by
    rw [ae_all_iff]
    intro t
    simpa only [hF] using tendsto_empiricalCDFSequence_ae P X hX hindep hident (t : ℝ)
  filter_upwards [hrat, hdisc] with ω hωrat hωdisc
  intro t
  rw [← hF]
  by_cases ht : ContinuousAt (cdf μ) t
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.1 ht) (ε / 2) (half_pos hε)
    obtain ⟨q, hqleft, hqt⟩ := exists_rat_btwn (sub_lt_self t hδ)
    obtain ⟨r, htr, hrright⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
    have hqdist : dist (q : ℝ) t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hrdist : dist (r : ℝ) t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hFq := hclose hqdist
    have hFr := hclose hrdist
    have hqconv := (Metric.tendsto_nhds.1 (hωrat q)) (ε / 2) (half_pos hε)
    have hrconv := (Metric.tendsto_nhds.1 (hωrat r)) (ε / 2) (half_pos hε)
    rw [← hF] at hqconv hrconv
    filter_upwards [hqconv, hrconv] with n hnq hnr
    rw [Real.dist_eq] at hFq hFr hnq hnr ⊢
    have hGnq : empiricalCDFSequence X n ω (q : ℝ) ≤
        empiricalCDFSequence X n ω t :=
      monotone_empiricalCDFSequence X n ω (le_of_lt hqt)
    have hGnr : empiricalCDFSequence X n ω t ≤
        empiricalCDFSequence X n ω (r : ℝ) :=
      monotone_empiricalCDFSequence X n ω (le_of_lt htr)
    have hFqt : cdf μ (q : ℝ) ≤ cdf μ t := monotone_cdf μ (le_of_lt hqt)
    have hFtr : cdf μ t ≤ cdf μ (r : ℝ) := monotone_cdf μ (le_of_lt htr)
    rw [abs_lt] at hFq hFr hnq hnr ⊢
    constructor <;> linarith
  · exact hωdisc ⟨t, ht⟩

end

end ProbabilityTheory
