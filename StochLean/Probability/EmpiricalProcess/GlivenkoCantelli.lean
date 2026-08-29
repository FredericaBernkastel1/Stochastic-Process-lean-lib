/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.StrongLaw
public import Mathlib.Probability.CDF
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform empirical-CDF convergence for continuous population laws

This file proves the deterministic compact bracketing theorem for monotone functions and applies
it to empirical CDFs whose population CDF is continuous. The general Glivenko–Cantelli theorem for
laws with atoms requires a further finite large-atom decomposition and remains a separate result.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped Topology

namespace ProbabilityTheory

noncomputable section

/-- On a compact real interval, pointwise convergence of monotone functions to a continuous limit
is uniform. The sequence need not be monotone in its index. -/
theorem tendstoUniformlyOn_Icc_of_monotone_of_continuous
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ n, Monotone (F n)) (hf : Continuous f)
    (hpoint : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    TendstoUniformlyOn F f atTop (Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlocal : ∀ c : Icc a b, ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, dist y c < δ → dist (f y) (f c) < ε / 6 := by
    intro c
    obtain ⟨δ, hδ, hc⟩ := (Metric.continuousAt_iff.1 hf.continuousAt) (ε / 6) (by linarith)
    exact ⟨δ, hδ, fun y hy ↦ hc hy⟩
  choose δ hδ hclose using hlocal
  let U : Icc a b → Set ℝ := fun c ↦ Metric.ball (c : ℝ) (δ c / 2)
  have hcover : Icc a b ⊆ ⋃ c, U c := by
    intro x hx
    apply mem_iUnion.2
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (by linarith [hδ ⟨x, hx⟩])
  obtain ⟨s, hs⟩ :=
    isCompact_Icc.elim_finite_subcover U (fun _ ↦ Metric.isOpen_ball) hcover
  have hend : ∀ᶠ n in atTop, ∀ c ∈ s,
      dist (F n ((c : ℝ) - δ c / 2)) (f ((c : ℝ) - δ c / 2)) < ε / 6 ∧
      dist (F n ((c : ℝ) + δ c / 2)) (f ((c : ℝ) + δ c / 2)) < ε / 6 := by
    rw [Filter.eventually_all_finset]
    intro c _
    exact ((Metric.tendsto_nhds.1 (hpoint ((c : ℝ) - δ c / 2))) (ε / 6) (by linarith)).and
      ((Metric.tendsto_nhds.1 (hpoint ((c : ℝ) + δ c / 2))) (ε / 6) (by linarith))
  filter_upwards [hend] with n hn x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hs hx)
  have hxball : dist x (c : ℝ) < δ c / 2 := hxc
  have hxcδ : dist x (c : ℝ) < δ c := hxball.trans (by linarith [hδ c])
  have hlδ : dist ((c : ℝ) - δ c / 2) (c : ℝ) < δ c := by
    rw [Real.dist_eq, abs_sub_comm]
    have hnon : 0 ≤ (c : ℝ) - ((c : ℝ) - δ c / 2) := by linarith [hδ c]
    rw [abs_of_nonneg hnon]
    linarith [hδ c]
  have hrδ : dist ((c : ℝ) + δ c / 2) (c : ℝ) < δ c := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg]
    · linarith [hδ c]
    · linarith [hδ c]
  have hlx : (c : ℝ) - δ c / 2 < x := by
    rw [Real.dist_eq, abs_lt] at hxball
    linarith
  have hxr : x < (c : ℝ) + δ c / 2 := by
    rw [Real.dist_eq, abs_lt] at hxball
    linarith
  have hGl : F n ((c : ℝ) - δ c / 2) ≤ F n x := hF n hlx.le
  have hGr : F n x ≤ F n ((c : ℝ) + δ c / 2) := hF n hxr.le
  have hfl := hclose c _ hlδ
  have hfr := hclose c _ hrδ
  have hfx := hclose c _ hxcδ
  have hnl := (hn c hc).1
  have hnr := (hn c hc).2
  rw [Real.dist_eq] at hfl hfr hfx hnl hnr ⊢
  rw [abs_lt] at hfl hfr hfx hnl hnr ⊢
  constructor <;> linarith

/-- Global version of compact monotone bracketing when the approximants take values in `[0,1]`
and the continuous limit tends to zero and one at the two ends of the real line. -/
theorem tendstoUniformly_of_monotone_of_continuous
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Monotone (F n)) (hf : Continuous f)
    (hF0 : ∀ n x, 0 ≤ F n x) (hF1 : ∀ n x, F n x ≤ 1)
    (hfbot : Tendsto f atBot (nhds 0)) (hftop : Tendsto f atTop (nhds 1))
    (hpoint : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    TendstoUniformly F f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hη : 0 < ε / 4 := by linarith
  have hbot := (Metric.tendsto_nhds.1 hfbot) (ε / 4) hη
  have htop := (Metric.tendsto_nhds.1 hftop) (ε / 4) hη
  obtain ⟨A, hA⟩ := eventually_atBot.1 hbot
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 htop
  let B := max B₀ A
  have hcompact := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_Icc_of_monotone_of_continuous
      (a := A) (b := B) hF hf hpoint) ε hε
  have hAt := (Metric.tendsto_nhds.1 (hpoint A)) (ε / 4) hη
  have hBt := (Metric.tendsto_nhds.1 (hpoint B)) (ε / 4) hη
  filter_upwards [hcompact, hAt, hBt] with n hn hAn hBn x
  by_cases hxA : x < A
  · have hfx := hA x hxA.le
    have hFA := hA A le_rfl
    have hmono := hF n hxA.le
    rw [Real.dist_eq] at hfx hFA hAn ⊢
    rw [abs_lt] at hfx hFA hAn ⊢
    constructor <;> linarith [hF0 n x]
  · by_cases hxB : B < x
    · have hfx := hB₀ x (le_trans (le_max_left _ _) hxB.le)
      have hFB := hB₀ B (le_max_left _ _)
      have hmono := hF n hxB.le
      rw [Real.dist_eq] at hfx hFB hBn ⊢
      rw [abs_lt] at hfx hFB hBn ⊢
      constructor <;> linarith [hF1 n x]
    · exact hn x ⟨le_of_not_gt hxA, le_of_not_gt hxB⟩

/-- Glivenko–Cantelli for pairwise independent identically distributed samples whose population
CDF is continuous. Convergence is uniform in the threshold on one full-measure event. -/
theorem tendstoUniformly_empiricalCDFSequence_ae_of_continuous_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hcont : Continuous (cdf (Measure.map (X 0) P))) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n t ↦ empiricalCDFSequence X n ω t)
      (cdf (Measure.map (X 0) P)) atTop := by
  let μ : Measure ℝ := Measure.map (X 0) P
  let _ : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hF (t : ℝ) : cdf μ t = P.real ((X 0) ⁻¹' Set.Iic t) := by
    rw [cdf_eq_real, map_measureReal_apply (hX 0) measurableSet_Iic]
  filter_upwards [tendsto_empiricalCDFSequence_all_ae P X hX hindep hident] with ω hω
  apply tendstoUniformly_of_monotone_of_continuous
    (fun n ↦ monotone_empiricalCDFSequence X n ω) hcont
    (fun n t ↦ empiricalCDFSequence_nonneg X n ω t)
    (fun n t ↦ empiricalCDFSequence_le_one X n ω t)
    (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ)
  intro t
  change Tendsto (fun n => empiricalCDFSequence X n ω t) atTop (𝓝 (cdf μ t))
  simpa only [hF] using hω t

end

end ProbabilityTheory
