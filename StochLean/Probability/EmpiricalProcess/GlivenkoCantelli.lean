/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.StrongLaw
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Glivenko–Cantelli theorem

This file proves compact bracketing theorems for monotone functions. Tracking both the function
values and their strict left limits handles jumps, and yields the full Glivenko–Cantelli theorem
for arbitrary real laws, including laws with atoms.
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

/-- On a compact interval, pointwise convergence at function values and strict left limits is
uniform for monotone right-continuous limits. The companion `L n t` supplies the strict-left value
of the approximant at `t`; the one-sided comparison `F n s ≤ L n t` for `s < t` is all that the
bracketing proof needs. -/
theorem tendstoUniformlyOn_Icc_of_monotone_of_leftLimits
    {F L : ℕ → ℝ → ℝ} {f : StieltjesFunction ℝ} {a b : ℝ}
    (hF : ∀ n, Monotone (F n))
    (hFL : ∀ n ⦃s t : ℝ⦄, s < t → F n s ≤ L n t)
    (hpoint : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    (hleftPoint : ∀ x, Tendsto (fun n ↦ L n x) atTop
      (nhds (Function.leftLim f x))) :
    TendstoUniformlyOn F f atTop (Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hη : 0 < ε / 8 := by linarith
  have hlocal : ∀ c : Icc a b, ∃ δ : ℝ, 0 < δ ∧
      (∀ y : ℝ, dist y c < δ → y < c →
        dist (f y) (Function.leftLim f c) < ε / 8) ∧
      (∀ y : ℝ, dist y c < δ → (c : ℝ) ≤ y → dist (f y) (f c) < ε / 8) := by
    intro c
    have hl := (Metric.tendsto_nhds.1 (f.mono.tendsto_leftLim (c : ℝ))) (ε / 8) hη
    have hlmem : {y : ℝ | dist (f y) (Function.leftLim f (c : ℝ)) < ε / 8} ∈
        𝓝[<] (c : ℝ) := hl
    rw [Metric.mem_nhdsWithin_iff] at hlmem
    obtain ⟨δl, hδl, hleft⟩ := hlmem
    have hr := (Metric.tendsto_nhds.1 (f.right_continuous (c : ℝ))) (ε / 8) hη
    have hrmem : {y : ℝ | dist (f y) (f (c : ℝ)) < ε / 8} ∈
        𝓝[Set.Ici (c : ℝ)] (c : ℝ) := hr
    rw [Metric.mem_nhdsWithin_iff] at hrmem
    obtain ⟨δr, hδr, hright⟩ := hrmem
    refine ⟨min δl δr, lt_min hδl hδr, ?_, ?_⟩
    · intro y hy hyc
      exact hleft ⟨Metric.mem_ball.mpr (hy.trans_le (min_le_left _ _)), hyc⟩
    · intro y hy hcy
      exact hright ⟨Metric.mem_ball.mpr (hy.trans_le (min_le_right _ _)), hcy⟩
  choose δ hδ hleft hright using hlocal
  let U : Icc a b → Set ℝ := fun c ↦ Metric.ball (c : ℝ) (δ c / 2)
  have hcover : Icc a b ⊆ ⋃ c, U c := by
    intro x hx
    apply mem_iUnion.2
    refine ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hδ ⟨x, hx⟩])⟩
  obtain ⟨s, hs⟩ :=
    isCompact_Icc.elim_finite_subcover U (fun _ ↦ Metric.isOpen_ball) hcover
  have hend : ∀ᶠ n in atTop, ∀ c ∈ s,
      dist (F n ((c : ℝ) - δ c / 2)) (f ((c : ℝ) - δ c / 2)) < ε / 8 ∧
      dist (L n (c : ℝ)) (Function.leftLim f (c : ℝ)) < ε / 8 ∧
      dist (F n (c : ℝ)) (f (c : ℝ)) < ε / 8 ∧
      dist (F n ((c : ℝ) + δ c / 2)) (f ((c : ℝ) + δ c / 2)) < ε / 8 := by
    rw [Filter.eventually_all_finset]
    intro c _
    exact ((Metric.tendsto_nhds.1 (hpoint ((c : ℝ) - δ c / 2))) (ε / 8) hη).and
      (((Metric.tendsto_nhds.1 (hleftPoint (c : ℝ))) (ε / 8) hη).and
      (((Metric.tendsto_nhds.1 (hpoint (c : ℝ))) (ε / 8) hη).and
      ((Metric.tendsto_nhds.1 (hpoint ((c : ℝ) + δ c / 2))) (ε / 8) hη)))
  filter_upwards [hend] with n hn x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hs hx)
  have hxball : dist x (c : ℝ) < δ c / 2 := hxc
  have hlδ : dist ((c : ℝ) - δ c / 2) (c : ℝ) < δ c := by
    rw [Real.dist_eq, abs_sub_comm]
    have hnon : 0 ≤ (c : ℝ) - ((c : ℝ) - δ c / 2) := by linarith [hδ c]
    rw [abs_of_nonneg hnon]
    linarith [hδ c]
  have hrδ : dist ((c : ℝ) + δ c / 2) (c : ℝ) < δ c := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg]
    · linarith [hδ c]
    · linarith [hδ c]
  have hlc : (c : ℝ) - δ c / 2 < c := by linarith [hδ c]
  have hcr : (c : ℝ) < (c : ℝ) + δ c / 2 := by linarith [hδ c]
  have hlx : (c : ℝ) - δ c / 2 < x := by
    rw [Real.dist_eq, abs_lt] at hxball
    linarith
  have hxr : x < (c : ℝ) + δ c / 2 := by
    rw [Real.dist_eq, abs_lt] at hxball
    linarith
  by_cases hxc' : x < (c : ℝ)
  · have hGl : F n ((c : ℝ) - δ c / 2) ≤ F n x := hF n hlx.le
    have hGu : F n x ≤ L n (c : ℝ) := hFL n hxc'
    have hfl := hleft c _ hlδ hlc
    have hfxl : f ((c : ℝ) - δ c / 2) ≤ f x := f.mono hlx.le
    have hfxu : f x ≤ Function.leftLim f (c : ℝ) := f.mono.le_leftLim hxc'
    rcases hn c hc with ⟨hnl, hnL, _hnc, _hnr⟩
    rw [Real.dist_eq] at hfl hnl hnL ⊢
    rw [abs_lt] at hfl hnl hnL ⊢
    constructor <;> linarith
  · have hcx : (c : ℝ) ≤ x := le_of_not_gt hxc'
    have hGl : F n (c : ℝ) ≤ F n x := hF n hcx
    have hGu : F n x ≤ F n ((c : ℝ) + δ c / 2) := hF n hxr.le
    have hfr := hright c _ hrδ hcr.le
    have hfl : f (c : ℝ) ≤ f x := f.mono hcx
    have hfu : f x ≤ f ((c : ℝ) + δ c / 2) := f.mono hxr.le
    rcases hn c hc with ⟨_hnl, _hnL, hnc, hnr⟩
    rw [Real.dist_eq] at hfr hnc hnr ⊢
    rw [abs_lt] at hfr hnc hnr ⊢
    constructor <;> linarith

/-- Global left-limit bracketing theorem for `[0,1]`-valued monotone approximants of a CDF-like
Stieltjes function. Unlike the continuous-limit theorem, this result allows arbitrary jumps. -/
theorem tendstoUniformly_of_monotone_of_leftLimits
    {F L : ℕ → ℝ → ℝ} {f : StieltjesFunction ℝ}
    (hF : ∀ n, Monotone (F n))
    (hFL : ∀ n ⦃s t : ℝ⦄, s < t → F n s ≤ L n t)
    (hF0 : ∀ n x, 0 ≤ F n x) (hF1 : ∀ n x, F n x ≤ 1)
    (hfbot : Tendsto f atBot (nhds 0)) (hftop : Tendsto f atTop (nhds 1))
    (hpoint : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    (hleftPoint : ∀ x, Tendsto (fun n ↦ L n x) atTop
      (nhds (Function.leftLim f x))) :
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
    (tendstoUniformlyOn_Icc_of_monotone_of_leftLimits
      (a := A) (b := B) hF hFL hpoint hleftPoint) ε hε
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

/-- The strict left limit of a probability CDF is the mass of the strict lower half-line. -/
theorem leftLim_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Function.leftLim (cdf μ) t = μ.real (Iio t) := by
  have hnon : 0 ≤ Function.leftLim (cdf μ) t :=
    (cdf_nonneg μ (t - 1)).trans ((monotone_cdf μ).le_leftLim (by linarith))
  have hm := StieltjesFunction.measure_Iio (cdf μ) (tendsto_cdf_atBot μ) t
  rw [measure_cdf μ] at hm
  rw [measureReal_def, hm]
  simp only [sub_zero, ENNReal.toReal_ofReal hnon]

/-- Full Glivenko–Cantelli theorem for arbitrary real laws, including discontinuous laws.
Pairwise independence suffices because the pointwise inputs use Etemadi's strong law. The strict
empirical CDF controls the left side of every population jump. -/
theorem tendstoUniformly_empiricalCDFSequence_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, TendstoUniformly (fun n t ↦ empiricalCDFSequence X n ω t)
      (cdf (Measure.map (X 0) P)) atTop := by
  let μ : Measure ℝ := Measure.map (X 0) P
  let _ : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  have hFcdf (t : ℝ) : cdf μ t = P.real ((X 0) ⁻¹' Iic t) := by
    rw [cdf_eq_real, map_measureReal_apply (hX 0) measurableSet_Iic]
  have hFleft (t : ℝ) : Function.leftLim (cdf μ) t = P.real ((X 0) ⁻¹' Iio t) := by
    rw [leftLim_cdf, map_measureReal_apply (hX 0) measurableSet_Iio]
  filter_upwards [tendsto_empiricalCDFSequence_all_ae P X hX hindep hident,
    tendsto_empiricalCDFSequenceLt_all_ae P X hX hindep hident] with ω hω hωlt
  apply tendstoUniformly_of_monotone_of_leftLimits
    (fun n ↦ monotone_empiricalCDFSequence X n ω)
    (fun n _s _t hst ↦ empiricalCDFSequence_le_lt_of_lt X n ω hst)
    (fun n t ↦ empiricalCDFSequence_nonneg X n ω t)
    (fun n t ↦ empiricalCDFSequence_le_one X n ω t)
    (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ)
  · intro t
    simpa only [hFcdf] using hω t
  · intro t
    simpa only [hFleft] using hωlt t

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
