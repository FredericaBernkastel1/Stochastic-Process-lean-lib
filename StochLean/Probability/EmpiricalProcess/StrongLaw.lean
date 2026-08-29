/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.CDF
public import Mathlib.Probability.StrongLaw

/-!
# Pointwise strong law for empirical cumulative distribution functions

For every fixed threshold, the empirical CDF of pairwise independent identically distributed
real random variables converges almost surely to the corresponding population probability. This is
the pointwise probabilistic input to the Glivenko–Cantelli argument; uniform convergence over all
thresholds is deliberately a separate theorem obligation.
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

end

end ProbabilityTheory
