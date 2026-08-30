/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Exchangeability.EmpiricalMeasure
public import StochLean.Probability.EmpiricalProcess.StrongLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence of empirical probability measures on the real line

This file consumes the empirical measure and empirical CDF objects from the earlier milestones.
The proof uses Mathlib's convergence-determining rational open-interval π-system; it does not
introduce another CDF or another weak-convergence predicate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

noncomputable section

/-- The canonical empirical measure bundled as a `ProbabilityMeasure`. -/
def empiricalProbabilityMeasurePM {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ProbabilityMeasure ℝ :=
  ⟨empiricalProbabilityMeasure X n ω, inferInstance⟩

/-- The law of one real random variable bundled as a `ProbabilityMeasure`. -/
def lawProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    ProbabilityMeasure ℝ :=
  ⟨P.map X, Measure.isProbabilityMeasure_map hX.aemeasurable⟩

private theorem empiricalProbabilityMeasure_real_Ioo
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) {a b : ℝ} (hab : a < b) :
    (empiricalProbabilityMeasure X n ω).real (Ioo a b) =
      empiricalCDFSequenceLt X n ω b - empiricalCDFSequence X n ω a := by
  rw [show Ioo a b = Iio b \ Iic a by ext x; simp]
  rw [measureReal_sdiff (Iic_subset_Iio.2 hab) measurableSet_Iic]
  change ((empiricalProbabilityMeasure X n ω) (Iio b)).toReal -
      ((empiricalProbabilityMeasure X n ω) (Iic a)).toReal = _
  rw [empiricalProbabilityMeasure_Iio, empiricalProbabilityMeasure_Iic]

private theorem law_measureReal_Ioo
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) {a b : ℝ} (hab : a < b) :
    P.real (X ⁻¹' Ioo a b) =
      P.real (X ⁻¹' Iio b) - P.real (X ⁻¹' Iic a) := by
  rw [show X ⁻¹' Ioo a b = X ⁻¹' Iio b \ X ⁻¹' Iic a by
    ext x
    simp [and_comm]]
  exact measureReal_sdiff (preimage_mono (Iic_subset_Iio.2 hab))
    (measurableSet_Iic.preimage hX)

/-- The empirical probability measures of pairwise-independent identically distributed real
observations converge weakly to their common law on one probability-one event. -/
theorem tendsto_empiricalProbabilityMeasurePM_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empiricalProbabilityMeasurePM X n ω) atTop
      (𝓝 (lawProbabilityMeasure P (X 0) (hX 0))) := by
  filter_upwards [tendsto_empiricalCDFSequence_all_ae P X hX hindep hident,
    tendsto_empiricalCDFSequenceLt_all_ae P X hX hindep hident] with ω hIic hIio
  apply Real.isPiSystem_Ioo_rat.tendsto_probabilityMeasure_of_tendsto_of_mem
  · intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact measurableSet_Ioo
  · intro u hu x hx
    obtain ⟨s, hs, hxs, hsu⟩ :=
      Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open hx hu
    exact ⟨s, hs, Real.isTopologicalBasis_Ioo_rat.mem_nhds_iff.2
      ⟨s, hs, hxs, Subset.rfl⟩, hsu⟩
  · intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨a, b, hab, rfl⟩ := hs
    have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
    have ht := (hIio (b : ℝ)).sub (hIic (a : ℝ))
    have hreal : Tendsto
        (fun n ↦ (empiricalProbabilityMeasure X n ω).real (Ioo (a : ℝ) (b : ℝ)))
        atTop (𝓝 (P.real ((X 0) ⁻¹' Ioo (a : ℝ) (b : ℝ)))) := by
      rw [law_measureReal_Ioo P (X 0) (hX 0) (by exact_mod_cast hab)]
      simpa only [empiricalProbabilityMeasure_real_Ioo X _ ω hab'] using ht
    have hnn := tendsto_real_toNNReal hreal
    simpa only [empiricalProbabilityMeasurePM, lawProbabilityMeasure,
      ProbabilityMeasure.mk_apply, Measure.real, ENNReal.toNNReal_toReal_eq,
      Measure.map_apply (hX 0) measurableSet_Ioo] using hnn

end

end ProbabilityTheory
