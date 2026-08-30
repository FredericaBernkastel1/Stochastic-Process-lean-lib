/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.BorelCantelli
public import Mathlib.Probability.Martingale.Convergence
public import StochLean.Probability.Martingale.QuadraticVariation

/-!
# Stable adapters for Mathlib's discrete martingale calculus

These declarations give the project stable entry points while keeping Mathlib's implementations
canonical. They are intentionally proofs by direct reuse, not duplicate developments.
-/

@[expose] public section

open TopologicalSpace Filter
open scoped MeasureTheory ENNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Stable project entry point for the algebraic identity in Doob's decomposition. -/
theorem doobDecomposition [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → Ω → E) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) :
    martingalePart f 𝓕 μ + predictablePart f 𝓕 μ = f :=
  martingalePart_add_predictablePart 𝓕 μ f

/-- Stable project entry point for bounded optional sampling. The upper stopping time is genuinely
pointwise bounded; this theorem does not use `untopA` to manufacture a finite value. -/
theorem Martingale.boundedOptionalSampling
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℕ → Ω → E} {𝓕 : Filtration ℕ mΩ} {τ σ : Ω → ℕ∞}
    (hf : Martingale f 𝓕 μ) (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    {N : ℕ} (hτ_le : ∀ ω, τ ω ≤ N) [SigmaFiniteFiltration μ 𝓕]
    [SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    stoppedValue f (fun ω => min (σ ω) (τ ω)) =ᵐ[μ]
      μ[stoppedValue f τ | hσ.measurableSpace] :=
  hf.stoppedValue_min_ae_eq_condExp hτ hσ hτ_le

/-- Stopping preserves discrete predictability.  The proof uses the exact `n+1`/`n` convention:
the event that the process has not stopped before the next increment is `𝓕 n`-measurable. -/
theorem IsStronglyPredictable.stoppedProcess_nat
    {A : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {τ : Ω → ℕ∞}
    (hA : IsStronglyPredictable 𝓕 A) (hτ : IsStoppingTime 𝓕 τ) :
    IsStronglyPredictable 𝓕 (MeasureTheory.stoppedProcess A τ) := by
  apply IsStronglyPredictable.of_measurable_add_one
  · have hzero : MeasureTheory.stoppedProcess A τ 0 = A 0 := by
      ext ω
      exact MeasureTheory.stoppedProcess_eq_of_le bot_le
    rw [hzero]
    exact hA.stronglyAdapted 0
  · intro n
    rw [MeasureTheory.stoppedProcess_eq]
    apply StronglyMeasurable.add
    · apply StronglyMeasurable.indicator
        (hA.measurable_add_one n)
      have heq : {ω | ((n + 1 : ℕ) : ℕ∞) ≤ τ ω} =
          {ω | τ ω ≤ (n : ℕ∞)}ᶜ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        change (n : ℕ∞) + 1 ≤ τ ω ↔ ¬τ ω ≤ (n : ℕ∞)
        rw [ENat.natCast_add_one_le_iff]
        exact lt_iff_not_ge
      rw [heq]
      exact (hτ.measurableSet_le n).compl
    · refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp hi
      apply StronglyMeasurable.indicator
        ((hA.stronglyAdapted i).mono (𝓕.mono hin))
      exact 𝓕.mono hin _ (hτ.measurableSet_eq_of_countable i)

/-- Stopping a discrete martingale at an arbitrary (possibly infinite) stopping time preserves the
martingale property of the stopped process.  This is derived from Mathlib's submartingale theorem
and does not assign a terminal value to the original process at `∞`. -/
theorem Martingale.stoppedProcess
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {τ : Ω → ℕ∞}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hf : Martingale f 𝓕 μ) (hτ : IsStoppingTime 𝓕 τ) :
    Martingale (MeasureTheory.stoppedProcess f τ) 𝓕 μ := by
  rw [martingale_iff]
  constructor
  · have h := hf.neg.submartingale.stoppedProcess hτ |>.neg
    have heq : -MeasureTheory.stoppedProcess (-f) τ =
        MeasureTheory.stoppedProcess f τ := by
      ext n ω
      simp [MeasureTheory.stoppedProcess]
    rw [heq] at h
    exact h
  · exact hf.submartingale.stoppedProcess hτ

/-- Predictable quadratic variation commutes, up to the unavoidable a.e. equality, with stopping:
`⟨M^τ⟩ = ⟨M⟩^τ`.  The stopping time may take the value `∞`; only finite-time stopped-process
sections occur in the statement. -/
theorem Martingale.predictableQuadraticVariation_stoppedProcess_ae_eq
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {τ : Ω → ℕ∞}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    predictableQuadraticVariation (MeasureTheory.stoppedProcess M τ) 𝓕 μ n =ᵐ[μ]
      MeasureTheory.stoppedProcess (predictableQuadraticVariation M 𝓕 μ) τ n := by
  let S : ℕ → Ω → ℝ := MeasureTheory.stoppedProcess M τ
  let B : ℕ → Ω → ℝ := predictableQuadraticVariation M 𝓕 μ
  let A : ℕ → Ω → ℝ := MeasureTheory.stoppedProcess B τ
  have hS : Martingale S 𝓕 μ := hM.stoppedProcess hτ
  have hS_two : ∀ k, MemLp (S k) 2 μ := fun k =>
    memLp_stoppedProcess hτ hM_two k
  have hA_pred : IsStronglyPredictable 𝓕 A :=
    (isStronglyPredictable_predictableQuadraticVariation M 𝓕 μ).stoppedProcess_nat hτ
  have hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ := fun k =>
    ((hM_two (k + 1)).sub (hM_two k)).integrable_sq
  have hB_int : ∀ k, Integrable (B k) μ := fun k =>
    integrable_predictableQuadraticVariation hΔ k
  have hA_int : ∀ k, Integrable (A k) μ := fun k =>
    integrable_stoppedProcess hτ hB_int k
  have hA_zero : A 0 = 0 := by
    have hst0 : A 0 = B 0 := by
      ext ω
      exact MeasureTheory.stoppedProcess_eq_of_le bot_le
    rw [hst0]
    exact predictableQuadraticVariation_zero M 𝓕 μ
  have horig := hM.square_sub_predictableQuadraticVariation hM_two
  have hstop := horig.stoppedProcess hτ
  have hstop_eq : MeasureTheory.stoppedProcess
      (fun k => M k ^ 2 - predictableQuadraticVariation M 𝓕 μ k) τ =
      fun k => S k ^ 2 - A k := by
    ext k ω
    rfl
  rw [hstop_eq] at hstop
  have hpath := hS.square_sub_pathwiseQuadraticVariation hS_two
  have hdiff := hstop.sub hpath
  have heq : (fun k => S k ^ 2 - A k) - squareMinusPathwiseQuadraticVariation S =
      pathwiseQuadraticVariation S - A := by
    ext k ω
    simp [squareMinusPathwiseQuadraticVariation]
  rw [heq] at hdiff
  exact predictableQuadraticVariation_unique hdiff
    (fun k => hA_pred.measurable_add_one k) hA_zero hA_int n

/-- Stable entry point for a.e. and `L¹` convergence of a uniformly integrable martingale. -/
theorem Martingale.uniformIntegrable_tendsto_limitProcess
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ]
    [SigmaFiniteFiltration μ 𝓕] (hf : Martingale f 𝓕 μ)
    (hUI : UniformIntegrable f 1 μ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (𝓕.limitProcess f μ ω))) ∧
      Tendsto (fun n => eLpNorm (f n - 𝓕.limitProcess f μ) 1 μ) atTop (𝓝 0) :=
  ⟨hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hUI,
    hf.submartingale.tendsto_eLpNorm_one_limitProcess hUI⟩

/-- Stable entry point for Levy's conditional Borel-Cantelli theorem. -/
theorem conditionalBorelCantelli
    {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ] {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[𝓕 n] (s n)) :
    ∀ᵐ ω ∂μ, ω ∈ limsup s atTop ↔
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ) | 𝓕 k]) ω) atTop atTop :=
  ae_mem_limsup_atTop_iff μ hs

end MeasureTheory
