/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance

/-!
# Quadratic variation and predictable bracket in discrete time

The pathwise quadratic variation `[M]` and the predictable bracket `⟨M⟩` are deliberately
different definitions.  The latter is the Doob predictable part (compensator) of the former.
-/

@[expose] public section

open scoped BigOperators ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Pathwise quadratic variation of a real-valued discrete process. -/
def pathwiseQuadraticVariation (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω) ^ 2

theorem pathwiseQuadraticVariation_eq_sum (M : ℕ → Ω → ℝ) (n : ℕ) :
    pathwiseQuadraticVariation M n =
      ∑ k ∈ Finset.range n, (M (k + 1) - M k) ^ 2 := by
  ext ω
  simp [pathwiseQuadraticVariation]

@[simp]
theorem pathwiseQuadraticVariation_zero (M : ℕ → Ω → ℝ) :
    pathwiseQuadraticVariation M 0 = 0 := by
  ext ω
  simp [pathwiseQuadraticVariation]

theorem pathwiseQuadraticVariation_succ (M : ℕ → Ω → ℝ) (n : ℕ) :
    pathwiseQuadraticVariation M (n + 1) =
      pathwiseQuadraticVariation M n + (M (n + 1) - M n) ^ 2 := by
  ext ω
  simp [pathwiseQuadraticVariation, Finset.sum_range_succ]

/-- The predictable bracket, defined as the Doob compensator of pathwise quadratic variation. -/
noncomputable def predictableQuadraticVariation (M : ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  predictablePart (pathwiseQuadraticVariation M) 𝓕 μ

@[simp]
theorem predictableQuadraticVariation_zero (M : ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) :
    predictableQuadraticVariation M 𝓕 μ 0 = 0 := by
  simp [predictableQuadraticVariation]

theorem predictableQuadraticVariation_succ (M : ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) (n : ℕ) :
    predictableQuadraticVariation M 𝓕 μ (n + 1) =
      predictableQuadraticVariation M 𝓕 μ n +
        μ[(M (n + 1) - M n) ^ 2 | 𝓕 n] := by
  rw [predictableQuadraticVariation, predictablePart_add_one,
    pathwiseQuadraticVariation_succ]
  congr 2
  simp

theorem stronglyAdapted_pathwiseQuadraticVariation {M : ℕ → Ω → ℝ}
    {𝓕 : Filtration ℕ mΩ} (hM : StronglyAdapted 𝓕 M) :
    StronglyAdapted 𝓕 (pathwiseQuadraticVariation M) := by
  intro n
  rw [pathwiseQuadraticVariation_eq_sum]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact (((hM (k + 1)).mono (𝓕.mono (Nat.succ_le_of_lt hk))).sub
    ((hM k).mono (𝓕.mono hk.le))).pow 2

theorem integrable_pathwiseQuadraticVariation {M : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    Integrable (pathwiseQuadraticVariation M n) μ := by
  rw [pathwiseQuadraticVariation_eq_sum]
  exact integrable_finsetSum' _ fun k _ => hΔ k

theorem integrable_predictableQuadraticVariation {M : ℕ → Ω → ℝ}
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    (_hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    Integrable (predictableQuadraticVariation M 𝓕 μ n) μ := by
  unfold predictableQuadraticVariation predictablePart
  exact integrable_finsetSum' _ fun k _ => integrable_condExp

/-- The predictable bracket is predictable; in particular its `(n+1)` section only uses
information available at time `n`. -/
theorem isStronglyPredictable_predictableQuadraticVariation
    (M : ℕ → Ω → ℝ) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) :
    IsStronglyPredictable 𝓕 (predictableQuadraticVariation M 𝓕 μ) := by
  exact isPredictable_predictablePart

/-- Pathwise quadratic variation minus its bracket is a martingale. -/
theorem martingale_pathwiseQuadraticVariation_sub_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [SigmaFiniteFiltration μ 𝓕] (hM : StronglyAdapted 𝓕 M)
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) :
    Martingale (pathwiseQuadraticVariation M - predictableQuadraticVariation M 𝓕 μ) 𝓕 μ := by
  change Martingale (martingalePart (pathwiseQuadraticVariation M) 𝓕 μ) 𝓕 μ
  exact martingale_martingalePart (stronglyAdapted_pathwiseQuadraticVariation hM)
    (integrable_pathwiseQuadraticVariation hΔ)

/-- The bracket is the unique integrable predictable process starting from zero whose subtraction
from pathwise quadratic variation is a martingale. -/
theorem predictableQuadraticVariation_unique
    {M A : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [SigmaFiniteFiltration μ 𝓕]
    (hcomp : Martingale (pathwiseQuadraticVariation M - A) 𝓕 μ)
    (hA : StronglyAdapted 𝓕 fun n => A (n + 1)) (hA_zero : A 0 = 0)
    (hA_int : ∀ n, Integrable (A n) μ) (n : ℕ) :
    predictableQuadraticVariation M 𝓕 μ n =ᵐ[μ] A n := by
  have h := predictablePart_add_ae_eq hcomp hA hA_zero hA_int n
  have heq : (pathwiseQuadraticVariation M - A) + A = pathwiseQuadraticVariation M := by
    ext k ω
    simp
  rw [heq] at h
  exact h

/-- Pathwise and predictable quadratic variation have the same expectation at every time. -/
theorem integral_pathwiseQuadraticVariation_eq_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [SigmaFiniteFiltration μ 𝓕] (hM : StronglyAdapted 𝓕 M)
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  have hmart :=
    martingale_pathwiseQuadraticVariation_sub_predictableQuadraticVariation hM hΔ
  have hzero := hmart.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, Pi.sub_apply,
    pathwiseQuadraticVariation_zero, predictableQuadraticVariation_zero, Pi.zero_apply,
    sub_self, integral_zero] at hzero
  rw [integral_sub (integrable_pathwiseQuadraticVariation hΔ n)
    (integrable_predictableQuadraticVariation hΔ n)] at hzero
  linarith

/-- The predictable bracket has almost surely nondecreasing sample paths. -/
theorem monotone_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕] (hM : StronglyAdapted 𝓕 M)
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) :
    ∀ᵐ ω ∂μ, Monotone (predictableQuadraticVariation M 𝓕 μ · ω) := by
  have hqv : Submartingale (pathwiseQuadraticVariation M) 𝓕 μ := by
    refine submartingale_of_condExp_sub_nonneg_nat
      (stronglyAdapted_pathwiseQuadraticVariation hM)
      (integrable_pathwiseQuadraticVariation hΔ) fun n => ?_
    rw [pathwiseQuadraticVariation_succ]
    simp only [add_sub_cancel_left]
    exact condExp_nonneg (ae_of_all μ fun ω => sq_nonneg (M (n + 1) ω - M n ω))
  simpa only [predictableQuadraticVariation] using hqv.monotone_predictablePart

/-- The square of a process minus its pathwise quadratic variation. Its increments are the
martingale-transform terms `2 Mₙ (Mₙ₊₁ - Mₙ)`. -/
def squareMinusPathwiseQuadraticVariation (M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n => M n ^ 2 - pathwiseQuadraticVariation M n

/-- For a square-integrable martingale, `M² - [M]` is a martingale. -/
theorem Martingale.square_sub_pathwiseQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (squareMinusPathwiseQuadraticVariation M) 𝓕 μ := by
  have hΔ_two : ∀ n, MemLp (M (n + 1) - M n) 2 μ :=
    fun n => (hM_two (n + 1)).sub (hM_two n)
  have hΔ_sq : ∀ n, Integrable ((M (n + 1) - M n) ^ 2) μ :=
    fun n => (hΔ_two n).integrable_sq
  have hadp : StronglyAdapted 𝓕 (squareMinusPathwiseQuadraticVariation M) := by
    intro n
    exact (hM.stronglyMeasurable n).pow 2 |>.sub
      (stronglyAdapted_pathwiseQuadraticVariation hM.stronglyAdapted n)
  have hint : ∀ n, Integrable (squareMinusPathwiseQuadraticVariation M n) μ := by
    intro n
    exact (hM_two n).integrable_sq.sub (integrable_pathwiseQuadraticVariation hΔ_sq n)
  refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun n => ?_
  have hdiff : squareMinusPathwiseQuadraticVariation M (n + 1) -
      squareMinusPathwiseQuadraticVariation M n =
        (2 : ℝ) • (M n * (M (n + 1) - M n)) := by
    ext ω
    simp [squareMinusPathwiseQuadraticVariation, pathwiseQuadraticVariation,
      Finset.sum_range_succ, smul_eq_mul]
    ring
  rw [hdiff]
  calc
    μ[(2 : ℝ) • (M n * (M (n + 1) - M n)) | 𝓕 n] =ᵐ[μ]
        (2 : ℝ) • μ[M n * (M (n + 1) - M n) | 𝓕 n] :=
      condExp_smul (2 : ℝ) _ _
    _ =ᵐ[μ] (2 : ℝ) • (M n * μ[M (n + 1) - M n | 𝓕 n]) := by
      have hpull := condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable n)
        ((hM_two n).integrable_mul (hΔ_two n))
        ((hM.integrable (n + 1)).sub (hM.integrable n))
      filter_upwards [hpull] with ω hω
      simp [smul_eq_mul, hω]
    _ =ᵐ[μ] 0 := by
      have hzero : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] 0 := by
        calc
          μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ]
              μ[M (n + 1) | 𝓕 n] - μ[M n | 𝓕 n] :=
            condExp_sub (hM.integrable (n + 1)) (hM.integrable n) _
          _ =ᵐ[μ] M n - M n :=
            (hM.condExp_ae_eq n.le_succ).sub (hM.condExp_ae_eq le_rfl)
          _ =ᵐ[μ] 0 := by simp
      filter_upwards [hzero] with ω hω
      simp [hω]

/-- For a square-integrable martingale, `M² - ⟨M⟩` is a martingale. -/
theorem Martingale.square_sub_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (fun n => M n ^ 2 - predictableQuadraticVariation M 𝓕 μ n) 𝓕 μ := by
  have hΔ_sq : ∀ n, Integrable ((M (n + 1) - M n) ^ 2) μ :=
    fun n => ((hM_two (n + 1)).sub (hM_two n)).integrable_sq
  have hsum := hM.square_sub_pathwiseQuadraticVariation hM_two |>.add
    (martingale_pathwiseQuadraticVariation_sub_predictableQuadraticVariation
      hM.stronglyAdapted hΔ_sq)
  have heq : (fun n => M n ^ 2 - predictableQuadraticVariation M 𝓕 μ n) =
      squareMinusPathwiseQuadraticVariation M +
        (pathwiseQuadraticVariation M - predictableQuadraticVariation M 𝓕 μ) := by
    ext n ω
    simp [squareMinusPathwiseQuadraticVariation]
  rw [heq]
  exact hsum

/-- Variance/bracket identity for a square-integrable martingale starting from zero. -/
theorem Martingale.integral_sq_eq_integral_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    (hM_zero : M 0 = 0) (n : ℕ) :
    ∫ ω, (M n ω) ^ 2 ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  have hmart := hM.square_sub_predictableQuadraticVariation hM_two
  have hzero := hmart.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  have hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ :=
    fun k => ((hM_two (k + 1)).sub (hM_two k)).integrable_sq
  simp only [Measure.restrict_univ,
    predictableQuadraticVariation_zero, sub_zero] at hzero
  rw [hM_zero] at hzero
  change (∫ _ω, (0 : ℝ) ^ 2 ∂μ) =
    ∫ ω, M n ω ^ 2 - predictableQuadraticVariation M 𝓕 μ n ω ∂μ at hzero
  rw [integral_sub (hM_two n).integrable_sq
    (integrable_predictableQuadraticVariation hΔ n)] at hzero
  have hz : (∫ _ω, (0 : ℝ) ^ 2 ∂μ) = 0 := by simp
  rw [hz] at hzero
  exact sub_eq_zero.mp hzero.symm

/-- Klenke's bracket identity without normalizing the martingale at time zero. -/
theorem Martingale.integral_sub_initial_sq_eq_integral_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  let N : ℕ → Ω → ℝ := fun k => M k - M 0
  have hconst : Martingale (fun _ : ℕ => M 0) 𝓕 μ :=
    martingale_const_fun 𝓕 μ (hM.stronglyMeasurable 0) (hM.integrable 0)
  have hN : Martingale N 𝓕 μ := by
    change Martingale (M - fun _ : ℕ => M 0) 𝓕 μ
    exact hM.sub hconst
  have hN_two : ∀ k, MemLp (N k) 2 μ := fun k => (hM_two k).sub (hM_two 0)
  have hN_zero : N 0 = 0 := by
    ext ω
    simp [N]
  have hqv : pathwiseQuadraticVariation N = pathwiseQuadraticVariation M := by
    ext k ω
    simp only [pathwiseQuadraticVariation, N]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    change (M (j + 1) ω - M 0 ω) - (M j ω - M 0 ω) =
      M (j + 1) ω - M j ω
    ring
  have hbr : predictableQuadraticVariation N 𝓕 μ =
      predictableQuadraticVariation M 𝓕 μ := by
    simp only [predictableQuadraticVariation, hqv]
  have h := hN.integral_sq_eq_integral_predictableQuadraticVariation hN_two hN_zero n
  rw [hbr] at h
  simpa only [N, Pi.sub_apply] using h

/-- Variance is the expected predictable bracket when the initial value is deterministic. -/
theorem Martingale.variance_eq_integral_predictableQuadraticVariation
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    {c : ℝ} (hM_zero : M 0 = fun _ => c) (n : ℕ) :
    Var[M n; μ] = ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  have hmean := hM.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hmean
  rw [hM_zero] at hmean
  simp only [integral_const] at hmean
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hmean
  rw [ProbabilityTheory.variance_eq_integral
    (hM_two n).aestronglyMeasurable.aemeasurable, ← hmean]
  have h := hM.integral_sub_initial_sq_eq_integral_predictableQuadraticVariation hM_two n
  rw [hM_zero] at h
  exact h

end MeasureTheory
