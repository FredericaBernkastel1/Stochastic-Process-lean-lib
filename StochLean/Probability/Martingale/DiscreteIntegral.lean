/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Discrete stochastic integrals

This file gives a named API for the discrete predictable transform

`(H · X) n = ∑ k ∈ range n, H (k + 1) • (X (k + 1) - X k)`.

The `k + 1` convention is deliberate: predictability says that `H (k + 1)` is
measurable with respect to the information available at time `k`.
-/

@[expose] public section

open scoped BigOperators

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}

/-- The discrete stochastic integral (predictable transform), with the integrand indexed so that
`H (k + 1)` multiplies the increment from time `k` to time `k + 1`. -/
def discreteStochasticIntegral [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ k ∈ Finset.range n, H (k + 1) ω • (X (k + 1) ω - X k ω)

theorem discreteStochasticIntegral_eq_sum [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral H X n =
      ∑ k ∈ Finset.range n, H (k + 1) • (X (k + 1) - X k) := by
  ext ω
  simp [discreteStochasticIntegral]

@[simp]
theorem discreteStochasticIntegral_zero [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) :
    discreteStochasticIntegral H X 0 = 0 := by
  ext ω
  simp [discreteStochasticIntegral]

theorem discreteStochasticIntegral_succ [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral H X (n + 1) =
      discreteStochasticIntegral H X n + H (n + 1) • (X (n + 1) - X n) := by
  ext ω
  simp [discreteStochasticIntegral, Finset.sum_range_succ]

@[simp]
theorem discreteStochasticIntegral_zero_integrand [AddCommGroup E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral (0 : ℕ → Ω → ℝ) X n = 0 := by
  ext ω
  simp [discreteStochasticIntegral]

theorem discreteStochasticIntegral_add [AddCommGroup E] [Module ℝ E]
    (H K : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral (H + K) X n =
      discreteStochasticIntegral H X n + discreteStochasticIntegral K X n := by
  ext ω
  simp [discreteStochasticIntegral, add_smul, Finset.sum_add_distrib]

theorem discreteStochasticIntegral_smul [AddCommGroup E] [Module ℝ E]
    (c : ℝ) (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral (c • H) X n =
      c • discreteStochasticIntegral H X n := by
  ext ω
  simp [discreteStochasticIntegral, Finset.smul_sum, smul_smul]

@[simp]
theorem discreteStochasticIntegral_one [AddCommGroup E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral (1 : ℕ → Ω → ℝ) X n = X n - X 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [discreteStochasticIntegral_succ, ih]
      simp

section Martingale

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → ℝ} {X : ℕ → Ω → E}

/-- A sectionwise essentially bounded predictable transform of a martingale is a martingale.

The bound may depend on the time section. This is strictly weaker than requiring one uniform
bound for the whole process, and is sufficient because each integral is a finite sum. -/
theorem Martingale.discreteStochasticIntegral [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H)
    (hH_bdd : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖H n ω‖ ≤ C) :
    Martingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by
  choose C hC using hH_bdd
  have hint : ∀ n, Integrable (MeasureTheory.discreteStochasticIntegral H X n) μ := by
    intro n
    rw [MeasureTheory.discreteStochasticIntegral_eq_sum]
    exact integrable_finsetSum' _ fun k _ => Integrable.bdd_smul
      ((hX.integrable (k + 1)).sub (hX.integrable k)) (C (k + 1))
      ((hH.measurable_add_one k).mono (𝓕.le k)).aestronglyMeasurable (hC (k + 1))
  have hadp : StronglyAdapted 𝓕 (MeasureTheory.discreteStochasticIntegral H X) := by
    intro n
    rw [MeasureTheory.discreteStochasticIntegral_eq_sum]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    rw [Finset.mem_range] at hk
    exact ((hH.measurable_add_one k).mono (𝓕.mono hk.le)).smul
      (((hX.stronglyMeasurable (k + 1)).mono (𝓕.mono (Nat.succ_le_of_lt hk))).sub
        ((hX.stronglyMeasurable k).mono (𝓕.mono hk.le)))
  refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun n => ?_
  have hdiff : MeasureTheory.discreteStochasticIntegral H X (n + 1) -
      MeasureTheory.discreteStochasticIntegral H X n =
        H (n + 1) • (X (n + 1) - X n) := by
    rw [MeasureTheory.discreteStochasticIntegral_succ]
    abel
  rw [hdiff]
  calc
    μ[H (n + 1) • (X (n + 1) - X n) | 𝓕 n] =ᵐ[μ]
        H (n + 1) • μ[X (n + 1) - X n | 𝓕 n] :=
      condExp_smul_of_aestronglyMeasurable_left
        (hH.measurable_add_one n).aestronglyMeasurable
        (((hX.integrable (n + 1)).sub (hX.integrable n)).bdd_smul (C (n + 1))
          ((hH.measurable_add_one n).mono (𝓕.le n)).aestronglyMeasurable (hC (n + 1)))
        ((hX.integrable (n + 1)).sub (hX.integrable n))
    _ =ᵐ[μ] H (n + 1) • 0 := by
      have hΔ : μ[X (n + 1) - X n | 𝓕 n] =ᵐ[μ] 0 := by
        calc
          μ[X (n + 1) - X n | 𝓕 n] =ᵐ[μ]
              μ[X (n + 1) | 𝓕 n] - μ[X n | 𝓕 n] :=
            condExp_sub (hX.integrable (n + 1)) (hX.integrable n) _
          _ =ᵐ[μ] X n - X n :=
            (hX.condExp_ae_eq n.le_succ).sub (hX.condExp_ae_eq le_rfl)
          _ =ᵐ[μ] 0 := by simp
      filter_upwards [hΔ] with ω hω
      simp [hω]
    _ = 0 := by simp

/-- A nonnegative, uniformly bounded predictable transform of a submartingale is a
submartingale. This is the named StochLean wrapper around Mathlib's sum theorem. -/
theorem Submartingale.discreteStochasticIntegral [PartialOrder E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsFiniteMeasure μ]
    (hX : Submartingale X 𝓕 μ) (hH : IsStronglyPredictable 𝓕 H) {R : ℝ}
    (hH_bdd : ∀ n ω, H n ω ≤ R) (hH_nonneg : ∀ n ω, 0 ≤ H n ω) :
    Submartingale (MeasureTheory.discreteStochasticIntegral H X) 𝓕 μ := by
  let hS := hX.sum_smul_sub' (fun n => hH.measurable_add_one n) hH_bdd hH_nonneg
  apply hS.congr
  · intro n
    rw [MeasureTheory.discreteStochasticIntegral_eq_sum]
    exact hS.stronglyAdapted n
  · intro n
    rw [MeasureTheory.discreteStochasticIntegral_eq_sum]

end Martingale

end MeasureTheory
