/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Kolmogorov's maximal inequality

The pinned Mathlib release already proves Doob's finite-horizon maximal inequality.  This module
records the exact square-submartingale specialization used for centered independent partial sums;
it does not duplicate the stopping-time proof.
-/

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {S : ℕ → Ω → ℝ}

/-- The square of a square-integrable real martingale is a submartingale. -/
theorem Martingale.sq_submartingale [IsFiniteMeasure P] [SigmaFiniteFiltration P ℱ]
    (hS : Martingale S ℱ P) (hS2 : ∀ n, MemLp (S n) 2 P) :
    Submartingale (fun n ω ↦ S n ω ^ 2) ℱ P := by
  refine ⟨(fun n ↦ (hS.stronglyAdapted n).pow 2), ?_, fun n ↦
    (memLp_two_iff_integrable_sq (hS2 n).aestronglyMeasurable).mp (hS2 n)⟩
  intro i j hij
  have hjensen := (show Even (2 : ℕ) by norm_num).convexOn_pow.map_condExp_le_univ
    (ℱ.le i) (continuous_pow 2).lowerSemicontinuous
    ((hS2 j).integrable (by norm_num))
    ((memLp_two_iff_integrable_sq (hS2 j).aestronglyMeasurable).mp (hS2 j))
  have hjensen' : (fun ω ↦ (P[S j | ℱ i] ω) ^ 2) ≤ᵐ[P]
      P[fun ω ↦ S j ω ^ 2 | ℱ i] := by
    simpa only [Function.comp_def] using hjensen
  filter_upwards [hS.condExp_ae_eq hij, hjensen'] with ω heq hle
  simpa only [heq] using hle

/-- Partial sums with the empty sum at time zero. -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ∑ i ∈ range n, X i

@[simp]
theorem partialSum_apply (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum X n ω = ∑ i ∈ range n, X i ω := by
  simp [partialSum]

/-- The nonempty partial sums form a martingale for the natural filtration of an independent,
centered sequence.  At time `n` the process is `X₀ + ... + Xₙ`. -/
theorem martingale_partialSum_succ [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hXint : ∀ i, Integrable (X i) P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) :
    Martingale (fun n ↦ partialSum X (n + 1)) (Filtration.natural X hXstrong) P := by
  let ℱX := Filtration.natural X hXstrong
  have hXadapt : StronglyAdapted ℱX X := Filtration.stronglyAdapted_natural hXstrong
  have hsumAdapt : StronglyAdapted ℱX (fun n ↦ partialSum X (n + 1)) := by
    intro n
    exact Finset.stronglyMeasurable_sum (range (n + 1)) fun i hi ↦
      (hXadapt i).mono (ℱX.mono (Nat.le_of_lt_succ (mem_range.mp hi)))
  have hsumInt : ∀ n, Integrable (partialSum X (n + 1)) P := fun n ↦ by
    have h := integrable_finsetSum (range (n + 1)) fun i _ ↦ hXint i
    apply h.congr
    filter_upwards with ω
    simp [partialSum]
  apply martingale_nat hsumAdapt hsumInt
  intro n
  have hrec : partialSum X (n + 2) = partialSum X (n + 1) + X (n + 1) := by
    simp [partialSum, sum_range_succ]
  rw [hrec]
  have hadd := condExp_add (hsumInt n) (hXint (n + 1)) (ℱX n)
  have hpast := condExp_of_stronglyMeasurable (ℱX.le n) (hsumAdapt n) (hsumInt n)
  have hfuture : P[X (n + 1) | ℱX n] =ᵐ[P]
      fun _ => ∫ ω, X (n + 1) ω ∂P := by
    simpa [ℱX] using hindep.condExp_natural_ae_eq_of_lt (i := n) (j := n + 1)
      hXstrong (Nat.lt_succ_self n)
  rw [hpast] at hadd
  filter_upwards [hadd, hfuture] with ω ha hf
  rw [ha]
  simp only [Pi.add_apply]
  rw [hf, hcenter (n + 1)]
  simp

/-- A finite partial sum of square-integrable variables is square-integrable. -/
theorem memLp_partialSum {X : ℕ → Ω → ℝ} (hX2 : ∀ i, MemLp (X i) 2 P) (n : ℕ) :
    MemLp (partialSum X n) 2 P := by
  simpa only [partialSum] using memLp_finsetSum' (range n) fun i _ => hX2 i

/-- Centering is preserved by finite partial sums. -/
theorem integral_partialSum_eq_zero {X : ℕ → Ω → ℝ} (hXint : ∀ i, Integrable (X i) P)
    (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0) (n : ℕ) :
    ∫ ω, partialSum X n ω ∂P = 0 := by
  simp only [partialSum, Finset.sum_apply]
  rw [integral_finsetSum]
  · simp [hcenter]
  · exact fun i _ => hXint i

/-- Variance additivity for a finite partial sum of an independent sequence. -/
theorem variance_partialSum_eq_sum {X : ℕ → Ω → ℝ} (hX2 : ∀ i, MemLp (X i) 2 P)
    (hindep : iIndepFun X P) (n : ℕ) :
    Var[partialSum X n; P] = ∑ i ∈ range n, Var[X i; P] := by
  rw [partialSum, IndepFun.variance_sum (fun i _ => hX2 i)]
  exact fun i _ j _ hij => hindep.indepFun hij

/-- Kolmogorov's maximal bound for every process whose square is a submartingale.  In particular,
this applies to the partial sums of independent centered square-integrable random variables with
their natural filtration. -/
theorem kolmogorov_maximal_ineq_of_sq_submartingale [IsFiniteMeasure P]
    (hS : Submartingale (fun k ω ↦ S k ω ^ 2) ℱ P) (ε : ℝ≥0) (n : ℕ) :
    ε ^ 2 * P {ω |
      ((ε : ℝ) ^ 2 ≤
        (range (n + 1)).sup' nonempty_range_add_one fun k ↦ S k ω ^ 2)} ≤
      ENNReal.ofReal (∫ ω, S n ω ^ 2 ∂P) := by
  have hmax := maximal_ineq hS (fun _ _ ↦ sq_nonneg _) (ε := ε ^ 2) n
  refine hmax.trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact setIntegral_le_integral (hS.integrable n) (ae_of_all _ fun _ ↦ sq_nonneg _)

/-- **Kolmogorov's maximal inequality** for independent centered square-integrable variables.

This is the division-free form of
`P(max_{k ≤ n} |Sₖ| ≥ ε) ≤ (∑_{i ≤ n} Var Xᵢ) / ε²`; the event is written with
squares so that it is definitionally the event used by Doob's maximal inequality. -/
theorem kolmogorov_maximal_ineq [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (ε : ℝ≥0) (n : ℕ) :
    ε ^ 2 * P {ω |
      ((ε : ℝ) ^ 2 ≤ (range (n + 1)).sup' nonempty_range_add_one
        fun k => partialSum X (k + 1) ω ^ 2)} ≤
      ENNReal.ofReal (∑ i ∈ range (n + 1), Var[X i; P]) := by
  have hM := martingale_partialSum_succ hXstrong
    (fun i => (hX2 i).integrable (by norm_num)) hcenter hindep
  have hsub := ProbabilityTheory.Martingale.sq_submartingale hM
    fun n => memLp_partialSum hX2 (n + 1)
  refine (kolmogorov_maximal_ineq_of_sq_submartingale hsub ε n).trans_eq ?_
  congr 1
  have hmean := integral_partialSum_eq_zero
    (fun i => (hX2 i).integrable (by norm_num)) hcenter (n + 1)
  calc
    ∫ ω, partialSum X (n + 1) ω ^ 2 ∂P = Var[partialSum X (n + 1); P] := by
      rw [variance_eq_integral (memLp_partialSum hX2 (n + 1)).aemeasurable, hmean]
      simp only [sub_zero]
    _ = ∑ i ∈ range (n + 1), Var[X i; P] :=
      variance_partialSum_eq_sum hX2 hindep (n + 1)

/-- The customary quotient form of `kolmogorov_maximal_ineq`. -/
theorem kolmogorov_maximal_ineq_div [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (ε : ℝ≥0) (hε : ε ≠ 0) (n : ℕ) :
    P {ω | ((ε : ℝ) ^ 2 ≤ (range (n + 1)).sup' nonempty_range_add_one
      fun k => partialSum X (k + 1) ω ^ 2)} ≤
      ENNReal.ofReal (∑ i ∈ range (n + 1), Var[X i; P]) / ε ^ 2 := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hε)))
    (Or.inl (by simp))).2
  simpa only [mul_comm] using kolmogorov_maximal_ineq hXstrong hX2 hcenter hindep ε n

end ProbabilityTheory
