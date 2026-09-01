/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.ContinuousPowers
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Linearized roots and compound-Poisson limits

This file develops the forward implication in the root-array criterion for infinite
divisibility.  A continuous pointwise limit of the linearized characteristic functions
produces all nonnegative convolution powers through internal compound-Poisson
approximations.  In particular its unit-time law is infinitely divisible.

The definitions and theorem organization are native to StochLean; no external Lean
package is used.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

/-- Linearized characteristic-function convergence in Theorem 16.6. -/
def HasLinearizedRootLimit (ρ : ℕ → ProbabilityMeasure ℝ) (ψ : ℝ → ℂ) : Prop :=
  ContinuousAt ψ 0 ∧ ∀ t : ℝ,
    Tendsto (fun n => ((n + 1 : ℕ) : ℂ) *
      (charFun (ρ n : Measure ℝ) t - 1)) atTop (nhds (ψ t))

theorem HasLinearizedRootLimit.zero {ρ : ℕ → ProbabilityMeasure ℝ} {ψ : ℝ → ℂ}
    (h : HasLinearizedRootLimit ρ ψ) : ψ 0 = 0 := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds (ψ 0)) := by
    simpa using h.2 0
  exact tendsto_nhds_unique hzero tendsto_const_nhds

theorem tendsto_one_add_pow_succ_exp_of_tendsto {g : ℕ → ℂ} {z : ℂ}
    (h : Tendsto (fun n => ((n + 1 : ℕ) : ℂ) * g n) atTop (nhds z)) :
    Tendsto (fun n => (1 + g n) ^ (n + 1)) atTop (nhds (Complex.exp z)) := by
  let g' : ℕ → ℂ
    | 0 => 0
    | n + 1 => g n
  have hshift : Tendsto (fun n => ((n + 1 : ℕ) : ℂ) * g' (n + 1)) atTop (nhds z) := by
    simpa [g'] using h
  have hg' : Tendsto (fun n : ℕ => (n : ℂ) * g' n) atTop (nhds z) := by
    apply (Filter.tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => (n : ℂ) * g' n) 1).mp
    simpa only [Nat.add_comm] using hshift
  have hp := Complex.tendsto_one_add_pow_exp_of_tendsto hg'
  have hpShift : Tendsto (fun n => (1 + g' (n + 1)) ^ (n + 1)) atTop
      (nhds (Complex.exp z)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hp
  simpa [g'] using hpShift

/-- The root powers converge to the exponential of the linearized limit. -/
theorem HasLinearizedRootLimit.tendsto_charFun_pow {ρ : ℕ → ProbabilityMeasure ℝ}
    {ψ : ℝ → ℂ} (h : HasLinearizedRootLimit ρ ψ) (t : ℝ) :
    Tendsto (fun n => charFun (ρ n : Measure ℝ) t ^ (n + 1)) atTop
      (nhds (Complex.exp (ψ t))) := by
  have hp := tendsto_one_add_pow_succ_exp_of_tendsto (h.2 t)
  convert hp using 1
  funext n
  congr 1
  ring

/-- Compound-Poisson approximants for an arbitrary positive multiple of a linearized limit. -/
noncomputable def linearizedCompoundPoissonLaw (ρ : ℕ → ProbabilityMeasure ℝ)
    (r : NNReal) (n : ℕ) : ProbabilityMeasure ℝ :=
  CompoundPoisson.law (r * ((n + 1 : ℕ) : NNReal)) (ρ n)

theorem HasLinearizedRootLimit.tendsto_charFun_linearizedCompoundPoissonLaw
    {ρ : ℕ → ProbabilityMeasure ℝ} {ψ : ℝ → ℂ}
    (h : HasLinearizedRootLimit ρ ψ) (r : NNReal) (t : ℝ) :
    Tendsto (fun n => charFun (linearizedCompoundPoissonLaw ρ r n : Measure ℝ) t)
      atTop (nhds (Complex.exp ((r : ℂ) * ψ t))) := by
  have hscaled := Tendsto.const_mul (r : ℂ) (h.2 t)
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp hscaled
  convert hexp using 1
  funext n
  simp only [Function.comp_apply]
  rw [linearizedCompoundPoissonLaw, CompoundPoisson.charFun_law]
  push_cast
  ring

theorem HasLinearizedRootLimit.exists_powerLaw {ρ : ℕ → ProbabilityMeasure ℝ}
    {ψ : ℝ → ℂ} (h : HasLinearizedRootLimit ρ ψ) (r : NNReal) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t, charFun (μ : Measure ℝ) t = Complex.exp ((r : ℂ) * ψ t) := by
  obtain ⟨μ, hμ, -⟩ := exists_probabilityMeasure_of_tendsto_charFun
    (μ := linearizedCompoundPoissonLaw ρ r)
    (φ := fun t => Complex.exp ((r : ℂ) * ψ t))
    (Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.mul h.1))
    (h.tendsto_charFun_linearizedCompoundPoissonLaw r)
  exact ⟨μ, hμ⟩

noncomputable def HasLinearizedRootLimit.powerLaw {ρ : ℕ → ProbabilityMeasure ℝ}
    {ψ : ℝ → ℂ} (h : HasLinearizedRootLimit ρ ψ) (r : NNReal) :
    ProbabilityMeasure ℝ :=
  Classical.choose (h.exists_powerLaw r)

theorem HasLinearizedRootLimit.charFun_powerLaw {ρ : ℕ → ProbabilityMeasure ℝ}
    {ψ : ℝ → ℂ} (h : HasLinearizedRootLimit ρ ψ) (r : NNReal) (t : ℝ) :
    charFun (h.powerLaw r : Measure ℝ) t = Complex.exp ((r : ℂ) * ψ t) :=
  Classical.choose_spec (h.exists_powerLaw r) t

theorem HasLinearizedRootLimit.powerLaw_add {ρ : ℕ → ProbabilityMeasure ℝ}
    {ψ : ℝ → ℂ} (h : HasLinearizedRootLimit ρ ψ) (r s : NNReal) :
    h.powerLaw (r + s) = ProbabilityMeasure.conv (h.powerLaw r) (h.powerLaw s) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [ProbabilityMeasure.coe_conv, charFun_conv, h.charFun_powerLaw,
    h.charFun_powerLaw, h.charFun_powerLaw, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Corollary 16.7: the exponential of a continuous linearized root limit is an infinitely
divisible characteristic function. -/
theorem HasLinearizedRootLimit.isInfinitelyDivisible_powerLaw_one
    {ρ : ℕ → ProbabilityMeasure ℝ} {ψ : ℝ → ℂ}
    (h : HasLinearizedRootLimit ρ ψ) :
    (h.powerLaw 1).IsInfinitelyDivisible := by
  intro n hn
  let r : NNReal := ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n)⟩
  refine ⟨h.powerLaw r, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [ProbabilityMeasure.charFun_convPow_real, h.charFun_powerLaw,
    h.charFun_powerLaw, ← Complex.exp_nat_mul]
  congr 1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : (r : ℂ) = (n : ℂ)⁻¹ := by
    change (((n : ℝ)⁻¹ : ℝ) : ℂ) = (n : ℂ)⁻¹
    rw [Complex.ofReal_inv]
    rfl
  rw [hr, ← mul_assoc, mul_inv_cancel₀ hnC, one_mul]
  simp

/-- If both sides of Theorem 16.6 are presented, their pointwise limits agree by the exponential
formula. -/
theorem HasLinearizedRootLimit.powerLimit_eq_exp
    {ρ : ℕ → ProbabilityMeasure ℝ} {ψ φ : ℝ → ℂ}
    (h : HasLinearizedRootLimit ρ ψ)
    (hpow : ∀ t, Tendsto (fun n => charFun (ρ n : Measure ℝ) t ^ (n + 1))
      atTop (nhds (φ t))) :
    φ = fun t => Complex.exp (ψ t) := by
  funext t
  exact tendsto_nhds_unique (hpow t) (h.tendsto_charFun_pow t)

end ProbabilityTheory
