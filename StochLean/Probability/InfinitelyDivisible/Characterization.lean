/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.RootLimits

/-!
# Characterization by nonnegative convolution powers

This file gives the law-level characterization of infinite divisibility by a normalized
continuous characteristic exponent whose every nonnegative real multiple exponentiates to a
characteristic function.  It is the internal StochLean form of Klenke Corollaries 16.7--16.8.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

/-- A probability law has a normalized continuous exponent admitting characteristic laws at
every nonnegative time. -/
def HasAllNonnegativeConvolutionPowers (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ ψ : C(ℝ, ℂ), ψ 0 = 0 ∧
    (∀ t, charFun (μ : Measure ℝ) t = Complex.exp (ψ t)) ∧
    ∀ r : NNReal, ∃ ν : ProbabilityMeasure ℝ,
      ∀ t, charFun (ν : Measure ℝ) t = Complex.exp ((r : ℂ) * ψ t)

theorem ProbabilityMeasure.IsInfinitelyDivisible.hasAllNonnegativeConvolutionPowers
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    HasAllNonnegativeConvolutionPowers μ := by
  refine ⟨hμ.exponent, hμ.exponent_zero, (fun t ↦ (hμ.exp_exponent t).symm), ?_⟩
  intro r
  exact ⟨hμ.positivePower r, hμ.charFun_positivePower r⟩

/-- Klenke Corollary 16.7 in law form: if all nonnegative multiples of a normalized continuous
exponent are characteristic exponents, then its unit-time law is infinitely divisible. -/
theorem HasAllNonnegativeConvolutionPowers.isInfinitelyDivisible
    {μ : ProbabilityMeasure ℝ} (hμ : HasAllNonnegativeConvolutionPowers μ) :
    μ.IsInfinitelyDivisible := by
  obtain ⟨ψ, -, hψμ, hpowers⟩ := hμ
  intro n hn
  let r : NNReal := ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n)⟩
  obtain ⟨ρ, hρ⟩ := hpowers r
  refine ⟨ρ, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [ProbabilityMeasure.charFun_convPow_real, hρ, hψμ, ← Complex.exp_nat_mul]
  congr 1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : (r : ℂ) = (n : ℂ)⁻¹ := by
    change (((n : ℝ)⁻¹ : ℝ) : ℂ) = (n : ℂ)⁻¹
    rw [Complex.ofReal_inv]
    rfl
  rw [hr, ← mul_assoc, mul_inv_cancel₀ hnC, one_mul]

/-- Klenke Corollary 16.8: infinite divisibility is equivalent to admitting all nonnegative
convolution powers through one normalized continuous characteristic exponent. -/
theorem isInfinitelyDivisible_iff_hasAllNonnegativeConvolutionPowers
    (μ : ProbabilityMeasure ℝ) :
    μ.IsInfinitelyDivisible ↔ HasAllNonnegativeConvolutionPowers μ :=
  ⟨ProbabilityMeasure.IsInfinitelyDivisible.hasAllNonnegativeConvolutionPowers,
    HasAllNonnegativeConvolutionPowers.isInfinitelyDivisible⟩

end ProbabilityTheory
