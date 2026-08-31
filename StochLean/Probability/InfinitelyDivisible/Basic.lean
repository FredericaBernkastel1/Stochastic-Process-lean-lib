/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Convolution.Semigroup

/-!
# Infinitely divisible probability laws

The definition is law-first: every positive convolution root must exist.  No process or path-space
realization is bundled into the predicate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- A probability law is infinitely divisible if it has an `n`-fold convolution root for every
positive natural number `n`. -/
def IsInfinitelyDivisible (μ : ProbabilityMeasure G) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ρ : ProbabilityMeasure G, convPow ρ n = μ

/-- The Dirac law at the additive identity is infinitely divisible on every measurable additive
commutative monoid. -/
theorem isInfinitelyDivisible_pointMass_zero :
    IsInfinitelyDivisible (pointMass (G := G) 0) := by
  have hpow : ∀ n : ℕ, convPow (pointMass (G := G) 0) n = pointMass 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [convPow_succ, ih]
  intro n _
  exact ⟨pointMass 0, hpow n⟩

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

theorem IsConvolutionSemigroup.convPow_succ
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν)
    (t : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure.convPow (ν t) (n + 1) = ν ((n + 1) • t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ, ih, ← hν.add]
      congr 1

/-- The canonical `(n+1)`-st root of a semigroup marginal. -/
theorem IsConvolutionSemigroup.convPow_root
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν)
    (t : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure.convPow (ν (t / (n + 1))) (n + 1) = ν t := by
  rw [hν.convPow_succ]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- Every marginal of a nonnegative-time convolution semigroup is infinitely divisible.  This
uses only the semigroup law; continuity and the time-zero identity are not required. -/
theorem IsConvolutionSemigroup.isInfinitelyDivisible
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν) (t : ℝ≥0) :
    ProbabilityMeasure.IsInfinitelyDivisible (ν t) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨ν (t / (m + 1)), ?_⟩
  rw [hν.convPow_succ]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

end ProbabilityTheory
