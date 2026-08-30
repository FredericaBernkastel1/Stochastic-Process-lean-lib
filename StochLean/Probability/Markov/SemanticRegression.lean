/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Convergence
public import StochLean.Probability.Markov.Countable.Invariant
public import StochLean.Probability.Markov.Countable.Periodicity
public import StochLean.Probability.Markov.Feller
public import StochLean.Probability.Markov.Generator.Poisson

/-!
# Markov semantic regressions

These compile-time checks pin the source corrections and representation boundaries that are easy
to reverse accidentally: zero-time reachability, strictly positive return times, full-TV
normalization, semantic coalescence, the safe zero uniformization branch, and operator order.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology ZeroAtInfty

namespace ProbabilityTheory

private noncomputable def forceTrueKernel : Kernel Bool Bool :=
  Kernel.deterministic (fun _ => true) (measurable_of_countable _)

private noncomputable def flipKernel : Kernel Bool Bool :=
  Kernel.deterministic (!·) (measurable_of_countable _)

/-- Kernel composition is genuinely ordered: first forcing `true` and then flipping differs from
first flipping and then forcing `true`. -/
example :
    flipKernel ∘ₖ forceTrueKernel ≠ forceTrueKernel ∘ₖ flipKernel := by
  intro h
  have h' := congrArg (fun K : Kernel Bool Bool => K false {false}) h
  simp [forceTrueKernel, flipKernel, Kernel.deterministic_comp_deterministic,
    Kernel.deterministic_apply] at h'

example {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (κ : Kernel E E) (x : E) : κ.CanReach x x :=
  Kernel.canReach_self κ x

example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (X : ℕ → Ω → E) (A : Set E) (ω : Ω) :
    1 ≤ firstPositiveHittingTime X A ω :=
  one_le_firstPositiveHittingTime X A ω

/-- A two-point mutually singular pair forces the corrected full-TV diameter `2`. -/
example :
    fullTotalVariationDistance (Measure.dirac false) (Measure.dirac true) = 2 := by
  exact fullTotalVariationDistance_dirac_ne Bool.false_ne_true

example {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    independentCoalescentKernel κ (x, x) {p | p.1 ≠ p.2} = 0 :=
  independentCoalescentKernel_diagonal_compl κ x

example {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (q : E → E → ℝ) (t : ℝ≥0) :
    uniformizedSemigroup q 0 t = Kernel.id :=
  uniformizedSemigroup_zero_rate q t

example (rate : ℝ≥0) : IsQMatrix (poissonQMatrix rate) :=
  isQMatrix_poissonQMatrix rate

/-- The Poisson Q-matrix regression pins the OCR-sensitive sign distinction: the successor rate
is positive while the diagonal rate is negative. -/
example (rate : ℝ≥0) (hrate : 0 < rate) :
    poissonQMatrix rate (0 : ℕ) (1 : ℕ) > 0 ∧
      poissonQMatrix rate (0 : ℕ) (0 : ℕ) < 0 := by
  simp [poissonQMatrix, hrate]

example (rate : ℝ≥0) :
    HasQMatrix (uniformizedSemigroup (poissonQMatrix rate) rate) (poissonQMatrix rate) :=
  hasQMatrix_poissonUniformizedSemigroup rate

/-- Choosing a larger valid Poisson domination rate leaves the transition semigroup unchanged. -/
example (rate : ℝ≥0) {Λ M : ℝ}
    (hΛ : IsUniformizationRate (poissonQMatrix rate) Λ)
    (hM : IsUniformizationRate (poissonQMatrix rate) M) :
    uniformizedSemigroup (poissonQMatrix rate) Λ =
      uniformizedSemigroup (poissonQMatrix rate) M :=
  uniformizedSemigroup_rate_independent (isQMatrix_poissonQMatrix rate) hΛ hM

example (rate : ℝ≥0) {Λ : ℝ}
    (hΛ : IsUniformizationRate (poissonQMatrix rate) Λ) :
    ∃! κ : ℝ≥0 → Kernel ℕ ℕ,
      IsCanonicalBoundedQSemigroup (poissonQMatrix rate) κ :=
  existsUnique_isCanonicalBoundedQSemigroup (isQMatrix_poissonQMatrix rate) hΛ

example {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {κ : ℝ≥0 → Kernel E E} (hκ : IsFellerSemigroup κ) (s t : ℝ≥0) :
    hκ.operator (s + t) = (hκ.operator s).comp (hκ.operator t) :=
  hκ.operator_add s t

example {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (γ : Measure ((ℕ → E) × (ℕ → E))) [IsProbabilityMeasure γ] :
    IsSuccessfulPathCoupling γ ↔ EventuallyEqualAE γ :=
  successfulPathCoupling_iff_eventuallyEqualAE γ

end ProbabilityTheory
