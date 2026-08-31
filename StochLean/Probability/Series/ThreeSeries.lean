/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic

/-!
# Ordered random series and Kolmogorov's three conditions

The order of a real series is part of the API.  In particular, expectation series use convergence
of ordinary prefix sums and are not replaced by `Summable`, which would impose absolute
convergence over `ℝ`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Prefix sum over exactly the indices `0, ..., n - 1`. -/
def orderedPartialSum {A : Type*} [AddCommMonoid A] (a : ℕ → A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range n, a k

/-- Convergence of an ordinary ordered series, without an absolute/unconditional strengthening. -/
def OrderedSeriesConverges (a : ℕ → ℝ) : Prop :=
  ∃ s : ℝ, Tendsto (orderedPartialSum a) atTop (𝓝 s)

/-- Ordered random prefix sums converge on one measurable full-measure event. -/
def OrderedRandomSeriesConvergesAE (X : ℕ → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, ∃ s : ℝ, Tendsto (fun n ↦ orderedPartialSum (fun k ↦ X k ω) n) atTop (𝓝 s)

/-- Klenke's truncation convention includes the boundary `|X n| = K`. -/
noncomputable def threeSeriesTruncation (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if |X n ω| ≤ K then X n ω else 0

/-- The three source conditions: summable large-jump probabilities, ordered convergence of the
truncated expectation series, and summable truncated variances. -/
def KolmogorovThreeSeriesConditions (X : ℕ → Ω → ℝ) (P : Measure Ω) (K : ℝ) : Prop :=
  (∑' n, P {ω | K < |X n ω|}) < ∞ ∧
    OrderedSeriesConverges (fun n ↦ ∫ ω, threeSeriesTruncation X K n ω ∂P) ∧
    (∑' n, ENNReal.ofReal (variance (threeSeriesTruncation X K n) P)) < ∞

@[simp]
theorem orderedPartialSum_zero {A : Type*} [AddCommMonoid A] (a : ℕ → A) :
    orderedPartialSum a 0 = 0 := by
  simp [orderedPartialSum]

theorem orderedPartialSum_succ {A : Type*} [AddCommMonoid A] (a : ℕ → A) (n : ℕ) :
    orderedPartialSum a (n + 1) = orderedPartialSum a n + a n := by
  simp [orderedPartialSum, Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
@[simp]
theorem threeSeriesTruncation_of_le (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω)
    (h : |X n ω| ≤ K) : threeSeriesTruncation X K n ω = X n ω := by
  simp [threeSeriesTruncation, h]

omit [MeasurableSpace Ω] in
@[simp]
theorem threeSeriesTruncation_of_lt (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω)
    (h : K < |X n ω|) : threeSeriesTruncation X K n ω = 0 := by
  simp [threeSeriesTruncation, not_le_of_gt h]

omit [MeasurableSpace Ω] in
/-- The large-jump and truncation events partition the natural domain without changing the source
boundary convention. -/
theorem threeSeriesTruncation_eq_indicator (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) :
    threeSeriesTruncation X K n = {ω | |X n ω| ≤ K}.indicator (X n) := by
  funext ω
  by_cases h : |X n ω| ≤ K <;> simp [threeSeriesTruncation, h]

end ProbabilityTheory
