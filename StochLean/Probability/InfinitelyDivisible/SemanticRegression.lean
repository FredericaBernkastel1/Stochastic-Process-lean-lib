/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.CompoundPoisson
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
public import StochLean.Probability.InfinitelyDivisible.Stable
public import StochLean.Probability.Process.StationaryIndependentIncrements

/-! Semantic compile-time guards for the LSII law layer. -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {G Ω : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [MeasurableSpace Ω]

example {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsConvolutionSemigroup ν) (t : ℝ≥0) :
    ProbabilityMeasure.IsInfinitelyDivisible (ν t) :=
  hν.isInfinitelyDivisible t

example (μ : ProbabilityMeasure G) :
    CompoundPoisson.law 0 μ = ProbabilityMeasure.pointMass 0 :=
  CompoundPoisson.law_zero μ

example : CompoundPoisson.ofFiniteMeasure (0 : FiniteMeasure G) =
    ProbabilityMeasure.pointMass 0 :=
  CompoundPoisson.ofFiniteMeasure_zero

example (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    CompoundPoisson.ofFiniteMeasure (r • μ.toFiniteMeasure) = CompoundPoisson.law r μ :=
  CompoundPoisson.ofFiniteMeasure_smul_probability r μ

example (r s : ℝ≥0) (μ : ProbabilityMeasure G) :
    CompoundPoisson.law (r + s) μ =
      ProbabilityMeasure.conv (CompoundPoisson.law r μ) (CompoundPoisson.law s μ) :=
  CompoundPoisson.law_add r s μ

example (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ProbabilityMeasure.IsInfinitelyDivisible (CompoundPoisson.law r μ) :=
  CompoundPoisson.isInfinitelyDivisible r μ

example {ν : Measure ℝ} (hν : IsLevyMeasure ν) : SigmaFinite ν :=
  hν.sigmaFinite

example : IsLevyMeasure geometricLevyMeasure :=
  isLevyMeasure_geometricLevyMeasure

example : geometricLevyMeasure Set.univ = ∞ :=
  geometricLevyMeasure_univ

example {μ : ProbabilityMeasure ℝ} (hμ : ProbabilityMeasure.IsStable μ) :
    ProbabilityMeasure.IsNonDirac μ :=
  hμ.1

example {μ : ProbabilityMeasure ℝ} (hμ : ProbabilityMeasure.IsStableInBroadSense μ) :
    ProbabilityMeasure.IsInfinitelyDivisible μ :=
  hμ.isInfinitelyDivisible

example {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : ProbabilityMeasure.IsStableInBroadSenseWithIndex α μ) :
    ProbabilityMeasure.IsStableInBroadSense μ :=
  hμ.isStableInBroadSense

example {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : ProbabilityMeasure.IsStableWithIndex α μ) :
    ProbabilityMeasure.IsStable μ :=
  hμ.isStable

example : signedLogAbs 0 = 0 := signedLogAbs_zero

variable {X : ℝ≥0 → Ω → G} {P : Measure Ω} {ν : ℝ≥0 → ProbabilityMeasure G}

example (hX : HasStationaryIndependentIncrements X P) (hν : HasIncrementLawFamily X ν P) :
    IsConvolutionSemigroup ν :=
  hX.isConvolutionSemigroup hν

section Topological

variable [TopologicalSpace G] [OpensMeasurableSpace G]

example {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ ν (t / (n + 1))) atTop
      (𝓝 (ProbabilityMeasure.pointMass (G := G) 0)) :=
  hν.roots_tendsto_zero ht

example {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν)
    (t : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure.convPow (ν (t / (n + 1))) (n + 1) = ν t :=
  hν.isConvolutionSemigroup.convPow_root t n

end Topological

end ProbabilityTheory
