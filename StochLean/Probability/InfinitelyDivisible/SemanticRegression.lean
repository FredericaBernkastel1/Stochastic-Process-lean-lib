/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.CompoundPoisson
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
public import StochLean.Probability.InfinitelyDivisible.LevySemigroup
public import StochLean.Probability.InfinitelyDivisible.Stable
public import StochLean.Probability.Process.StationaryIndependentIncrements

/-! Semantic compile-time guards for the LSII law layer. -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {G Ω : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [MeasurableSpace Ω]

example {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsConvolutionSemigroup ν) :
    ν 0 = ProbabilityMeasure.pointMass 0 :=
  hν.zero_eq_pointMass_real

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

example (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (CompoundPoisson.law r μ : Measure ℝ) t =
      Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) :=
  CompoundPoisson.charFun_law r μ t

example (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ProbabilityMeasure.IsInfinitelyDivisible (CompoundPoisson.law r μ) :=
  CompoundPoisson.isInfinitelyDivisible r μ

example {ν : Measure ℝ} (hν : IsLevyMeasure ν) : SigmaFinite ν :=
  hν.sigmaFinite

example : IsLevyMeasure geometricLevyMeasure :=
  isLevyMeasure_geometricLevyMeasure

example : geometricLevyMeasure Set.univ = ∞ :=
  geometricLevyMeasure_univ

example {ν : Measure ℝ} (hν : IsLevyMeasure ν) (t : ℝ) :
    Integrable (levyExponentIntegrand t) ν :=
  hν.integrable_levyExponentIntegrand t

example (η : LevyTriplet) (n : ℕ) (t : ℝ) :
    (η.nsmul n).exponent t = (n : ℂ) * η.exponent t :=
  η.exponent_nsmul n t

example (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).drift = a * η.drift + d +
      ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure := rfl

example (η : LevyTriplet) (a d t : ℝ) (ha : 0 < a) :
    (η.affine a d ha).exponent t =
      η.exponent (a * t) + ((d * t : ℝ) : ℂ) * Complex.I :=
  η.exponent_affine a d ha t

example (x : ℝ) :
    (LevyTriplet.pointMass x).Represents (ProbabilityMeasure.pointMass x) :=
  LevyTriplet.represents_pointMass x

example (m : ℝ) (v : ℝ≥0) :
    (LevyTriplet.gaussian m v).Represents (LevyTriplet.gaussianLaw m v) :=
  LevyTriplet.gaussian_represents_gaussianLaw m v

example (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (hzero : (μ : Measure ℝ) {0} = 0) :
    (CompoundPoisson.triplet r μ hzero).Represents (CompoundPoisson.law r μ) :=
  CompoundPoisson.triplet_represents_law r μ hzero

example (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (hzero : (μ : Measure ℝ) {0} = 0) :
    IsContinuousConvolutionSemigroup (fun t => CompoundPoisson.law (t * r) μ) :=
  CompoundPoisson.isContinuousConvolutionSemigroup_mul r μ hzero

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

example [IsProbabilityMeasure P] (hX : HasFiniteStationaryIncrementLaws X ν P) :
    HasStationaryIndependentIncrements X P :=
  hX.hasStationaryIndependentIncrements

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

example {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsContinuousConvolutionSemigroup ν) :
    Continuous ν :=
  hν.continuous_real

end ProbabilityTheory
