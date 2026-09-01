/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.CompoundPoisson
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
public import StochLean.Probability.InfinitelyDivisible.LevySemigroup
public import StochLean.Probability.InfinitelyDivisible.NonnegativeLevyKhintchine
public import StochLean.Probability.InfinitelyDivisible.NonnegativeExtraction
public import StochLean.Probability.InfinitelyDivisible.WeakClosure
public import StochLean.Probability.InfinitelyDivisible.PowerLimits
public import StochLean.Probability.InfinitelyDivisible.CanonicalRootAsymptotics
public import StochLean.Probability.InfinitelyDivisible.Stable
public import StochLean.Probability.InfinitelyDivisible.StableBounds
public import StochLean.Probability.InfinitelyDivisible.StableExponent
public import StochLean.Probability.InfinitelyDivisible.BoundedSupport
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
    (hμ : ProbabilityMeasure.IsStableInBroadSenseWithIndex α μ) : α ≤ 2 :=
  ProbabilityTheory.IsStableInBroadSenseWithIndex.index_le_two hμ

example {α : ℝ} {μ : ProbabilityMeasure ℝ} (hα : 2 < α) :
    ¬ ProbabilityMeasure.IsStableInBroadSenseWithIndex α μ := by
  intro hμ
  exact (not_lt_of_ge
    (ProbabilityTheory.IsStableInBroadSenseWithIndex.index_le_two hμ)) hα

example {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : ProbabilityMeasure.IsStableWithIndex α μ) :
    ProbabilityMeasure.IsStable μ :=
  hμ.isStable

example : signedLogAbs 0 = 0 := signedLogAbs_zero

example : stableSignedLogTerm 0 = 0 := stableSignedLogTerm_zero

example (cMinus cPlus : ℝ) : stableExponentClosedForm 1 cMinus cPlus 0 = 0 :=
  stableExponentClosedForm_zero 1 cMinus cPlus

example (cMinus cPlus : ℝ) : Continuous (stableExponentAtOne cMinus cPlus) :=
  continuous_stableExponentAtOne cMinus cPlus

example (η : LevyTriplet) (d : ℝ) :
    (η.affine 1 d zero_lt_one).jumpMeasure = η.jumpMeasure :=
  η.affine_one_jumpMeasure d

example (η : LevyTriplet) {d : ℝ} (hd : d ≠ 0) :
    (η.affine 1 d zero_lt_one).exponent ≠ η.exponent :=
  η.exponent_affine_one_ne hd

example {μ : ProbabilityMeasure ℝ} (hμ : μ.IsStableInBroadSense) :
    ∃ α : ℝ, α ∈ Set.Ioc 0 2 ∧ μ.IsStableInBroadSenseWithIndex α :=
  IsStableInBroadSense.exists_index hμ

example {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n).IsInfinitelyDivisible)
    (hlim : Tendsto μ atTop (nhds μ₀)) : μ₀.IsInfinitelyDivisible :=
  isInfinitelyDivisible_of_tendsto hμ hlim

example {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {a b : ℝ} (hbound : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Set.Icc a b) :
    ∃ c : ℝ, μ = ProbabilityMeasure.pointMass c :=
  hμ.eq_pointMass_of_boundedSupport hbound

example {ρ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (h : HasConvolutionPowerLimit ρ φ) (t : ℝ) : φ t ≠ 0 :=
  h.nonvanishing t

example {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto (fun n => canonicalRootLinearization hμ n t) atTop (𝓝 (hμ.exponent t)) :=
  ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization hμ t

example {η ξ : NonnegativeLevyPair} {μ : ProbabilityMeasure ℝ}
    (hη : η.toLevyTriplet.Represents μ) (hξ : ξ.toLevyTriplet.Represents μ) : η = ξ :=
  NonnegativeLevyPair.eq_of_represents hη hξ

example {μ : ProbabilityMeasure ℝ} :
    μ.IsInfinitelyDivisible ∧ μ.IsNonnegativeLaw ↔
      ∃! η : NonnegativeLevyPair, η.toLevyTriplet.Represents μ :=
  nonnegativeLevyKhintchine_iff

example {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n).IsInfinitelyDivisible)
    (hlim : Tendsto μ atTop (nhds μ₀)) (t : ℝ) :
    charFun (μ₀ : Measure ℝ) t ≠ 0 :=
  charFun_ne_zero_of_tendsto_infinitelyDivisible hμ hlim t

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
