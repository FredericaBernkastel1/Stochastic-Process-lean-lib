/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convolution semigroups of probability laws

The basic predicate contains only the semigroup equation.  In particular it does not silently
assert an identity law at time zero or continuity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Additive convolution, closed in the canonical probability-measure subtype. -/
noncomputable def conv (μ ν : ProbabilityMeasure G) : ProbabilityMeasure G :=
  ⟨(μ : Measure G) ∗ (ν : Measure G), inferInstance⟩

@[simp, norm_cast]
theorem coe_conv (μ ν : ProbabilityMeasure G) :
    ((conv μ ν : ProbabilityMeasure G) : Measure G) = (μ : Measure G) ∗ (ν : Measure G) :=
  rfl

/-- Canonical Dirac probability law. -/
noncomputable def pointMass (x : G) : ProbabilityMeasure G :=
  ⟨Measure.dirac x, inferInstance⟩

omit [AddCommMonoid G] [MeasurableAdd₂ G] in
@[simp, norm_cast]
theorem coe_pointMass (x : G) :
    ((pointMass x : ProbabilityMeasure G) : Measure G) = Measure.dirac x :=
  rfl

@[simp]
theorem conv_assoc (μ ν ρ : ProbabilityMeasure G) :
    conv (conv μ ν) ρ = conv μ (conv ν ρ) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv]
  exact Measure.conv_assoc _ _ _

@[simp]
theorem conv_comm (μ ν : ProbabilityMeasure G) : conv μ ν = conv ν μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv]
  exact Measure.conv_comm (μ : Measure G) (ν : Measure G)

@[simp]
theorem pointMass_zero_conv (μ : ProbabilityMeasure G) : conv (pointMass 0) μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv, coe_pointMass]
  exact Measure.dirac_zero_conv _

@[simp]
theorem conv_pointMass_zero (μ : ProbabilityMeasure G) : conv μ (pointMass 0) = μ := by
  rw [conv_comm, pointMass_zero_conv]

@[simp]
theorem pointMass_conv_pointMass (x y : G) :
    conv (pointMass x) (pointMass y) = pointMass (x + y) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv, coe_pointMass]
  exact Measure.dirac_conv_dirac x y

/-- The `n`-fold convolution power, including the canonical zeroth power `δ₀`. -/
noncomputable def convPow (μ : ProbabilityMeasure G) : ℕ → ProbabilityMeasure G
  | 0 => pointMass (G := G) 0
  | n + 1 => conv (convPow μ n) μ

@[simp]
theorem convPow_zero (μ : ProbabilityMeasure G) : convPow μ 0 = pointMass (G := G) 0 := rfl

@[simp]
theorem convPow_succ (μ : ProbabilityMeasure G) (n : ℕ) :
    convPow μ (n + 1) = conv (convPow μ n) μ := rfl

@[simp]
theorem convPow_one (μ : ProbabilityMeasure G) : convPow μ 1 = μ := by
  simp [convPow]

theorem convPow_add (μ : ProbabilityMeasure G) (m n : ℕ) :
    convPow μ (m + n) = conv (convPow μ m) (convPow μ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, convPow_succ, convPow_succ, ih, conv_assoc]

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {T G : Type*} [Add T] [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The law-level convolution semigroup property, with no identity or continuity bundled in. -/
def IsConvolutionSemigroup (ν : T → ProbabilityMeasure G) : Prop :=
  ∀ s t, ν (s + t) = ProbabilityMeasure.conv (ν s) (ν t)

theorem IsConvolutionSemigroup.add {ν : T → ProbabilityMeasure G}
    (hν : IsConvolutionSemigroup ν) (s t : T) :
    ν (s + t) = ProbabilityMeasure.conv (ν s) (ν t) :=
  hν s t

section Continuous

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- Continuous refinement on nonnegative real time.  The limit is explicitly from positive times. -/
def IsContinuousConvolutionSemigroup (ν : ℝ≥0 → ProbabilityMeasure G) : Prop :=
  IsConvolutionSemigroup ν ∧
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi (0 : ℝ≥0)))
      (𝓝 (ProbabilityMeasure.pointMass (G := G) (0 : G)))

theorem IsContinuousConvolutionSemigroup.isConvolutionSemigroup
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    IsConvolutionSemigroup ν :=
  hν.1

theorem IsContinuousConvolutionSemigroup.tendsto_zero
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi (0 : ℝ≥0)))
      (𝓝 (ProbabilityMeasure.pointMass (G := G) (0 : G))) :=
  hν.2

/-- Positive-time convolution roots supplied by a continuous semigroup converge to `δ₀`. -/
theorem IsContinuousConvolutionSemigroup.roots_tendsto_zero
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ ν (t / (n + 1))) atTop
      (𝓝 (ProbabilityMeasure.pointMass (G := G) 0)) := by
  apply hν.tendsto_zero.comp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hden : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hreal : Tendsto (fun n : ℕ ↦ (t : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hnn := tendsto_real_toNNReal hreal
    convert hnn using 1
    · funext n
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by positivity)]
      simp
    · simp
  · filter_upwards [] with n
    exact div_pos ht (by positivity)

end Continuous

end ProbabilityTheory
