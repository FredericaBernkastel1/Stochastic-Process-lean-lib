/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Semigroup
public import StochLean.ForMathlib.MeasureTheory.Measure.VagueConvergence
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Feller semigroups

This file uses Mathlib's `C₀(E, ℝ)` and Klenke's pointwise-at-zero definition.  Sup-norm
strong continuity is deliberately not built into `IsFellerSemigroup`: the cited proof of its
equivalence with this definition has to be audited before that bridge is added.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal ProbabilityTheory Topology ZeroAtInfty

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The action of a transition kernel on a real-valued `C₀` test function. -/
noncomputable def kernelAction (κ : Kernel E E) (f : C₀(E, ℝ)) (x : E) : ℝ :=
  ∫ y, f y ∂κ x

/-- Klenke's Feller-semigroup predicate: Markov semigroup, preservation of Mathlib's `C₀`,
and pointwise convergence to the identity as nonnegative time tends down to zero. -/
structure IsFellerSemigroup (κ : ℝ≥0 → Kernel E E) : Prop where
  toIsMarkovSemigroup : IsMarkovSemigroup κ
  maps_zeroAtInfty : ∀ t f, ∃ g : C₀(E, ℝ), ∀ x, g x = kernelAction (κ t) f x
  tendsto_zero : ∀ f x,
    Tendsto (fun t : ℝ≥0 => kernelAction (κ t) f x) (𝓝 0) (𝓝 (f x))

namespace IsFellerSemigroup

variable {κ : ℝ≥0 → Kernel E E} (hκ : IsFellerSemigroup κ)
include hκ

/-- The canonical `C₀` representative of the kernel action. -/
noncomputable def operatorValue (t : ℝ≥0) (f : C₀(E, ℝ)) : C₀(E, ℝ) :=
  Classical.choose (hκ.maps_zeroAtInfty t f)

@[simp]
theorem operatorValue_apply (t : ℝ≥0) (f : C₀(E, ℝ)) (x : E) :
    hκ.operatorValue t f x = kernelAction (κ t) f x :=
  Classical.choose_spec (hκ.maps_zeroAtInfty t f) x

/-- At every fixed time the kernel action on a `C₀` test function is continuous in the state. -/
theorem continuous_kernelAction (t : ℝ≥0) (f : C₀(E, ℝ)) :
    Continuous (kernelAction (κ t) f) := by
  obtain ⟨g, hg⟩ := hκ.maps_zeroAtInfty t f
  exact g.continuous.congr fun x => hg x

/-- The Feller operator is linear on `C₀(E, ℝ)`. -/
noncomputable def operator (t : ℝ≥0) : C₀(E, ℝ) →ₗ[ℝ] C₀(E, ℝ) where
  toFun := hκ.operatorValue t
  map_add' f g := by
    ext x
    letI : IsMarkovKernel (κ t) := hκ.toIsMarkovSemigroup.markov t
    simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, operatorValue_apply]
    unfold kernelAction
    exact integral_add (f.toBCF.integrable (κ t x)) (g.toBCF.integrable (κ t x))
  map_smul' c f := by
    ext x
    simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply,
      operatorValue_apply]
    unfold kernelAction
    exact integral_smul c (fun y => f y)

@[simp]
theorem operator_apply (t : ℝ≥0) (f : C₀(E, ℝ)) (x : E) :
    hκ.operator t f x = kernelAction (κ t) f x :=
  operatorValue_apply hκ t f x

/-- Every Feller operator is a contraction in the `C₀` sup norm. -/
theorem norm_operator_le (t : ℝ≥0) (f : C₀(E, ℝ)) :
    ‖hκ.operator t f‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => ?_
  rw [ZeroAtInftyContinuousMap.toBCF_apply, operator_apply]
  letI : IsMarkovKernel (κ t) := hκ.toIsMarkovSemigroup.markov t
  exact (f.toBCF.norm_integral_le_norm (κ t x)).trans_eq
    ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

/-- At time zero the Feller operator is the identity. -/
@[simp]
theorem operator_zero : hκ.operator 0 = LinearMap.id := by
  ext f x
  rw [operator_apply, kernelAction, hκ.toIsMarkovSemigroup.zero, Kernel.id_apply]
  exact integral_dirac' f x f.toBCF.continuous.stronglyMeasurable

/-- The operator composition order induced by Mathlib's kernel convention:
`κ (s+t) = κ t ∘ₖ κ s` acts as `P_s (P_t f)`. -/
theorem operator_add (s t : ℝ≥0) :
    hκ.operator (s + t) = (hκ.operator s).comp (hκ.operator t) := by
  ext f x
  simp only [LinearMap.comp_apply, operator_apply]
  letI : IsMarkovKernel (κ s) := hκ.toIsMarkovSemigroup.markov s
  letI : IsMarkovKernel (κ t) := hκ.toIsMarkovSemigroup.markov t
  have hf : Integrable (fun y => f y) ((κ t ∘ₖ κ s) x) := by
    letI : IsProbabilityMeasure ((κ t ∘ₖ κ s) x) := by infer_instance
    exact f.toBCF.integrable _
  rw [kernelAction, hκ.toIsMarkovSemigroup.add, Kernel.integral_comp hf]
  apply integral_congr_ae
  exact ae_of_all _ fun y => (operator_apply hκ t f y).symm

/-- The pointwise-at-zero field, restated for the derived operator. -/
theorem tendsto_operator_zero (f : C₀(E, ℝ)) (x : E) :
    Tendsto (fun t : ℝ≥0 => hκ.operator t f x) (𝓝 0) (𝓝 (f x)) := by
  simpa only [operator_apply] using hκ.tendsto_zero f x

/-- Fixed-time transition measures depend vaguely continuously on the initial state.  This is the
canonical noncompact statement obtained directly from the `C₀` Feller axiom; on compact state
spaces it upgrades to ordinary weak continuity below. -/
theorem tendstoVaguely_transitionMeasure (t : ℝ≥0) (x : E) :
    TendstoVaguely (fun y => κ t y) (𝓝 x) (κ t x) := by
  letI : IsMarkovKernel (κ t) := hκ.toIsMarkovSemigroup.markov t
  refine ⟨fun _ => inferInstance, inferInstance, fun f => ?_⟩
  have hcont : Continuous (kernelAction (κ t) (f : C₀(E, ℝ))) :=
    hκ.continuous_kernelAction t (f : C₀(E, ℝ))
  change Tendsto (kernelAction (κ t) (f : C₀(E, ℝ))) (𝓝 x)
    (𝓝 (kernelAction (κ t) (f : C₀(E, ℝ)) x))
  exact hcont.continuousAt

/-- The probability measure represented by a Feller transition row.  Naming this subtype value
keeps proof witnesses out of downstream weak-convergence statements. -/
noncomputable def transitionProbabilityMeasure (t : ℝ≥0) (x : E) : ProbabilityMeasure E :=
  ⟨κ t x, (hκ.toIsMarkovSemigroup.markov t).isProbabilityMeasure x⟩

@[simp]
theorem coe_transitionProbabilityMeasure (t : ℝ≥0) (x : E) :
    (hκ.transitionProbabilityMeasure t x : Measure E) = κ t x :=
  rfl

/-- On a compact state space, a Feller transition kernel is weakly continuous in its initial
state. -/
theorem continuous_transitionProbabilityMeasure [CompactSpace E] (t : ℝ≥0) :
    Continuous (hκ.transitionProbabilityMeasure t) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (hκ.transitionProbabilityMeasure t) (𝓝 x)
    (𝓝 (hκ.transitionProbabilityMeasure t x))
  rw [ProbabilityMeasure.tendsto_iff_tendstoVaguely]
  simpa only [coe_transitionProbabilityMeasure] using hκ.tendstoVaguely_transitionMeasure t x

/-- On a compact state space, Feller transition laws converge weakly to the point mass at their
initial state as time decreases to zero. -/
theorem tendsto_transitionProbabilityMeasure_zero [CompactSpace E] (x : E) :
    Tendsto (fun t => hκ.transitionProbabilityMeasure t x) (𝓝 0) (𝓝 (diracProba x)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  let g : C₀(E, ℝ) :=
    ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f.toContinuousMap
  have hg (y : E) : g y = f y := rfl
  have h := hκ.tendsto_zero g x
  rw [show (diracProba x : Measure E) = Measure.dirac x by rfl,
    integral_dirac' f x f.continuous.stronglyMeasurable]
  simpa only [coe_transitionProbabilityMeasure, kernelAction, hg] using h

end IsFellerSemigroup

end ProbabilityTheory
