/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Process.Predictable
public import StochLean.Probability.Process.Filtration.Natural
public import StochLean.Probability.Process.Path.Cadlag
public import StochLean.Probability.Process.Stationarity
public import StochLean.Probability.Process.Stopping

/-!
# Semantic regression tests for process core

These counterexamples and compile-time examples protect the distinctions between modification and
indistinguishability, marginal and process stationarity, right continuity and the usual
conditions, and finite and infinite stopping times.
-/

@[expose] public section

open NNReal MeasureTheory TopologicalSpace
open scoped unitInterval
open scoped Topology

namespace ProbabilityTheory

noncomputable section

section Modification

/-- The diagonal spike on `[0,1]`: every fixed coordinate is zero almost surely, but every sample
path contains one spike. -/
def diagonalSpike (t ω : unitInterval) : ℝ := if ω = t then 1 else 0

def diagonalZero (_t _ω : unitInterval) : ℝ := 0

theorem diagonalSpike_isModification :
    IsModification diagonalSpike diagonalZero volume := by
  intro t
  filter_upwards [volume.ae_ne t] with ω hω
  simp [diagonalSpike, diagonalZero, hω]

theorem diagonalSpike_not_indistinguishable :
    ¬ Indistinguishable diagonalSpike diagonalZero volume := by
  intro hind
  have hfalse : ∀ᵐ _ω ∂(volume : Measure unitInterval), False := hind.mono fun ω hω ↦ by
    have h := hω ω
    simp [diagonalSpike, diagonalZero] at h
  have hzero := ae_iff.mp hfalse
  simp at hzero

/-- The diagonal spike and zero process nevertheless have the same coordinate-product law. This
does not turn their laws into pathwise equality or a law on a continuous-path topology. -/
theorem diagonalSpike_map_process_eq :
    (volume : Measure unitInterval).map (fun ω ↦ (diagonalSpike · ω)) =
      volume.map (fun ω ↦ (diagonalZero · ω)) := by
  apply diagonalSpike_isModification.map_process_eq
  · exact (measurable_pi_lambda _ fun t ↦
      Measurable.ite (measurableSet_singleton t) measurable_const measurable_const).aemeasurable
  · exact (measurable_pi_lambda _ fun _ ↦ measurable_const).aemeasurable

end Modification

section Stationarity

/-- Uniform probability on a Boolean Rademacher coordinate. -/
def uniformBoolMeasure : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

private theorem identDistrib_bool_not :
    IdentDistrib (fun x : Bool ↦ x) (!·) uniformBoolMeasure uniformBoolMeasure := by
  refine ⟨measurable_id.aemeasurable,
    (measurable_of_finite (fun x : Bool ↦ !x)).aemeasurable, ?_⟩
  rw [uniformBoolMeasure,
    PMF.toMeasure_map (f := fun x : Bool ↦ x) (PMF.uniformOfFintype Bool) measurable_id,
    PMF.toMeasure_map (f := fun x : Bool ↦ !x) (PMF.uniformOfFintype Bool)
      (measurable_of_finite _)]
  congr 1
  ext b
  cases b <;> simp [PMF.map_apply]

/-- `X₀ = Z`, `X₁ = Z`, and `Xₙ = ¬Z` for `n ≥ 2`. -/
def marginalStationarityCounterexample (t : ℕ) (ω : Bool) : Bool :=
  if t = 0 ∨ t = 1 then ω else !ω

/-- All one-time marginals of the counterexample agree. -/
theorem marginalStationarityCounterexample_identDistrib_zero (t : ℕ) :
    IdentDistrib (marginalStationarityCounterexample t)
      (marginalStationarityCounterexample 0) uniformBoolMeasure uniformBoolMeasure := by
  by_cases ht : t = 0 ∨ t = 1
  · rw [show marginalStationarityCounterexample t = (fun x : Bool ↦ x) by
          funext ω; simp only [marginalStationarityCounterexample, if_pos ht],
      show marginalStationarityCounterexample 0 = (fun x : Bool ↦ x) by
          funext ω; simp [marginalStationarityCounterexample]]
    exact IdentDistrib.refl (μ := uniformBoolMeasure) measurable_id.aemeasurable
  · rw [show marginalStationarityCounterexample t = (!·) by
          funext ω; simp only [marginalStationarityCounterexample, if_neg ht],
      show marginalStationarityCounterexample 0 = (fun x : Bool ↦ x) by
          funext ω; simp [marginalStationarityCounterexample]]
    exact identDistrib_bool_not.symm

/-- Equal one-time marginals do not imply stationarity: the first pair is always equal, while its
unit shift is always unequal. -/
theorem marginalStationarityCounterexample_not_stationary :
    ¬ IsStationary marginalStationarityCounterexample uniformBoolMeasure := by
  intro hstat
  have hpair := (hstat 1).comp
    (u := fun f : ℕ → Bool ↦ f 0 = f 1)
      ((measurable_pi_apply 0).eq (measurable_pi_apply 1))
  change IdentDistrib
    (fun ω ↦ marginalStationarityCounterexample 0 ω =
      marginalStationarityCounterexample 1 ω)
    (fun ω ↦ marginalStationarityCounterexample (1 + 0) ω =
      marginalStationarityCounterexample (1 + 1) ω)
    uniformBoolMeasure uniformBoolMeasure at hpair
  have hconst : IdentDistrib (fun _ : Bool ↦ True) (fun _ : Bool ↦ False)
      uniformBoolMeasure uniformBoolMeasure := by
    simpa [marginalStationarityCounterexample] using hpair
  have heq := hconst.measure_mem_eq (measurableSet_singleton True)
  simp [uniformBoolMeasure] at heq

end Stationarity

section Filtration

/-- The constant trivial filtration on a nontrivial ambient Boolean measurable space. -/
def incompleteBottomFiltration : Filtration ℝ≥0 (⊤ : MeasurableSpace Bool) :=
  Filtration.const ℝ≥0 ⊥ bot_le

theorem incompleteBottomFiltration_rightContinuous :
    incompleteBottomFiltration.IsRightContinuous := by
  constructor
  intro i
  rw [Filtration.rightCont_eq]
  change (⨅ j, ⨅ (_ : i < j), ⊥) ≤ ⊥
  exact iInf₂_le_of_le (i + 1) (by simp) le_rfl

theorem incompleteBottomFiltration_not_usual :
    ¬ incompleteBottomFiltration.IsUsual (Measure.dirac true) := by
  apply Filtration.not_isUsual_of_not_complete_initial
  intro hcomplete
  have hs : MeasurableSet[incompleteBottomFiltration ⊥] ({false} : Set Bool) :=
    hcomplete {false} (by simp)
  change MeasurableSet[⊥] ({false} : Set Bool) at hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with hs | hs
  · simp at hs
  · have : true ∈ ({false} : Set Bool) := by rw [hs]; trivial
    simp at this

end Filtration

section InfiniteStoppingTime

def alwaysInfiniteStoppingTime (Ω : Type*) : Ω → WithTop ℝ≥0 := fun _ ↦ ⊤

theorem alwaysInfiniteStoppingTime_isStoppingTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) :
    IsStoppingTime ℱ (alwaysInfiniteStoppingTime Ω) := by
  intro i
  simp [alwaysInfiniteStoppingTime]

/-- The value `∞` is preserved on a probability-one event; it is not encoded by a finite
sentinel. -/
theorem measure_alwaysInfiniteStoppingTime_eq_top
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] :
    P {ω | alwaysInfiniteStoppingTime Ω ω = ⊤} = 1 := by
  simp [alwaysInfiniteStoppingTime]

end InfiniteStoppingTime

section ReuseChains

/- Natural-filtration adaptedness and minimality compile together. -/
example {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    [TopologicalSpace E] [MetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (X : ι → Ω → E) (hX : ∀ i, StronglyMeasurable (X i)) :
    StronglyAdapted (Filtration.natural X hX) X ∧
      ∀ ℱ : Filtration ι mΩ, StronglyAdapted ℱ X → Filtration.natural X hX ≤ ℱ :=
  ⟨Filtration.stronglyAdapted_natural hX,
    fun ℱ hℱ ↦ Filtration.natural_le_of_stronglyAdapted X hX ℱ hℱ⟩

/- Predictable processes follow the canonical predictable → progressive → adapted chain. -/
example {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : IsStronglyPredictable ℱ X) :
    IsStronglyProgressive ℱ X ∧ StronglyAdapted ℱ X :=
  ⟨hX.isStronglyProgressive, hX.stronglyAdapted⟩

/- The discrete predictable characterization is exactly Mathlib's `n+1`/`n` information rule. -/
example {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → E} :
    IsStronglyPredictable ℱ X ↔ StronglyMeasurable[ℱ 0] (X 0) ∧
      ∀ n, StronglyMeasurable[ℱ n] (X (n + 1)) :=
  IsStronglyPredictable.iff_measurable_add_one

/- Cadlag is one trajectory-level property on one common full-measure event. -/
example {Ω E : Type*} {_mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} {P : Measure Ω} (hX : HasCadlagPaths X P) :
    ∀ᵐ ω ∂P, IsRightContinuousPath (fun t ↦ X t ω) ∧
      ∀ t, t ≠ ⊥ → ∃ y : E, Filter.Tendsto (fun u ↦ X u ω)
        (nhdsWithin t (Set.Iio t)) (𝓝 y) :=
  hX

end ReuseChains

end

end ProbabilityTheory
