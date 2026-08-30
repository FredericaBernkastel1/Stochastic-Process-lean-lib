/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Coupling.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Couplings and full total variation

The normalization here is Klenke's full total-variation norm: twice the supremum of the
difference on measurable events.  Consequently the coupling inequality has the indispensable
factor `2`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The event-supremum total-variation distance, without Klenke's factor two. -/
noncomputable def eventTotalVariationDistance (μ ν : Measure E) : ℝ≥0∞ :=
  ⨆ A : {A : Set E // MeasurableSet A}, ENNReal.ofReal |μ.real A - ν.real A|

/-- Klenke's full total-variation norm.  Its range on probability measures is `[0, 2]`. -/
noncomputable def fullTotalVariationDistance (μ ν : Measure E) : ℝ≥0∞ :=
  2 * eventTotalVariationDistance μ ν

/-- Every measurable event contributes a lower bound to the event-normalized distance. -/
theorem eventDistance_le_eventTotalVariationDistance
    (μ ν : Measure E) {A : Set E} (hA : MeasurableSet A) :
    ENNReal.ofReal |μ.real A - ν.real A| ≤ eventTotalVariationDistance μ ν := by
  unfold eventTotalVariationDistance
  exact le_iSup (fun B : {B : Set E // MeasurableSet B} =>
    ENNReal.ofReal |μ.real B - ν.real B|) ⟨A, hA⟩

/-- The event-normalized distance is bounded by Klenke's full normalization. -/
theorem eventTotalVariationDistance_le_fullTotalVariationDistance
    (μ ν : Measure E) :
    eventTotalVariationDistance μ ν ≤ fullTotalVariationDistance μ ν := by
  rw [fullTotalVariationDistance]
  nth_rewrite 1 [← one_mul (eventTotalVariationDistance μ ν)]
  gcongr
  norm_num

/-- The event-normalized distance between probability measures is at most one. -/
theorem eventTotalVariationDistance_le_one
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    eventTotalVariationDistance μ ν ≤ 1 := by
  unfold eventTotalVariationDistance
  refine iSup_le fun A => ?_
  rw [ENNReal.ofReal_le_one]
  rw [abs_sub_le_iff]
  constructor <;> linarith [measureReal_nonneg (μ := μ) (s := A.1),
    measureReal_nonneg (μ := ν) (s := A.1), measureReal_le_one (μ := μ) (s := A.1),
    measureReal_le_one (μ := ν) (s := A.1)]

/-- Klenke's full normalization has diameter two on probability measures. -/
theorem fullTotalVariationDistance_le_two
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    fullTotalVariationDistance μ ν ≤ 2 := by
  calc
    fullTotalVariationDistance μ ν = 2 * eventTotalVariationDistance μ ν := rfl
    _ ≤ 2 * 1 := by
      gcongr
      exact eventTotalVariationDistance_le_one μ ν
    _ = 2 := by simp

/-- Distinct point masses have event-normalized distance one. -/
theorem eventTotalVariationDistance_dirac_ne [MeasurableSingletonClass E]
    {x y : E} (hxy : x ≠ y) :
    eventTotalVariationDistance (Measure.dirac x) (Measure.dirac y) = 1 := by
  apply le_antisymm
  · exact eventTotalVariationDistance_le_one _ _
  · unfold eventTotalVariationDistance
    let A : {A : Set E // MeasurableSet A} := ⟨{x}, MeasurableSet.singleton x⟩
    calc
      1 = ENNReal.ofReal |(Measure.dirac x).real A - (Measure.dirac y).real A| := by
        simp [A, Measure.real, Measure.dirac_apply', Ne.symm hxy]
      _ ≤ ⨆ B : {B : Set E // MeasurableSet B},
          ENNReal.ofReal |(Measure.dirac x).real B - (Measure.dirac y).real B| :=
        le_iSup (fun B : {B : Set E // MeasurableSet B} =>
          ENNReal.ofReal |(Measure.dirac x).real B - (Measure.dirac y).real B|) A

/-- Under the full normalization, distinct point masses are exactly distance two apart. -/
theorem fullTotalVariationDistance_dirac_ne [MeasurableSingletonClass E]
    {x y : E} (hxy : x ≠ y) :
    fullTotalVariationDistance (Measure.dirac x) (Measure.dirac y) = 2 := by
  rw [fullTotalVariationDistance, eventTotalVariationDistance_dirac_ne hxy]
  simp

namespace IsCoupling

variable {γ : Measure (E × E)} {μ ν : Measure E}

/-- A measurable event can differ between the two coordinates only on the mismatch event. -/
theorem abs_measureReal_sub_le_mismatch [IsProbabilityMeasure γ]
    (hγ : IsCoupling γ μ ν) {A : Set E} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ γ.real {p | p.1 ≠ p.2} := by
  have hfst : μ.real A = γ.real (Prod.fst ⁻¹' A) := by
    rw [← hγ.fst, map_measureReal_apply measurable_fst hA]
  have hsnd : ν.real A = γ.real (Prod.snd ⁻¹' A) := by
    rw [← hγ.snd, map_measureReal_apply measurable_snd hA]
  have hleft : Prod.fst ⁻¹' A ⊆ Prod.snd ⁻¹' A ∪ {p : E × E | p.1 ≠ p.2} := by
    intro p hp
    by_cases h : p.1 = p.2
    · left
      simpa [h] using hp
    · exact Or.inr h
  have hright : Prod.snd ⁻¹' A ⊆ Prod.fst ⁻¹' A ∪ {p : E × E | p.1 ≠ p.2} := by
    intro p hp
    by_cases h : p.1 = p.2
    · left
      simpa [h] using hp
    · exact Or.inr h
  rw [hfst, hsnd]
  apply abs_sub_le_iff.mpr
  constructor
  · linarith [measureReal_mono (μ := γ) hleft (by finiteness),
      measureReal_union_le (μ := γ) (Prod.snd ⁻¹' A) {p : E × E | p.1 ≠ p.2}]
  · linarith [measureReal_mono (μ := γ) hright (by finiteness),
      measureReal_union_le (μ := γ) (Prod.fst ⁻¹' A) {p : E × E | p.1 ≠ p.2}]

/-- The event-supremum distance is bounded by the mismatch probability of every coupling. -/
theorem eventTotalVariationDistance_le_mismatch [IsProbabilityMeasure γ]
    (hγ : IsCoupling γ μ ν) :
    eventTotalVariationDistance μ ν ≤ couplingMismatch γ := by
  unfold eventTotalVariationDistance
  refine iSup_le fun A => ?_
  have hfinite : couplingMismatch γ ≠ ∞ := by
    apply ne_of_lt
    calc
      couplingMismatch γ ≤ γ Set.univ := measure_mono (subset_univ _)
      _ = 1 := MeasureTheory.measure_univ
      _ < ∞ := ENNReal.one_lt_top
  rw [ENNReal.ofReal_le_iff_le_toReal hfinite]
  simpa only [couplingMismatch, Measure.real] using
    hγ.abs_measureReal_sub_le_mismatch A.property

/-- Corrected coupling inequality for Klenke's full total-variation normalization. -/
theorem fullTotalVariationDistance_le_two_mul_mismatch [IsProbabilityMeasure γ]
    (hγ : IsCoupling γ μ ν) :
    fullTotalVariationDistance μ ν ≤ 2 * couplingMismatch γ := by
  unfold fullTotalVariationDistance
  gcongr
  exact hγ.eventTotalVariationDistance_le_mismatch

end IsCoupling

end ProbabilityTheory
