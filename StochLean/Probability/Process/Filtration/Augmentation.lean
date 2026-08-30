/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Filtration.Usual

/-!
# Usual augmentation of a filtration

The construction deliberately changes the ambient measurable space to Mathlib's
`NullMeasurableSpace Ω P` and the measure to `P.completion`. This avoids the semantically invalid
shortcut of claiming that the original ambient sigma-algebra already contains all null sets.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Filtration

/-- The smallest sigma-algebra containing every ambient `P`-null set. -/
@[instance_reducible] def nullSets {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {s | P s = 0}

/-- Lift a filtration to the completed ambient space and adjoin all ambient null sets at every
time. Right continuity is imposed separately by `usualAugmentation`. -/
def withNullSets {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (ℱ : Filtration ι m) (P : Measure Ω) :
    Filtration ι (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) where
  seq i := ℱ i ⊔ @nullSets Ω m P
  mono' _i _j hij := sup_le_sup_right (ℱ.mono hij) _
  le' i := sup_le
    (fun s hs ↦ (ℱ.le i s hs).nullMeasurableSet)
    (MeasurableSpace.generateFrom_le fun _s hs ↦ NullMeasurableSet.of_null hs)

/-- The usual augmentation: first adjoin all null sets in the genuinely completed ambient space,
then take Mathlib's right continuation. -/
noncomputable def usualAugmentation
    {Ω ι : Type*} {m : MeasurableSpace Ω} [PartialOrder ι]
    (ℱ : Filtration ι m) (P : Measure Ω) :
    Filtration ι (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
  (withNullSets ℱ P).rightCont

/-- The original information is contained in its usual augmentation. -/
theorem le_usualAugmentation
    {Ω ι : Type*} {m : MeasurableSpace Ω} [PartialOrder ι]
    (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    ℱ i ≤ usualAugmentation ℱ P i :=
  (show ℱ i ≤ withNullSets ℱ P i from le_sup_left).trans
    ((withNullSets ℱ P).le_rightCont i)

/-- The augmented filtration satisfies the usual conditions for the completed measure. -/
theorem usualAugmentation_isUsual
    {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι] [OrderBot ι]
    (ℱ : Filtration ι m) (P : Measure Ω) :
    (usualAugmentation ℱ P).IsUsual P.completion := by
  constructor
  · change ((withNullSets ℱ P).rightCont).IsRightContinuous
    infer_instance
  · intro s hs
    change P s = 0 at hs
    have hsnull : MeasurableSet[@nullSets Ω m P] s :=
      MeasurableSpace.measurableSet_generateFrom hs
    have hsbase : MeasurableSet[withNullSets ℱ P ⊥] s :=
      (le_sup_right : @nullSets Ω m P ≤ ℱ ⊥ ⊔ @nullSets Ω m P) s hsnull
    exact (withNullSets ℱ P).le_rightCont ⊥ s hsbase

end MeasureTheory.Filtration

