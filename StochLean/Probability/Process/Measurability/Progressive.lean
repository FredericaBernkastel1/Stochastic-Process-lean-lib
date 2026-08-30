/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Probability.Process.Adapted
public import StochLean.Probability.Process.Filtration.Usual
public import StochLean.Probability.Process.Measurability.Joint
public import StochLean.Probability.Process.Path.Cadlag

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

private noncomputable def rightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil (((n + 1 : ℕ) : ℝ≥0) * t) : ℝ≥0) / (n + 1 : ℕ)

private lemma le_rightGrid (n : ℕ) (t : ℝ≥0) : t ≤ rightGrid n t := by
  rw [rightGrid, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using Nat.le_ceil (((n + 1 : ℕ) : ℝ≥0) * t)

private lemma measurable_rightGrid (n : ℕ) : Measurable (rightGrid n) := by
  unfold rightGrid
  fun_prop

private lemma countable_range_rightGrid (n : ℕ) :
    (Set.range (rightGrid n)).Countable := by
  refine (Set.countable_range (fun k : ℕ ↦ (k : ℝ≥0) / (n + 1 : ℕ))).mono ?_
  rintro y ⟨t, rfl⟩
  exact ⟨Nat.ceil (((n + 1 : ℕ) : ℝ≥0) * t), rfl⟩

private lemma rightGrid_lt (n : ℕ) (t : ℝ≥0) :
    rightGrid n t < t + 1 / (n + 1 : ℕ) := by
  rw [rightGrid, div_lt_iff₀ (by positivity)]
  have h := Nat.ceil_lt_add_one (R := ℝ≥0)
    (a := ((n + 1 : ℕ) : ℝ≥0) * t) (by positivity)
  convert h using 1
  rw [add_mul, one_div, inv_mul_cancel₀]
  · ring
  · positivity

private lemma tendsto_rightGrid (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ rightGrid n t) Filter.atTop (𝓝 t) := by
  have hu : Filter.Tendsto (fun n : ℕ ↦ t + 1 / ((n : ℝ≥0) + 1))
      Filter.atTop (𝓝 t) := by
    simpa using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1))
            Filter.atTop (𝓝 0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n ↦ le_rightGrid n t) (fun n ↦ by
      simpa [Nat.cast_add, Nat.cast_one] using (rightGrid_lt n t).le)

private lemma tendsto_rightGrid_nhdsWithin (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ rightGrid n t) Filter.atTop (nhdsWithin t (Set.Ici t)) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_rightGrid t,
    Filter.Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (le_rightGrid n t)⟩

private noncomputable def cappedRightGrid (i : ℝ≥0) (n : ℕ)
    (t : Set.Iic i) : Set.Iic i :=
  ⟨min i (rightGrid n t), Set.mem_Iic.mpr (min_le_left _ _)⟩

private lemma measurable_cappedRightGrid (i : ℝ≥0) (n : ℕ) :
    Measurable (cappedRightGrid i n) := by
  unfold cappedRightGrid
  exact Measurable.subtype_mk <|
    (measurable_const.min ((measurable_rightGrid n).comp measurable_subtype_coe))

private lemma tendsto_cappedRightGrid (i : ℝ≥0) (t : Set.Iic i) :
    Filter.Tendsto (fun n ↦ cappedRightGrid i n t) Filter.atTop (𝓝 t) := by
  rw [tendsto_subtype_rng]
  have hc : Filter.Tendsto (fun x : ℝ≥0 ↦ min i x) (𝓝 (t : ℝ≥0))
      (𝓝 (min i (t : ℝ≥0))) :=
    (continuous_const.min continuous_id).continuousAt
  have hcomp := hc.comp (tendsto_rightGrid (t : ℝ≥0))
  change Filter.Tendsto (fun n ↦ min i (rightGrid n (t : ℝ≥0))) Filter.atTop
    (𝓝 (min i (t : ℝ≥0))) at hcomp
  simpa only [cappedRightGrid, min_eq_right (Set.mem_Iic.mp t.property)] using hcomp

private lemma countable_range_cappedRightGrid (i : ℝ≥0) (n : ℕ) :
    (Set.range (cappedRightGrid i n)).Countable := by
  have hsub : Set.range (cappedRightGrid i n) ⊆
      {⟨i, Set.mem_Iic.mpr le_rfl⟩} ∪
        Subtype.val ⁻¹' Set.range (rightGrid n) := by
    rintro y ⟨t, rfl⟩
    by_cases h : i ≤ rightGrid n t
    · left
      apply Subtype.ext
      simp [cappedRightGrid, min_eq_left h]
    · right
      exact ⟨t, by simp [cappedRightGrid, min_eq_right (le_of_not_ge h)]⟩
  refine (Set.countable_singleton _).union ?_ |>.mono hsub
  exact (countable_range_rightGrid n).preimage Subtype.val_injective

private lemma le_cappedRightGrid (i : ℝ≥0) (n : ℕ) (t : Set.Iic i) :
    (t : ℝ≥0) ≤ cappedRightGrid i n t := by
  exact le_min t.property (le_rightGrid n t)

private lemma tendsto_cappedRightGrid_nhdsWithin (i : ℝ≥0) (t : Set.Iic i) :
    Filter.Tendsto (fun n ↦ ((cappedRightGrid i n t : Set.Iic i) : ℝ≥0)) Filter.atTop
      (nhdsWithin (t : ℝ≥0) (Set.Ici t)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.tendsto.comp (tendsto_cappedRightGrid i t)
  · exact Filter.Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (le_cappedRightGrid i n t)

private noncomputable def leftGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.floor (((n + 1 : ℕ) : ℝ≥0) * t) : ℝ≥0) / (n + 1 : ℕ)

private lemma leftGrid_le (n : ℕ) (t : ℝ≥0) : leftGrid n t ≤ t := by
  rw [leftGrid, div_le_iff₀ (by positivity)]
  simpa [mul_comm] using
    Nat.floor_le (show (0 : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) * t by positivity)

private lemma measurable_leftGrid (n : ℕ) : Measurable (leftGrid n) := by
  unfold leftGrid
  fun_prop

private lemma countable_range_leftGrid (n : ℕ) :
    (Set.range (leftGrid n)).Countable := by
  refine (Set.countable_range (fun k : ℕ ↦ (k : ℝ≥0) / (n + 1 : ℕ))).mono ?_
  rintro y ⟨t, rfl⟩
  exact ⟨Nat.floor (((n + 1 : ℕ) : ℝ≥0) * t), rfl⟩

private lemma lt_leftGrid_add (n : ℕ) (t : ℝ≥0) :
    t < leftGrid n t + 1 / (n + 1 : ℕ) := by
  rw [leftGrid, ← add_div]
  rw [lt_div_iff₀ (by positivity)]
  simpa [mul_comm] using Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ≥0) * t)

private lemma tendsto_leftGrid (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ leftGrid n t) Filter.atTop (𝓝 t) := by
  have hδ : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / ((n : ℝ≥0) + 1))
      Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlower : Filter.Tendsto
      (fun n : ℕ ↦ t - (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) Filter.atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
    (fun n ↦ by
      apply tsub_le_iff_right.mpr
      simpa [Nat.cast_add, Nat.cast_one] using (lt_leftGrid_add n t).le)
    (fun n ↦ leftGrid_le n t)

private lemma tendsto_leftGrid_nhdsWithin (t : ℝ≥0) :
    Filter.Tendsto (fun n ↦ leftGrid n t) Filter.atTop (nhdsWithin t (Set.Iic t)) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_leftGrid t,
    Filter.Eventually.of_forall fun n ↦ Set.mem_Iic.mpr (leftGrid_le n t)⟩

private noncomputable def leftGridOnHorizon (i : ℝ≥0) (n : ℕ)
    (t : Set.Iic i) : Set.Iic i :=
  ⟨leftGrid n t, (leftGrid_le n t).trans t.property⟩

private lemma measurable_leftGridOnHorizon (i : ℝ≥0) (n : ℕ) :
    Measurable (leftGridOnHorizon i n) := by
  unfold leftGridOnHorizon
  exact Measurable.subtype_mk ((measurable_leftGrid n).comp measurable_subtype_coe)

private lemma countable_range_leftGridOnHorizon (i : ℝ≥0) (n : ℕ) :
    (Set.range (leftGridOnHorizon i n)).Countable := by
  apply ((countable_range_leftGrid n).preimage Subtype.val_injective).mono
  rintro y ⟨t, rfl⟩
  exact ⟨t, rfl⟩

namespace MeasureTheory

namespace StronglyAdapted

/-- A strongly adapted process indexed by `ℝ≥0` whose every path is right-continuous is jointly
strongly measurable on time times sample space. This is the product-measurability part of the
regular-path acceptance chain. -/
theorem stronglyMeasurable_uncurry_of_rightContinuous
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X)
    (hright : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) :
    StronglyMeasurable (Function.uncurry X) := by
  borelize E
  let U (n : ℕ) (p : ℝ≥0 × Ω) := X (rightGrid n p.1) p.2
  have hU : ∀ n, StronglyMeasurable (U n) := by
    intro n
    let q := rightGrid n
    let _ : Countable (Set.range q) := (countable_range_rightGrid n).to_subtype
    have h_str_meas : StronglyMeasurable
        (fun p : Set.range q × Ω => X p.1.1 p.2) := by
      refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
      · have hswap : (fun p : Set.range q × Ω => X p.1.1 p.2) =
            (fun p : Ω × Set.range q => X p.2.1 p.1) ∘ Prod.swap := rfl
        rw [hswap, measurable_swap_iff]
        exact measurable_from_prod_countable_left fun j =>
          ((hX j.1).mono (ℱ.le j.1)).measurable
      · have hsep : IsSeparable (⋃ j : Set.range q, Set.range (X j.1)) :=
          .iUnion fun j => ((hX j.1).mono (ℱ.le j.1)).isSeparable_range
        apply hsep.mono
        rintro _ ⟨p, rfl⟩
        exact Set.mem_iUnion.2 ⟨p.1, Set.mem_range_self p.2⟩
    have hfactor : U n = (fun p : Set.range q × Ω => X p.1.1 p.2) ∘
        fun p : ℝ≥0 × Ω => (⟨q p.1, Set.mem_range_self p.1⟩, p.2) := rfl
    rw [hfactor]
    exact h_str_meas.comp_measurable <| Measurable.prodMk
      ((((measurable_rightGrid n).comp measurable_fst).subtype_mk)) measurable_snd
  refine stronglyMeasurable_of_tendsto Filter.atTop hU ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (hright p.2 p.1).tendsto.comp (tendsto_rightGrid_nhdsWithin p.1)

/-- Measurable-output specialization of
`StronglyAdapted.stronglyMeasurable_uncurry_of_rightContinuous`. -/
theorem isProductMeasurable_of_rightContinuous
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X)
    (hright : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) :
    ProbabilityTheory.IsProductMeasurable X :=
  (hX.stronglyMeasurable_uncurry_of_rightContinuous hright).measurable

/-- A strongly adapted process indexed by `ℝ≥0` whose every path is right-continuous is strongly
progressive. The right-grid construction is capped at each finite horizon, so every approximating
coordinate is measurable in the horizon sigma-algebra. -/
theorem isStronglyProgressive_of_rightContinuous
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X)
    (hright : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) :
    IsStronglyProgressive ℱ X := by
  intro i
  borelize E
  let U (n : ℕ) (p : Set.Iic i × Ω) := X (cappedRightGrid i n p.1) p.2
  have hU : ∀ n, StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)] (U n) := by
    intro n
    let q := cappedRightGrid i n
    let _ : Countable (Set.range q) := (countable_range_cappedRightGrid i n).to_subtype
    have h_str_meas :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)]
          (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) := by
      refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
      · have hswap :
            (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) =
              (fun p : Ω × Set.range q => X ((p.2.1 : Set.Iic i) : ℝ≥0) p.1) ∘
                Prod.swap := rfl
        rw [hswap, measurable_swap_iff]
        exact measurable_from_prod_countable_left fun j =>
          (hX.stronglyMeasurable_le j.1.property).measurable
      · have hsep : IsSeparable
            (⋃ j : Set.range q, Set.range (X ((j.1 : Set.Iic i) : ℝ≥0))) :=
          .iUnion fun j => (hX.stronglyMeasurable_le j.1.property).isSeparable_range
        apply hsep.mono
        rintro _ ⟨p, rfl⟩
        exact Set.mem_iUnion.2 ⟨p.1, Set.mem_range_self p.2⟩
    have hfactor : U n =
        (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) ∘
          fun p : Set.Iic i × Ω =>
            (⟨q p.1, Set.mem_range_self p.1⟩, p.2) := rfl
    rw [hfactor]
    exact h_str_meas.comp_measurable <| Measurable.prodMk
      ((((measurable_cappedRightGrid i n).comp measurable_fst).subtype_mk)) measurable_snd
  refine stronglyMeasurable_of_tendsto Filter.atTop hU ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (hright p.2 p.1).tendsto.comp (tendsto_cappedRightGrid_nhdsWithin i p.1)

/-- A strongly adapted process indexed by `ℝ≥0` whose every path is left-continuous is strongly
progressive. Floor-grid coordinates remain in the past of the evaluation time. -/
theorem isStronglyProgressive_of_leftContinuous
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X)
    (hleft : ∀ ω, ProbabilityTheory.IsLeftContinuousPath fun t ↦ X t ω) :
    IsStronglyProgressive ℱ X := by
  intro i
  borelize E
  let U (n : ℕ) (p : Set.Iic i × Ω) := X (leftGridOnHorizon i n p.1) p.2
  have hU : ∀ n, StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)] (U n) := by
    intro n
    let q := leftGridOnHorizon i n
    let _ : Countable (Set.range q) := (countable_range_leftGridOnHorizon i n).to_subtype
    have h_str_meas :
        StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ i)]
          (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) := by
      refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
      · have hswap :
            (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) =
              (fun p : Ω × Set.range q => X ((p.2.1 : Set.Iic i) : ℝ≥0) p.1) ∘
                Prod.swap := rfl
        rw [hswap, measurable_swap_iff]
        exact measurable_from_prod_countable_left fun j =>
          (hX.stronglyMeasurable_le j.1.property).measurable
      · have hsep : IsSeparable
            (⋃ j : Set.range q, Set.range (X ((j.1 : Set.Iic i) : ℝ≥0))) :=
          .iUnion fun j => (hX.stronglyMeasurable_le j.1.property).isSeparable_range
        apply hsep.mono
        rintro _ ⟨p, rfl⟩
        exact Set.mem_iUnion.2 ⟨p.1, Set.mem_range_self p.2⟩
    have hfactor : U n =
        (fun p : Set.range q × Ω => X ((p.1.1 : Set.Iic i) : ℝ≥0) p.2) ∘
          fun p : Set.Iic i × Ω =>
            (⟨q p.1, Set.mem_range_self p.1⟩, p.2) := rfl
    rw [hfactor]
    exact h_str_meas.comp_measurable <| Measurable.prodMk
      ((((measurable_leftGridOnHorizon i n).comp measurable_fst).subtype_mk)) measurable_snd
  refine stronglyMeasurable_of_tendsto Filter.atTop hU ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (hleft p.2 p.1).tendsto.comp (tendsto_leftGrid_nhdsWithin p.1)

/-- Under the usual conditions, a strongly adapted process with almost-sure right-continuous
paths has a strongly progressive modification whose paths are right-continuous everywhere. The
version is obtained by setting the process to zero on the single null event of bad paths; usual
completeness places that event in every filtration sigma-algebra. -/
theorem exists_isStronglyProgressive_modification_of_hasRightContinuousPaths
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X) (hℱ : ℱ.IsUsual P)
    (hpaths : ProbabilityTheory.HasRightContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, ProbabilityTheory.IsModification X Y P ∧
      IsStronglyProgressive ℱ Y ∧
      ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ Y t ω := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω}
  have hbad0 : P bad = 0 := ae_iff.mp hpaths
  have hbad_bot : MeasurableSet[ℱ ⊥] bad := hℱ.complete_initial bad hbad0
  let Y (t : ℝ≥0) (ω : Ω) := if ω ∈ bad then 0 else X t ω
  have hYadapted : StronglyAdapted ℱ Y := by
    intro t
    have hbad_t : MeasurableSet[ℱ t] bad := ℱ.mono bot_le bad hbad_bot
    exact StronglyMeasurable.ite hbad_t stronglyMeasurable_const (hX t)
  have hYpaths : ∀ ω, ProbabilityTheory.IsRightContinuousPath fun t ↦ Y t ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · simp only [Y, if_pos hω]
      exact fun _ ↦ continuousWithinAt_const
    · have hreg : ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω := by
        change ¬ (¬ ProbabilityTheory.IsRightContinuousPath fun t ↦ X t ω) at hω
        exact not_not.mp hω
      simpa only [Y, if_neg hω] using hreg
  refine ⟨Y, ?_, hYadapted.isStronglyProgressive_of_rightContinuous hYpaths, hYpaths⟩
  intro t
  filter_upwards [hpaths] with ω hω
  have hωbad : ω ∉ bad := by
    intro hbad
    exact hbad hω
  simp only [Y, if_neg hωbad]

/-- Left-continuous analogue of
`exists_isStronglyProgressive_modification_of_hasRightContinuousPaths`. -/
theorem exists_isStronglyProgressive_modification_of_hasLeftContinuousPaths
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    [PseudoMetrizableSpace E] [Zero E] {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted ℱ X) (hℱ : ℱ.IsUsual P)
    (hpaths : ProbabilityTheory.HasLeftContinuousPaths X P) :
    ∃ Y : ℝ≥0 → Ω → E, ProbabilityTheory.IsModification X Y P ∧
      IsStronglyProgressive ℱ Y ∧
      ∀ ω, ProbabilityTheory.IsLeftContinuousPath fun t ↦ Y t ω := by
  classical
  let bad := {ω | ¬ ProbabilityTheory.IsLeftContinuousPath fun t ↦ X t ω}
  have hbad0 : P bad = 0 := ae_iff.mp hpaths
  have hbad_bot : MeasurableSet[ℱ ⊥] bad := hℱ.complete_initial bad hbad0
  let Y (t : ℝ≥0) (ω : Ω) := if ω ∈ bad then 0 else X t ω
  have hYadapted : StronglyAdapted ℱ Y := by
    intro t
    have hbad_t : MeasurableSet[ℱ t] bad := ℱ.mono bot_le bad hbad_bot
    exact StronglyMeasurable.ite hbad_t stronglyMeasurable_const (hX t)
  have hYpaths : ∀ ω, ProbabilityTheory.IsLeftContinuousPath fun t ↦ Y t ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · simp only [Y, if_pos hω]
      exact fun _ ↦ continuousWithinAt_const
    · have hreg : ProbabilityTheory.IsLeftContinuousPath fun t ↦ X t ω := by
        change ¬ (¬ ProbabilityTheory.IsLeftContinuousPath fun t ↦ X t ω) at hω
        exact not_not.mp hω
      simpa only [Y, if_neg hω] using hreg
  refine ⟨Y, ?_, hYadapted.isStronglyProgressive_of_leftContinuous hYpaths, hYpaths⟩
  intro t
  filter_upwards [hpaths] with ω hω
  have hωbad : ω ∉ bad := by
    intro hbad
    exact hbad hω
  simp only [Y, if_neg hωbad]

end StronglyAdapted

end MeasureTheory
