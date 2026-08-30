/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Hitting
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Recurrence and extended-valued return times

The return time is never truncated or assigned a default value on the non-return event.  Its mean
therefore lives in `ℝ≥0∞`, and positive recurrence means genuine finiteness of that extended
integral.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Layer-cake identity for an extended natural number. -/
theorem enat_toENNReal_eq_tsum_lt (τ : ℕ∞) :
    (τ : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < τ then 1 else 0 := by
  cases τ using ENat.recTopCoe with
  | top => simp [ENNReal.tsum_const_eq_top_of_ne_zero]
  | coe m =>
      rw [tsum_eq_sum (s := Finset.range m)]
      · simp only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
        calc
          (m : ℝ≥0∞) = ∑ _i ∈ Finset.range m, (1 : ℝ≥0∞) := by simp
          _ = ∑ i ∈ Finset.range m, if i < m then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [if_pos (Finset.mem_range.mp hi)]
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [hn]

/-- Measurability of the event that the strict return time exceeds `n`. -/
theorem measurableSet_firstPositiveHittingTime_gt (x : E) (n : ℕ) :
    MeasurableSet
      {ω : ℕ → E | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω} := by
  let J : Type := {j : ℕ // j ∈ Set.Icc 1 n}
  have hrepr :
      {ω : ℕ → E | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω} =
        (⋃ j : J, {ω : ℕ → E | ω j = x})ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    have hle :
        firstPositiveHittingTime (fun k (z : ℕ → E) => z k) ({x} : Set E) ω ≤ (n : ℕ∞) ↔
          ∃ j : ℕ, j ∈ Set.Icc 1 n ∧
            (fun k (z : ℕ → E) => z k) j ω ∈ ({x} : Set E) := by
      change
        hittingAfter (fun k (z : ℕ → E) => z k) ({x} : Set E) 1 ω ≤ (n : WithTop ℕ) ↔ _
      exact hittingAfter_le_iff
    change
      ((n : ℕ∞) < firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω) ↔
        ∀ j : J, ω (j : ℕ) ≠ x
    rw [lt_iff_not_ge, hle]
    constructor
    · intro h j hjx
      exact h ⟨j, j.property, by simpa using hjx⟩
    · intro h
      rintro ⟨j, hj, hjx⟩
      exact h ⟨j, hj⟩ (by simpa using hjx)
  rw [hrepr]
  exact (MeasurableSet.iUnion fun j : J =>
    (show MeasurableSet ((fun ω : ℕ → E => ω (j : ℕ)) ⁻¹' {x}) from
      (measurable_pi_apply (j : ℕ)) (measurableSet_singleton x))).compl

/-- The extended-real coercion of the canonical strict return time is measurable. -/
theorem measurable_firstPositiveHittingTime_toENNReal (x : E) :
    Measurable fun ω : ℕ → E =>
      (firstPositiveHittingTime (fun k z => z k) {x} ω : ℝ≥0∞) := by
  have hfun :
      (fun ω : ℕ → E =>
        (firstPositiveHittingTime (fun k z => z k) {x} ω : ℝ≥0∞)) =
        fun ω => ∑' n : ℕ,
          if (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω then 1 else 0 := by
    funext ω
    exact enat_toENNReal_eq_tsum_lt _
  rw [hfun]
  apply Measurable.tsum
  intro n
  exact Measurable.ite (measurableSet_firstPositiveHittingTime_gt x n)
    measurable_const measurable_const

/-- Extended mean of the strict-positive return time of the canonical chain. -/
noncomputable def meanReturnTime (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : ℝ≥0∞ :=
  ∫⁻ ω, (firstPositiveHittingTime (fun n z => z n) {x} ω : ℝ≥0∞) ∂markovChainLaw κ x

/-- Tail-sum formula for the strict-positive return time. -/
theorem meanReturnTime_eq_tsum_tail (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    meanReturnTime κ x =
      ∑' n : ℕ, markovChainLaw κ x
        {ω : ℕ → E | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω} := by
  rw [meanReturnTime]
  simp_rw [enat_toENNReal_eq_tsum_lt]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    let A : Set (ℕ → E) :=
      {ω | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω}
    have hA : MeasurableSet A := measurableSet_firstPositiveHittingTime_gt x n
    have hfun :
        (fun ω : ℕ → E =>
          if (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω then 1 else 0) =
          A.indicator (1 : (ℕ → E) → ℝ≥0∞) := by
      funext ω
      simp [A, Set.indicator]
    rw [hfun]
    simpa only [A] using
      (lintegral_indicator_one (μ := markovChainLaw κ x) hA)
  · intro n
    let A : Set (ℕ → E) :=
      {ω | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω}
    have hA : MeasurableSet A := measurableSet_firstPositiveHittingTime_gt x n
    have hfun :
        (fun ω : ℕ → E =>
          if (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω then 1 else 0) =
          A.indicator (1 : (ℕ → E) → ℝ≥0∞) := by
      funext ω
      simp [A, Set.indicator]
    rw [hfun]
    exact (measurable_const.indicator hA).aemeasurable

/-- Recurrence at a state, expressed by almost-sure strict-positive return. -/
def RecurrentAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Prop :=
  returnProbability κ x x = 1

/-- Positive recurrence at a state, expressed by finite extended mean return time. -/
def PositiveRecurrentAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Prop :=
  meanReturnTime κ x < ∞

/-- Finite mean return time forces an almost-sure finite return, hence recurrence. -/
theorem PositiveRecurrentAt.recurrentAt
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (h : PositiveRecurrentAt κ x) : RecurrentAt κ x := by
  rw [PositiveRecurrentAt, meanReturnTime] at h
  have hfinite : ∀ᵐ ω ∂markovChainLaw κ x,
      (firstPositiveHittingTime (fun n z => z n) {x} ω : ℝ≥0∞) < ∞ :=
    ae_lt_top (measurable_firstPositiveHittingTime_toENNReal x) h.ne
  rw [RecurrentAt, returnProbability]
  have hAE :
      {ω | firstPositiveHittingTime (fun n z => z n) {x} ω < ∞} =ᵐ[markovChainLaw κ x]
        (Set.univ : Set (ℕ → E)) := by
    filter_upwards [hfinite] with ω hω
    apply propext
    change
      ((firstPositiveHittingTime (fun n z => z n) {x} ω : ℝ≥0∞) < ∞) ↔ True
    exact ⟨fun _ => trivial, fun _ => hω⟩
  calc
    markovChainLaw κ x
        {ω | firstPositiveHittingTime (fun n z => z n) {x} ω < ∞} =
        markovChainLaw κ x Set.univ := measure_congr hAE
    _ = 1 := measure_univ

/-- Null recurrence is recurrence without finite mean return time. -/
def NullRecurrentAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Prop :=
  RecurrentAt κ x ∧ ¬ PositiveRecurrentAt κ x

/-- Transience at a state, expressed by strict loss of return probability. -/
def TransientAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Prop :=
  returnProbability κ x x < 1

/-- Recurrence and transience are mutually exclusive. -/
theorem RecurrentAt.not_transientAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (h : RecurrentAt κ x) : ¬ TransientAt κ x := by
  rw [RecurrentAt] at h
  rw [TransientAt, h]
  exact lt_irrefl 1

/-- Every state is recurrent or transient. -/
theorem recurrentAt_or_transientAt (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    RecurrentAt κ x ∨ TransientAt κ x := by
  rw [RecurrentAt, TransientAt]
  rcases (returnProbability_le_one κ x x).eq_or_lt with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- A recurrent state is either positive recurrent or null recurrent. -/
theorem RecurrentAt.positive_or_null (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (h : RecurrentAt κ x) : PositiveRecurrentAt κ x ∨ NullRecurrentAt κ x := by
  by_cases hp : PositiveRecurrentAt κ x
  · exact Or.inl hp
  · exact Or.inr ⟨h, hp⟩

/-- Null recurrence excludes positive recurrence. -/
theorem NullRecurrentAt.not_positiveRecurrentAt (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) (h : NullRecurrentAt κ x) : ¬ PositiveRecurrentAt κ x :=
  h.2

/-- The mean return time is at least one. -/
theorem one_le_meanReturnTime (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    1 ≤ meanReturnTime κ x := by
  rw [meanReturnTime]
  have hconst : ∫⁻ _ : ℕ → E, (1 : ℝ≥0∞) ∂markovChainLaw κ x = 1 := by simp
  rw [← hconst]
  exact lintegral_mono (fun ω => by
      simpa only [ENat.toENNReal_one] using
        ENat.toENNReal_mono
          (one_le_firstPositiveHittingTime (fun n (z : ℕ → E) => z n) {x} ω))

end ProbabilityTheory
