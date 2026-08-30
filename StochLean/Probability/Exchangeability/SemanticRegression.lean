/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Exchangeability.Bernoulli
import StochLean.Probability.Exchangeability.EmpiricalMeasure
import StochLean.Probability.Exchangeability.InvariantTail
import StochLean.Probability.Exchangeability.Means
import StochLean.Probability.Exchangeability.Symmetrization

/-!
# Semantic regressions for exchangeability

These small models guard the distinctions required by the design: exchangeability is a genuine
finite-dimensional condition, it is weaker than independence, equal marginals are insufficient,
the tail field is only a subfield of the exchangeable field before completion, and empirical
measures never use an empty-sample division fallback.
-/

open MeasureTheory
open scoped ProbabilityTheory ENNReal

namespace ProbabilityTheory

noncomputable section

/-- Fair probability measure on `Bool`. -/
def fairBoolParameter : unitInterval := ⟨2⁻¹, by norm_num⟩

def fairBoolMeasure : Measure Bool := Ber(true, false, fairBoolParameter)

instance : IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

private theorem fairBoolMeasure_singleton_true :
    fairBoolMeasure ({true} : Set Bool) =
      unitInterval.toNNReal fairBoolParameter := by
  exact bernoulliMeasure_apply_of_mem_of_notMem fairBoolParameter
    (measurableSet_singleton true) (by simp) (by simp)

/-- All coordinates are the same nondegenerate Boolean random variable. -/
def commonBoolSequence (_n : ℕ) (ω : Bool) : Bool := ω

theorem commonBoolSequence_exchangeable :
    IsExchangeable commonBoolSequence fairBoolMeasure := by
  intro n i j
  have hm : AEMeasurable (fun ω : Bool => fun _ : Fin n => ω) fairBoolMeasure :=
    (measurable_pi_lambda _ fun _ => measurable_id).aemeasurable
  simpa [commonBoolSequence] using
    (IdentDistrib.refl (μ := fairBoolMeasure) hm)

/-- Exchangeability does not imply independence: the first two coordinates of the common-variable
sequence coincide and their nontrivial event cannot be independent of itself. -/
theorem commonBoolSequence_not_independent :
    ¬ IndepFun (commonBoolSequence 0) (commonBoolSequence 1) fairBoolMeasure := by
  intro h
  have hi := h.measure_inter_preimage_eq_mul
    ({true} : Set Bool) ({true} : Set Bool)
    (measurableSet_singleton true) (measurableSet_singleton true)
  have hcommon0 : commonBoolSequence 0 = id := rfl
  have hcommon1 : commonBoolSequence 1 = id := rfl
  rw [hcommon0, hcommon1, Set.preimage_id, Set.inter_self] at hi
  rw [fairBoolMeasure_singleton_true] at hi
  have ht : unitInterval.toNNReal fairBoolParameter = (2 : NNReal)⁻¹ := by
    ext
    change (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹
    rfl
  rw [ht] at hi
  have hir := congrArg ENNReal.toReal hi
  norm_num at hir

/-- Equal-marginal process used to show that one-dimensional laws do not imply exchangeability. -/
def equalMarginalNonexchangeable (n : ℕ) (ω : Bool) : Bool :=
  if n = 2 then !ω else ω

theorem equalMarginalNonexchangeable_identDistrib (n : ℕ) :
    IdentDistrib (equalMarginalNonexchangeable n) (equalMarginalNonexchangeable 0)
      fairBoolMeasure fairBoolMeasure := by
  by_cases hn : n = 2
  · rw [show equalMarginalNonexchangeable n = (!·) by
          funext ω; simp [equalMarginalNonexchangeable, hn],
        show equalMarginalNonexchangeable 0 = id by
          funext ω; simp [equalMarginalNonexchangeable]]
    refine ⟨(measurable_of_finite _).aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [fairBoolMeasure, map_bernoulliMeasure, Measure.map_id]
    change Ber(false, true, fairBoolParameter) = Ber(true, false, fairBoolParameter)
    rw [bernoulliMeasure_def, bernoulliMeasure_def]
    have hs : unitInterval.symm fairBoolParameter = fairBoolParameter := by
      ext
      norm_num [fairBoolParameter, unitInterval.symm]
    rw [hs]
    ac_rfl
  · rw [show equalMarginalNonexchangeable n = id by
          funext ω; simp [equalMarginalNonexchangeable, hn],
        show equalMarginalNonexchangeable 0 = id by
          funext ω; simp [equalMarginalNonexchangeable]]
    exact IdentDistrib.refl (μ := fairBoolMeasure) measurable_id.aemeasurable

theorem equalMarginalNonexchangeable_not_exchangeable :
    ¬ IsExchangeable equalMarginalNonexchangeable fairBoolMeasure := by
  intro hX
  let i : Fin 2 ↪ ℕ := Fin.valEmbedding
  let j : Fin 2 ↪ ℕ :=
    ⟨fun k => if k = 0 then 0 else 2, by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩
  have hpair := hX 2 i j
  have hj0 : j 0 = 0 := by
    change (if (0 : Fin 2) = 0 then 0 else 2) = 0
    simp
  have hj1 : j 1 = 2 := by
    change (if (1 : Fin 2) = 0 then 0 else 2) = 2
    simp
  have heq := hpair.comp
    ((measurable_pi_apply (0 : Fin 2)).eq (measurable_pi_apply (1 : Fin 2)))
  have hconst : IdentDistrib (fun _ : Bool => True) (fun _ : Bool => False)
      fairBoolMeasure fairBoolMeasure := by
    have hleft : ((fun x : Fin 2 → Bool => x 0 = x 1) ∘
        fun ω k => equalMarginalNonexchangeable (i k) ω) = fun _ : Bool => True := by
      funext ω
      apply propext
      simp [equalMarginalNonexchangeable, i]
    have hright : ((fun x : Fin 2 → Bool => x 0 = x 1) ∘
        fun ω k => equalMarginalNonexchangeable (j k) ω) = fun _ : Bool => False := by
      funext ω
      apply propext
      cases ω <;> simp [equalMarginalNonexchangeable, hj0, hj1]
    rw [hleft, hright] at heq
    exact heq
  have hmass := hconst.measure_mem_eq (measurableSet_singleton True)
  simp [fairBoolMeasure] at hmass

/- The general inclusion is deliberately one-way at raw sigma-field level. -/
example {E : Type*} [MeasurableSpace E] :
    tailMeasurableSpace (E := E) ≤ exchangeableMeasurableSpace (E := E) :=
  tailMeasurableSpace_le_exchangeableMeasurableSpace

/- The empirical API's `n` means a sample of size `n+1`, so its probability instance is available
without any `0⁻¹` interpretation. -/
example {Ω E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (empiricalProbabilityMeasure X n ω) := by infer_instance

/- A symmetric statistic factors through the empirical measure as an actual function equality;
the theorem does not merely assert invariance on a chosen enumeration. -/
example {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {n : ℕ} {f : (Fin (n + 1) → E) → ℝ} (hf : IsPermutationInvariant f) :
    ∃ g : Measure E → ℝ, f = g ∘ empiricalProbabilityMeasureOfTuple :=
  hf.exists_factorThrough_empiricalProbabilityMeasure

/- The raw inclusion is upgraded to equality only modulo the exchangeable law. -/
example {E : Type*} [MeasurableSpace E] {μ : Measure (ℕ → E)}
    [IsProbabilityMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → E) ↦ x k) μ) :
    MeasurableSpace.EqModulo (exchangeableMeasurableSpace (E := E))
      (tailMeasurableSpace (E := E)) μ :=
  exchangeableMeasurableSpace_eq_tail_modulo hX

/- Hewitt--Savage consumes independence plus identical laws and applies to the completed
exchangeable event class through the modulo-tail theorem. -/
example {E : Type*} [MeasurableSpace E] {μ : Measure (ℕ → E)}
    [IsProbabilityMeasure μ]
    (hindep : iIndepFun (fun k (x : ℕ → E) ↦ x k) μ)
    (hident : ∀ i j, IdentDistrib (fun x : ℕ → E ↦ x i) (fun x ↦ x j) μ μ)
    {A : Set (ℕ → E)} (hA : MeasurableSet[exchangeableMeasurableSpace (E := E)] A) :
    μ A = 0 ∨ μ A = 1 :=
  hewittSavage_zero_one hindep hident hA

/- The public de Finetti API is reused by the Boolean acceptance specialization. -/
example {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    (hX : IsExchangeable X μ) (hXm : ∀ n, Measurable (X n)) :
    ∃ Y : Ω → unitInterval, Measurable Y ∧
      ∀ (n : ℕ) (i : Fin n ↪ ℕ),
        μ.map (fun ω k => X (i k) ω) =
          μ.bind (fun ω => Measure.pi fun _ : Fin n => Ber(true, false, Y ω)) :=
  hX.hasBernoulliDeFinettiRepresentation hXm

end

end ProbabilityTheory
