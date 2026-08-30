/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Dirac
import StochLean.Probability.Exchangeability.ConditionalIID

/-!
# Bernoulli de Finetti specialization

This file is an acceptance bridge for the general structural theorem.  It does not provide a
second de Finetti theorem: a probability measure on `Bool` is identified with its mass at `true`,
and the already canonical mixture law is rewritten as a mixture of Bernoulli product measures.
-/

open MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

noncomputable section

/-- The Bernoulli parameter encoded by a probability measure on `Bool`. -/
def bernoulliParameter (θ : ProbabilityMeasure Bool) : I :=
  ⟨(θ : Measure Bool).real {true}, measureReal_nonneg,
    measureReal_le_one⟩

theorem measurable_bernoulliParameter : Measurable bernoulliParameter := by
  apply Measurable.subtype_mk
  apply Measurable.ennreal_toReal
  exact (Measure.measurable_coe (measurableSet_singleton true)).comp measurable_subtype_coe

/-- Every probability measure on `Bool` is the Bernoulli law determined by its mass at `true`. -/
theorem probabilityMeasure_bool_eq_bernoulliMeasure (θ : ProbabilityMeasure Bool) :
    (θ : Measure Bool) = Ber(true, false, bernoulliParameter θ) := by
  apply Measure.ext_of_measureReal_singleton
  intro b
  cases b
  · have hcompl : ({false} : Set Bool) = ({true} : Set Bool)ᶜ := by
      ext x
      cases x <;> simp
    rw [hcompl, measureReal_compl (measurableSet_singleton true)]
    simp only [Bool.univ_eq, ProbabilityMeasure.measureReal_eq_coe_coeFn,
      Bool.compl_singleton, Bool.not_true, MeasurableSpace.measurableSet_top,
      Set.mem_singleton_iff, Bool.true_eq_false, not_false_eq_true,
      bernoulliMeasure_real_apply_of_notMem_of_mem]
    rw [show ({false, true} : Set Bool) = Set.univ by
      ext x
      cases x <;> simp]
    rw [ProbabilityMeasure.coeFn_univ]
    rfl
  · simp [bernoulliParameter]

/-- Bernoulli acceptance form of de Finetti: an exchangeable Boolean sequence has a measurable
parameter `Y ∈ [0,1]`, and every finite tuple law is a mixture of `Ber(Y)` product laws. -/
theorem IsExchangeable.hasBernoulliDeFinettiRepresentation
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Bool} (hX : IsExchangeable X μ)
    (hXm : ∀ n, Measurable (X n)) :
    ∃ Y : Ω → I, Measurable Y ∧
      ∀ (n : ℕ) (i : Fin n ↪ ℕ),
        μ.map (fun ω k => X (i k) ω) =
          μ.bind (fun ω => Measure.pi fun _ : Fin n => Ber(true, false, Y ω)) := by
  obtain ⟨Θ, hΘm, _hXm, hlaw⟩ := hX.hasDeFinettiRepresentation hXm
  refine ⟨bernoulliParameter ∘ Θ, measurable_bernoulliParameter.comp hΘm, ?_⟩
  intro n i
  rw [hlaw n i]
  congr 1
  funext ω
  congr 1
  funext k
  exact probabilityMeasure_bool_eq_bernoulliMeasure (Θ ω)

end

end ProbabilityTheory
