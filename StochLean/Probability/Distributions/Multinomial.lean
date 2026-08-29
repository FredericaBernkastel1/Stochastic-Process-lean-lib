/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Multinomial laws

This module provides the finite categorical-count distribution missing from the pinned Mathlib
baseline.  It is defined canonically as the pushforward of a finite product of a categorical
`PMF`; no second product-measure construction is introduced.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory

noncomputable section

variable {κ Ω : Type*} {mκ : MeasurableSpace κ} {mΩ : MeasurableSpace Ω}
  [Fintype κ] [MeasurableSingletonClass κ]

/-- The vector of category counts in a finite sample. -/
def categoricalCounts {n : ℕ} (x : Fin n → κ) : κ → ℕ :=
  by
    classical
    exact fun a ↦ (Finset.univ.filter fun i ↦ x i = a).card

set_option linter.unusedFintypeInType false in
theorem measurable_categoricalCounts {n : ℕ} :
    Measurable (categoricalCounts (κ := κ) (n := n)) :=
  measurable_of_countable _

/-- The one-hot count vector associated with one categorical observation. -/
def categoricalOneHot (a : κ) : κ → ℕ := by
  classical
  exact fun b ↦ if a = b then 1 else 0

/-- The real-valued one-hot vector used by characteristic-function calculations. -/
def categoricalOneHotReal (a : κ) : κ → ℝ := by
  classical
  exact fun b ↦ if a = b then 1 else 0

/-- Coordinatewise coercion of a count vector to a real vector. -/
def categoricalCountsReal (c : κ → ℕ) : κ → ℝ := fun a ↦ c a

set_option linter.unusedFintypeInType false in
theorem measurable_categoricalCountsReal :
    Measurable (categoricalCountsReal (κ := κ)) :=
  measurable_of_countable _

omit [Fintype κ] in
/-- A categorical count vector is the sum of the corresponding one-hot vectors. -/
theorem categoricalCounts_eq_sum_oneHot {n : ℕ} (x : Fin n → κ) :
    categoricalCounts x = ∑ i, categoricalOneHot (x i) := by
  classical
  funext a
  simp only [categoricalCounts, categoricalOneHot, Finset.sum_apply]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

omit [Fintype κ] in
/-- The real cast of a categorical count vector is a finite sum of real one-hot vectors. -/
theorem categoricalCountsReal_comp_eq_sum_oneHotReal {n : ℕ} (x : Fin n → κ) :
    categoricalCountsReal (categoricalCounts x) = ∑ i, categoricalOneHotReal (x i) := by
  classical
  funext a
  have hcount := congrFun (categoricalCounts_eq_sum_oneHot x) a
  simp only [categoricalCountsReal, Finset.sum_apply]
  calc
    (categoricalCounts x a : ℝ) = ((∑ i, categoricalOneHot (x i) a : ℕ) : ℝ) :=
      congrArg ((↑) : ℕ → ℝ) (by simpa only [Finset.sum_apply] using hcount)
    _ = ∑ i, (categoricalOneHot (x i) a : ℝ) := by simp
    _ = ∑ i, categoricalOneHotReal (x i) a := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [categoricalOneHot, categoricalOneHotReal]

namespace PMF

/-- The multinomial law with `n` trials and categorical law `p`, represented as the pushforward
of the finite product law by `categoricalCounts`. -/
def multinomial (p : PMF κ) (n : ℕ) : PMF (κ → ℕ) :=
  let Q := (Measure.pi fun _ : Fin n ↦ p.toMeasure).map
    (categoricalCounts (κ := κ) (n := n))
  let _ : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map measurable_categoricalCounts.aemeasurable
  Q.toPMF

@[simp]
theorem multinomial_toMeasure (p : PMF κ) (n : ℕ) :
    (multinomial p n).toMeasure =
      (Measure.pi fun _ : Fin n ↦ p.toMeasure).map
        (categoricalCounts (κ := κ) (n := n)) :=
  by
    let Q := (Measure.pi fun _ : Fin n ↦ p.toMeasure).map
      (categoricalCounts (κ := κ) (n := n))
    let _ : IsProbabilityMeasure Q :=
      Measure.isProbabilityMeasure_map measurable_categoricalCounts.aemeasurable
    change Q.toPMF.toMeasure = Q
    exact Measure.toPMF_toMeasure Q

end PMF

/-- Independent categorical variables with common law `p` have the multinomial count law. -/
theorem iIndepFun.hasLaw_categoricalCounts {n : ℕ} {P : Measure Ω}
    {X : Fin n → Ω → κ} {p : PMF κ}
    (hIndep : iIndepFun X P) (hLaw : ∀ i, HasLaw (X i) p.toMeasure P) :
    HasLaw (fun ω ↦ categoricalCounts (fun i ↦ X i ω))
      (PMF.multinomial p n).toMeasure P := by
  have hPi := hIndep.hasLaw_pi hLaw
  have hCount : HasLaw (categoricalCounts (κ := κ) (n := n))
      (PMF.multinomial p n).toMeasure (Measure.pi fun _ : Fin n ↦ p.toMeasure) := by
    refine ⟨measurable_categoricalCounts.aemeasurable, ?_⟩
    exact (PMF.multinomial_toMeasure p n).symm
  simpa only [Function.comp_def] using hCount.comp hPi

/-- Mapping an independent i.i.d. sample through a finite measurable categorization gives the
multinomial law of the category counts. -/
theorem iIndepFun.hasLaw_multinomial_of_comp {S : Type*} {mS : MeasurableSpace S}
    {n : ℕ} {P : Measure Ω} {μ : Measure S} {X : Fin n → Ω → S}
    {c : S → κ} {p : PMF κ} (hIndep : iIndepFun X P)
    (hLaw : ∀ i, HasLaw (X i) μ P) (hcmeas : Measurable c)
    (hc : HasLaw c p.toMeasure μ) :
    HasLaw (fun ω ↦ categoricalCounts (fun i ↦ c (X i ω)))
      (PMF.multinomial p n).toMeasure P := by
  have hIndep' : iIndepFun (fun i ↦ c ∘ X i) P :=
    hIndep.comp (fun _ ↦ c) (fun _ ↦ hcmeas)
  have hLaw' : ∀ i, HasLaw (c ∘ X i) p.toMeasure P :=
    fun i ↦ hc.comp (hLaw i)
  simpa only [Function.comp_def] using hIndep'.hasLaw_categoricalCounts hLaw'

/-- The total number of observations recorded by a categorical count vector is the sample size. -/
@[simp]
theorem sum_categoricalCounts {n : ℕ} (x : Fin n → κ) :
    ∑ a, categoricalCounts x a = n := by
  classical
  change ∑ a, (Finset.univ.filter fun i ↦ x i = a).card = n
  simpa using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ x)

end

end ProbabilityTheory
