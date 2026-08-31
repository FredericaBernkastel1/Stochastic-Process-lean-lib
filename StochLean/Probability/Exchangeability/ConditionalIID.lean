/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import StochLean.Probability.Exchangeability.Basic
import StochLean.Internal.Exchangeability.DeFinetti.TheoremViaMartingale

/-!
# Conditional iid and directing-measure vocabulary

Conditional laws are stated almost everywhere after evaluating `condDistrib` at the conditioning
random variable. This avoids asserting equality of arbitrary kernel versions at every point.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω E S : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E] [MeasurableSpace S]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A sequence is conditionally iid given `Θ` if its coordinates are conditionally independent
given `σ(Θ)` and their regular conditional distributions agree almost everywhere. -/
structure IsConditionallyIIDGiven (X : ℕ → Ω → E) (Θ : Ω → S) (μ : Measure Ω)
    [IsFiniteMeasure μ] : Prop where
  measurable_conditioner : Measurable Θ
  measurable_coordinate : ∀ n, Measurable (X n)
  condIndependent :
    iCondIndepFun (MeasurableSpace.comap Θ inferInstance)
      measurable_conditioner.comap_le X μ
  condDistrib_eq_zero : ∀ n,
    condDistrib (X n) Θ μ =ᵐ[μ.map Θ] condDistrib (X 0) Θ μ

namespace IsConditionallyIIDGiven

theorem condDistrib_eq {X : ℕ → Ω → E} {Θ : Ω → S}
    (h : IsConditionallyIIDGiven X Θ μ) (i j : ℕ) :
    condDistrib (X i) Θ μ =ᵐ[μ.map Θ] condDistrib (X j) Θ μ :=
  (h.condDistrib_eq_zero i).trans (h.condDistrib_eq_zero j).symm

/-- Evaluated form of conditional identical distribution on the original sample space. -/
theorem condDistrib_comp_ae_eq {X : ℕ → Ω → E} {Θ : Ω → S}
    (h : IsConditionallyIIDGiven X Θ μ) (i j : ℕ) :
    ∀ᵐ ω ∂μ, condDistrib (X i) Θ μ (Θ ω) = condDistrib (X j) Θ μ (Θ ω) :=
  ae_of_ae_map h.measurable_conditioner.aemeasurable (h.condDistrib_eq i j)

/-- Conditional equality of the coordinate laws implies ordinary equality in distribution.
This bridge integrates the regular conditional kernels against the law of the conditioner, so
the a.e. kernel semantics are preserved. -/
theorem identDistrib {X : ℕ → Ω → E} {Θ : Ω → S}
    (h : IsConditionallyIIDGiven X Θ μ) (i j : ℕ) :
    IdentDistrib (X i) (X j) μ μ := by
  have hk : condDistrib (X i) Θ μ =ᵐ[μ.map Θ] condDistrib (X j) Θ μ := by
    exact h.condDistrib_eq i j
  refine ⟨(h.measurable_coordinate i).aemeasurable,
    (h.measurable_coordinate j).aemeasurable, ?_⟩
  calc
    μ.map (X i) = condDistrib (X i) Θ μ ∘ₘ (μ.map Θ) :=
      (condDistrib_comp_map h.measurable_conditioner.aemeasurable
        (h.measurable_coordinate i).aemeasurable).symm
    _ = condDistrib (X j) Θ μ ∘ₘ (μ.map Θ) := Measure.comp_congr hk
    _ = μ.map (X j) := condDistrib_comp_map h.measurable_conditioner.aemeasurable
      (h.measurable_coordinate j).aemeasurable

end IsConditionallyIIDGiven

/-- A probability-measure-valued random variable directs a sequence when, conditionally on that
random measure, the coordinates are independent and every coordinate has that conditional law. -/
structure IsDirectingMeasure (X : ℕ → Ω → E) (Θ : Ω → ProbabilityMeasure E)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Prop where
  measurable_director : Measurable Θ
  measurable_coordinate : ∀ n, Measurable (X n)
  condIndependent :
    iCondIndepFun (MeasurableSpace.comap Θ inferInstance)
      measurable_director.comap_le X μ
  condDistrib_eq : ∀ n,
    condDistrib (X n) Θ μ =ᵐ[μ.map Θ] fun θ => (θ : Measure E)

/-- The public structural de Finetti representation.  The final conjunct states the actual
mixture identity for every ordered tuple of distinct coordinates; it is intentionally stronger
than a name-only conditional-iid predicate and is directly usable by finite-dimensional-law
clients. -/
def HasDeFinettiRepresentation (X : ℕ → Ω → E) (μ : Measure Ω)
    [IsFiniteMeasure μ] : Prop :=
  ∃ Θ : Ω → ProbabilityMeasure E,
    Measurable Θ ∧
    (∀ n, Measurable (X n)) ∧
    ∀ (n : ℕ) (i : Fin n ↪ ℕ),
      μ.map (fun ω k => X (i k) ω) =
        μ.bind (fun ω => Measure.pi fun _ : Fin n => (Θ ω : Measure E))

theorem IsDirectingMeasure.isConditionallyIIDGiven
    {X : ℕ → Ω → E} {Θ : Ω → ProbabilityMeasure E}
    (h : IsDirectingMeasure X Θ μ) : IsConditionallyIIDGiven X Θ μ where
  measurable_conditioner := h.measurable_director
  measurable_coordinate := h.measurable_coordinate
  condIndependent := h.condIndependent
  condDistrib_eq_zero := by
    intro n
    exact (h.condDistrib_eq n).trans (h.condDistrib_eq 0).symm

omit [StandardBorelSpace Ω] [StandardBorelSpace E] [Nonempty E] [IsFiniteMeasure μ] in
/-- StochLean's finite-dimensional formulation implies the permutation formulation consumed by
the internal de Finetti proof engine. -/
private theorem IsExchangeable.toInternal
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ) :
    StochLean.Internal.Exchangeability.Exchangeable μ X := by
  intro n σ
  let i : Fin n ↪ ℕ := ⟨fun k => k.val, Fin.val_injective⟩
  exact (hX.finitePermutation n i σ).map_eq

/-- The structural de Finetti theorem for standard Borel state spaces.  The returned director is
a measurable probability-measure-valued random variable and its product-mixture identity covers
arbitrary ordered finite tuples of distinct indices. -/
theorem IsExchangeable.hasDeFinettiRepresentation [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} (hX : IsExchangeable X μ)
    (hXm : ∀ n, Measurable (X n)) : HasDeFinettiRepresentation X μ := by
  obtain ⟨ν, hνprob, hνmeas, hνlaw⟩ :=
    StochLean.Internal.Exchangeability.DeFinetti.deFinetti X hXm hX.toInternal
  let Θ : Ω → ProbabilityMeasure E := fun ω => ⟨ν ω, hνprob ω⟩
  have hΘmeas : Measurable Θ := by
    apply Measurable.subtype_mk
    exact Measure.measurable_of_measurable_coe ν hνmeas
  refine ⟨Θ, hΘmeas, hXm, ?_⟩
  intro n i
  let j : Fin n ↪ ℕ := ⟨fun k => k.val, Fin.val_injective⟩
  calc
    μ.map (fun ω k => X (i k) ω) = μ.map (fun ω k => X (j k) ω) :=
      (hX n i j).map_eq
    _ = μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω) :=
      hνlaw n (fun k => k.val) Fin.val_strictMono
    _ = μ.bind (fun ω => Measure.pi fun _ : Fin n => (Θ ω : Measure E)) := by rfl

omit [StandardBorelSpace Ω] [StandardBorelSpace E] [Nonempty E] in
/-- Any structural product-mixture representation is exchangeable. -/
theorem HasDeFinettiRepresentation.isExchangeable
    {X : ℕ → Ω → E} (h : HasDeFinettiRepresentation X μ) : IsExchangeable X μ := by
  obtain ⟨Θ, hΘm, hXm, hlaw⟩ := h
  intro n i j
  refine ⟨?_, ?_, (hlaw n i).trans (hlaw n j).symm⟩
  · apply Measurable.aemeasurable
    rw [measurable_pi_iff]
    exact fun k => hXm (i k)
  · apply Measurable.aemeasurable
    rw [measurable_pi_iff]
    exact fun k => hXm (j k)

/-- Standard-Borel de Finetti equivalence in the StochLean API. -/
theorem isExchangeable_iff_hasDeFinettiRepresentation [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} (hXm : ∀ n, Measurable (X n)) :
    IsExchangeable X μ ↔ HasDeFinettiRepresentation X μ := by
  constructor
  · exact fun h => h.hasDeFinettiRepresentation hXm
  · exact HasDeFinettiRepresentation.isExchangeable

end ProbabilityTheory
