/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import Mathlib.Probability.Martingale.Convergence
import Exchangeability.Probability.Martingale.Convergence

/-!
# Reverse martingale adapter

A reverse filtration is represented by an ordinary `Filtration (OrderDual ℕ)`. This file is
intentionally thin: all martingale definitions and conditional-expectation algebra remain the
ordinary Mathlib ones.
-/

namespace MeasureTheory

open Filter
open scoped Topology ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]

/-- Turn a decreasing family of sub-sigma-fields into a filtration indexed by `OrderDual ℕ`. -/
@[instance_reducible]
def antitoneFiltration (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (hG_le : ∀ n, G n ≤ mΩ) : Filtration (OrderDual ℕ) mΩ where
  seq n := G n
  mono' := by
    intro i j hij
    exact hG hij
  le' := hG_le

@[simp]
theorem antitoneFiltration_apply (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (hG_le : ∀ n, G n ≤ mΩ) (n : OrderDual ℕ) :
    antitoneFiltration G hG hG_le n = G n := rfl

/-- A reverse martingale is just a martingale on the order-dual index. -/
abbrev ReverseMartingale [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OrderDual ℕ → Ω → E) (G : ℕ → MeasurableSpace Ω)
    (hG : Antitone G) (hG_le : ∀ n, G n ≤ mΩ) (μ : Measure Ω) : Prop :=
  Martingale f (antitoneFiltration G hG hG_le) μ

/-- Conditional expectations along a decreasing family form a reverse martingale. -/
theorem reverseMartingale_condExp [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Ω → E) (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (hG_le : ∀ n, G n ≤ mΩ) (μ : Measure Ω)
    [SigmaFiniteFiltration μ (antitoneFiltration G hG hG_le)] :
    ReverseMartingale (fun n => μ[g | G n]) G hG hG_le μ := by
  change Martingale
    (fun n : OrderDual ℕ => μ[g | (antitoneFiltration G hG hG_le) n])
      (antitoneFiltration G hG hG_le) μ
  exact martingale_condExp g (antitoneFiltration G hG hG_le) μ

/-- Lévy's downward theorem for real conditional expectations.  This is the StochLean-facing
adapter: the implementation is supplied by the audited exchangeability dependency, while the
statement uses only Mathlib objects. -/
theorem tendsto_ae_condExp_iInf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G : ℕ → MeasurableSpace Ω} (hG : Antitone G)
    (hG_le : ∀ n, G n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | G n] ω) atTop
      (𝓝 (μ[f | ⨅ n, G n] ω)) :=
  Exchangeability.Probability.condExp_tendsto_iInf (μ := μ) hG hG_le f hf

/-- The `L¹` form of Lévy's downward theorem.  It follows from the almost-sure theorem and
uniform integrability of conditional expectations, rather than introducing a second convergence
mechanism. -/
theorem Integrable.tendsto_eLpNorm_condExp_iInf {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    {G : ℕ → MeasurableSpace Ω} (hf : Integrable f μ) (hG : Antitone G)
    (hG_le : ∀ n, G n ≤ (inferInstance : MeasurableSpace Ω)) :
    Tendsto (fun n => eLpNorm (μ[f | G n] - μ[f | ⨅ n, G n]) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
  · intro n
    exact integrable_condExp.aestronglyMeasurable
  · exact memLp_one_iff_integrable.2 integrable_condExp
  · exact (hf.uniformIntegrable_condExp hG_le).unifIntegrable
  · exact tendsto_ae_condExp_iInf hG hG_le f hf

end MeasureTheory
