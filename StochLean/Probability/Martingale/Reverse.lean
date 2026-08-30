/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.Convergence

/-!
# Reverse martingale adapter

A reverse filtration is represented by an ordinary `Filtration (OrderDual ℕ)`. This file is
intentionally thin: all martingale definitions and conditional-expectation algebra remain the
ordinary Mathlib ones.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}

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

end MeasureTheory
