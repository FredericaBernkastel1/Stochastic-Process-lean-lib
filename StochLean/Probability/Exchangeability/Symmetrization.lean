/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Exchangeability.Basic
public import Mathlib.Data.Fintype.Perm

/-!
# Finite symmetrization

The operator below averages a statistic over the finite permutation group.  It is kept separate
from conditional expectation: the algebraic projection is useful independently of probability.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*}

/-- A statistic on `n` coordinates is symmetric when permuting its inputs does not change it. -/
def IsPermutationInvariant {n : ℕ} (f : (Fin n → E) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → E), f (fun j => x (σ j)) = f x

/-- Average a finite-dimensional statistic over all coordinate permutations. -/
noncomputable def finiteSymmetrization {n : ℕ} (f : (Fin n → E) → ℝ) :
    (Fin n → E) → ℝ := fun x =>
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), f (fun j => x (σ j))

theorem finiteSymmetrization_add {n : ℕ} (f g : (Fin n → E) → ℝ) :
    finiteSymmetrization (f + g) = finiteSymmetrization f + finiteSymmetrization g := by
  ext x
  simp only [finiteSymmetrization, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem finiteSymmetrization_smul {n : ℕ} (c : ℝ) (f : (Fin n → E) → ℝ) :
    finiteSymmetrization (c • f) = c • finiteSymmetrization f := by
  ext x
  simp only [finiteSymmetrization, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Finite symmetrization is invariant under every coordinate permutation. -/
theorem finiteSymmetrization_isPermutationInvariant {n : ℕ} (f : (Fin n → E) → ℝ) :
    IsPermutationInvariant (finiteSymmetrization f) := by
  intro τ x
  unfold finiteSymmetrization
  congr 1
  let e : Equiv.Perm (Equiv.Perm (Fin n)) := Equiv.mulLeft τ.symm
  rw [← e.sum_comp]
  · apply Fintype.sum_congr
    intro σ
    congr 1
    funext j
    simp [e]
  · simp

theorem finiteSymmetrization_eq_self {n : ℕ} {f : (Fin n → E) → ℝ}
    (hf : IsPermutationInvariant f) : finiteSymmetrization f = f := by
  ext x
  rw [finiteSymmetrization]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n), f (fun j => x (σ j)) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
          ∑ _σ : Equiv.Perm (Fin n), f x := by
            congr 1
            exact Fintype.sum_congr _ _ fun σ => hf σ x
    _ = f x := by simp [hc]

/-- Finite symmetrization is an idempotent projection onto symmetric statistics. -/
theorem finiteSymmetrization_idem {n : ℕ} (f : (Fin n → E) → ℝ) :
    finiteSymmetrization (finiteSymmetrization f) = finiteSymmetrization f :=
  finiteSymmetrization_eq_self (finiteSymmetrization_isPermutationInvariant f)

/-- Integrability is preserved by finite symmetrization when every permuted summand is
integrable. -/
theorem integrable_finiteSymmetrization {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (f : (Fin n → E) → ℝ) (X : Ω → Fin n → E)
    (hint : ∀ σ : Equiv.Perm (Fin n),
      Integrable (fun ω => f (fun j => X ω (σ j))) μ) :
    Integrable (finiteSymmetrization f ∘ X) μ := by
  change Integrable (fun ω => (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), f (fun j => X ω (σ j))) μ
  have hs := (integrable_finsetSum' Finset.univ fun σ _ => hint σ).const_mul
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  simpa only [Finset.sum_apply] using hs

end ProbabilityTheory
