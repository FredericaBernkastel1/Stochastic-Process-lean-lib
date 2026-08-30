/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# Exchangeable sequences

Exchangeability is defined through all finite-dimensional distributions.  An index selection is
an embedding `Fin n ↪ ℕ`, so the API does not silently confuse repeated coordinates with a finite
permutation of distinct coordinates.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure Ω}

/-- A sequence is exchangeable when any two ordered finite vectors at distinct indices have the
same law.  This is the finite-dimensional-distribution formulation of invariance under finite
permutations. -/
def IsExchangeable (X : ℕ → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ (n : ℕ) (i j : Fin n ↪ ℕ),
    IdentDistrib (fun ω k => X (i k) ω) (fun ω k => X (j k) ω) μ μ

namespace IsExchangeable

variable {X : ℕ → Ω → E}

theorem finitePermutation (hX : IsExchangeable X μ) (n : ℕ) (i : Fin n ↪ ℕ)
    (σ : Equiv.Perm (Fin n)) :
    IdentDistrib (fun ω j => X (i (σ j)) ω) (fun ω j => X (i j) ω) μ μ :=
  hX n (σ.toEmbedding.trans i) i

set_option linter.unusedFintypeInType false in
/-- Fintype-indexed form of the finite-dimensional exchangeability API. -/
theorem identDistrib_fintype (hX : IsExchangeable X μ) {ι : Type*} [Fintype ι]
    (i j : ι ↪ ℕ) :
    IdentDistrib (fun ω k => X (i k) ω) (fun ω k => X (j k) ω) μ μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hX (Fintype.card ι) (e.toEmbedding.trans i) (e.toEmbedding.trans j)
  have hm : Measurable (fun v : Fin (Fintype.card ι) → E => fun k : ι => v (e.symm k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (e.symm k)
  convert h.comp hm using 1 <;> ext ω k <;> simp [e]

/-- An exchangeable sequence remains exchangeable after injective reindexing. -/
theorem reindex (hX : IsExchangeable X μ) {r : ℕ → ℕ} (hr : Function.Injective r) :
    IsExchangeable (fun n => X (r n)) μ := by
  intro n i j
  let rEmb : ℕ ↪ ℕ := ⟨r, hr⟩
  exact hX n (i.trans rEmb) (j.trans rEmb)

/-- Coordinatewise measurable maps preserve exchangeability. -/
theorem map (hX : IsExchangeable X μ) (g : E → F) (hg : Measurable g) :
    IsExchangeable (fun n => g ∘ X n) μ := by
  intro n i j
  have h := hX n i j
  have hmeas : Measurable (fun x : Fin n → E => fun j => g (x j)) :=
    measurable_pi_lambda _ fun j => hg.comp (measurable_pi_apply j)
  convert h.comp hmeas using 1 <;> rfl

/-- Exchangeability implies equality in law of every two coordinates. -/
theorem identDistrib (hX : IsExchangeable X μ) (a b : ℕ) :
    IdentDistrib (X a) (X b) μ μ := by
  let i : Fin 1 ↪ ℕ := ⟨fun _ => a, fun x y _ => Subsingleton.elim x y⟩
  let j : Fin 1 ↪ ℕ := ⟨fun _ => b, fun x y _ => Subsingleton.elim x y⟩
  have h := (hX 1 i j).comp (measurable_pi_apply (0 : Fin 1))
  convert h using 1 <;> ext ω <;> rfl

end IsExchangeable

/-- Independent, identically distributed coordinates are exchangeable. -/
theorem isExchangeable_of_iIndepFun
    {X : ℕ → Ω → E} (hXm : ∀ n, AEMeasurable (X n) μ)
    (h_indep : iIndepFun X μ) (h_ident : ∀ i j, IdentDistrib (X i) (X j) μ μ) :
    IsExchangeable X μ := by
  intro n i j
  have hi : iIndepFun (fun k : Fin n => X (i k)) μ := h_indep.precomp i.injective
  have hj : iIndepFun (fun k : Fin n => X (j k)) μ := h_indep.precomp j.injective
  refine ⟨aemeasurable_pi_lambda _ fun k => hXm (i k),
    aemeasurable_pi_lambda _ fun k => hXm (j k), ?_⟩
  rw [hi.map_fun_eq_pi_map (fun k => hXm (i k)),
    hj.map_fun_eq_pi_map (fun k => hXm (j k))]
  congr 1
  funext k
  exact (h_ident (i k) (j k)).map_eq

end ProbabilityTheory
