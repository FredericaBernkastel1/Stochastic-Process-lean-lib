/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Exchangeability.SigmaFields
public import StochLean.Probability.Exchangeability.Symmetrization
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Symmetrization as conditional expectation

This file isolates the analytic core of Klenke's symmetrized conditional-expectation theorem.
The probability law is required to be invariant under the genuine finite-coordinate actions;
the separate exchangeability-to-invariance bridge can therefore be audited independently.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The first `n` coordinates of a canonical sequence. -/
def prefixCoordinates (n : ℕ) (x : ℕ → E) : Fin n → E := fun j => x j

theorem measurable_prefixCoordinates (n : ℕ) : Measurable (prefixCoordinates (E := E) n) := by
  rw [measurable_pi_iff]
  intro j
  change Measurable (fun x : ℕ → E => x (j : ℕ))
  exact measurable_pi_apply (j : ℕ)

/-- A finite symmetrization is measurable with respect to the corresponding invariant
sigma-field. -/
theorem stronglyMeasurable_finiteSymmetrization_prefix {n : ℕ}
    (f : (Fin n → E) → ℝ) (hf : Measurable f) :
    StronglyMeasurable[prefixInvariantMeasurableSpace (E := E) n]
      (finiteSymmetrization f ∘ prefixCoordinates (E := E) n) := by
  have hambient : Measurable (finiteSymmetrization f ∘ prefixCoordinates (E := E) n) := by
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro σ hσ
    apply hf.comp
    rw [measurable_pi_iff]
    intro j
    change Measurable (fun x : ℕ → E => x (σ j : ℕ))
    exact measurable_pi_apply (σ j : ℕ)
  apply Measurable.stronglyMeasurable
  intro s hs
  refine ⟨hambient hs, ?_⟩
  intro τ hτ
  ext x
  simp only [Set.mem_preimage]
  have hinv := finiteSymmetrization_isPermutationInvariant (E := E) f
    (restrictPrefixPermutation n τ hτ) (prefixCoordinates (E := E) n x)
  have harg : (fun j => prefixCoordinates (E := E) n x
      (restrictPrefixPermutation n τ hτ j)) =
      prefixCoordinates (E := E) n (permuteSequence τ x) := by
    ext j
    rfl
  rw [harg] at hinv
  change finiteSymmetrization f (prefixCoordinates (E := E) n (permuteSequence τ x)) ∈ s ↔
    finiteSymmetrization f (prefixCoordinates (E := E) n x) ∈ s
  rw [hinv]

/-- The analytic core of Klenke's symmetrized conditional-expectation identity.

The two explicit hypotheses have distinct roles: `hpres` is distributional invariance under each
finite permutation, while `hsymm_meas` records measurability with respect to the invariant
sigma-field.  Neither is replaced by pointwise symmetry of the original statistic. -/
theorem finiteSymmetrization_ae_eq_condExp
    {n : ℕ} {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (f : (Fin n → E) → ℝ)
    (hf : Integrable (f ∘ prefixCoordinates (E := E) n) μ)
    (hpres : ∀ σ : Equiv.Perm (Fin n),
      MeasurePreserving
        (permuteSequence (σ.viaEmbedding Fin.valEmbedding)) μ μ)
    (hsymm_meas : StronglyMeasurable[prefixInvariantMeasurableSpace (E := E) n]
      (finiteSymmetrization f ∘ prefixCoordinates (E := E) n)) :
    finiteSymmetrization f ∘ prefixCoordinates (E := E) n =ᵐ[μ]
      μ[f ∘ prefixCoordinates (E := E) n |
        prefixInvariantMeasurableSpace (E := E) n] := by
  let F : (ℕ → E) → ℝ := f ∘ prefixCoordinates (E := E) n
  let G : (ℕ → E) → ℝ := finiteSymmetrization f ∘ prefixCoordinates (E := E) n
  have hm : prefixInvariantMeasurableSpace (E := E) n ≤
      (inferInstance : MeasurableSpace (ℕ → E)) := fun _ hs => hs.1
  have hperm_int : ∀ σ : Equiv.Perm (Fin n),
      Integrable (F ∘ permuteSequence (σ.viaEmbedding Fin.valEmbedding)) μ := by
    intro σ
    exact (hpres σ).integrable_comp_of_integrable hf
  have hG_int : Integrable G μ := by
    apply integrable_finiteSymmetrization f (prefixCoordinates (E := E) n)
    intro σ
    convert hperm_int σ using 1
    ext ω
    congr 1
    funext j
    change ω (σ j : ℕ) = ω ((σ.viaEmbedding Fin.valEmbedding) (j : ℕ))
    exact congrArg ω (Equiv.Perm.viaEmbedding_apply σ Fin.valEmbedding j).symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hμs
    exact hG_int.integrableOn
  · intro s hs hμs
    change ∫ x in s, G x ∂μ = ∫ x in s, F x ∂μ
    have h_each : ∀ σ : Equiv.Perm (Fin n),
        ∫ x in s, f (fun j => x (σ j : ℕ)) ∂μ =
          ∫ x in s, F x ∂μ := by
      intro σ
      let τ : Equiv.Perm ℕ := σ.viaEmbedding Fin.valEmbedding
      let e : (ℕ → E) ≃ᵐ (ℕ → E) := permuteSequenceMeasurableEquiv τ
      have hτprefix : IsPrefixPermutation n τ := by
        intro k hnk
        exact Equiv.Perm.viaEmbedding_apply_of_notMem σ Fin.valEmbedding k (by
          intro hk
          obtain ⟨j, hj⟩ := hk
          exact (not_lt_of_ge hnk) (hj ▸ j.isLt))
      have hpre : permuteSequence τ ⁻¹' s = s := hs.2 τ hτprefix
      have heq : (e : (ℕ → E) → (ℕ → E)) = permuteSequence (E := E) τ := by
        ext x k
        exact congr_fun (permuteSequenceMeasurableEquiv_apply τ x) k
      have he : MeasurableEmbedding (permuteSequence (E := E) τ) := by
        rw [← heq]
        exact e.measurableEmbedding
      have h := (hpres σ).setIntegral_preimage_emb he F s
      change ∫ x in permuteSequence τ ⁻¹' s, F (permuteSequence τ x) ∂μ =
        ∫ x in s, F x ∂μ at h
      rw [hpre] at h
      have hfunperm : (fun x : ℕ → E => F (permuteSequence τ x)) =
          fun x => f fun j => x (σ j : ℕ) := by
        ext x
        change f (fun j : Fin n => x (τ (j : ℕ))) = f (fun j => x (σ j : ℕ))
        congr 1
        funext j
        exact congrArg x (Equiv.Perm.viaEmbedding_apply σ Fin.valEmbedding j)
      rw [hfunperm] at h
      simpa only [F, Function.comp_apply] using h
    simp only [G, finiteSymmetrization, Function.comp_apply, prefixCoordinates]
    rw [integral_const_mul]
    rw [integral_finsetSum]
    · simp_rw [h_each]
      have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      simp [hc]
    · intro σ hσ
      have hfun : (fun a : ℕ → E => f fun j => a (σ j : ℕ)) =
          F ∘ permuteSequence (E := E) (σ.viaEmbedding Fin.valEmbedding) := by
        ext x
        congr 1
        funext j
        exact congrArg x (Equiv.Perm.viaEmbedding_apply σ Fin.valEmbedding j).symm
      rw [hfun]
      exact (hperm_int σ).integrableOn
  · exact hsymm_meas.aestronglyMeasurable

/-- Measurable-statistic form of the symmetrized conditional-expectation theorem. -/
theorem finiteSymmetrization_ae_eq_condExp_of_measurable
    {n : ℕ} {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (f : (Fin n → E) → ℝ) (hf_meas : Measurable f)
    (hf : Integrable (f ∘ prefixCoordinates (E := E) n) μ)
    (hpres : ∀ σ : Equiv.Perm (Fin n),
      MeasurePreserving
        (permuteSequence (σ.viaEmbedding Fin.valEmbedding)) μ μ) :
    finiteSymmetrization f ∘ prefixCoordinates (E := E) n =ᵐ[μ]
      μ[f ∘ prefixCoordinates (E := E) n |
        prefixInvariantMeasurableSpace (E := E) n] :=
  finiteSymmetrization_ae_eq_condExp f hf hpres
    (stronglyMeasurable_finiteSymmetrization_prefix f hf_meas)

/-- Klenke's symmetrized conditional-expectation theorem for an exchangeable canonical law. -/
theorem IsExchangeable.finiteSymmetrization_ae_eq_condExp
    {n : ℕ} {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → E) => x k) μ)
    (f : (Fin n → E) → ℝ) (hf_meas : Measurable f)
    (hf : Integrable (f ∘ prefixCoordinates (E := E) n) μ) :
    finiteSymmetrization f ∘ prefixCoordinates (E := E) n =ᵐ[μ]
      μ[f ∘ prefixCoordinates (E := E) n |
        prefixInvariantMeasurableSpace (E := E) n] :=
  finiteSymmetrization_ae_eq_condExp_of_measurable f hf_meas hf fun σ =>
    hX.measurePreserving_permuteSequence (σ.viaEmbedding Fin.valEmbedding)

end ProbabilityTheory
