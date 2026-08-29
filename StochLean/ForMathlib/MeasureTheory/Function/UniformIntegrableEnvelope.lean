/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Klenke's integrable-envelope presentations of uniform integrability

This file records the two literal sigma-finite formulations in Klenke 6.16--6.17.  They are kept
separate from Mathlib's `UniformIntegrable`, whose standard finite-measure semantics are different
on an infinite measure space.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

noncomputable section

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E]

/-- Klenke 6.16 in epsilon form: one nonnegative integrable spatial envelope makes all positive
remainders `(|f|-g)⁺` uniformly small. -/
def UniformIntegrableBySubtractiveEnvelope (f : ι → α → E) (μ : Measure α) : Prop :=
  (∀ i, Integrable (f i) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∃ g : α → ℝ, Integrable g μ ∧ 0 ≤ᵐ[μ] g ∧
      ∀ i, (∫ x, max (‖f i x‖ - g x) 0 ∂μ) < ε

/-- Klenke 6.17 in epsilon form: one nonnegative integrable spatial envelope makes all integrals
over `{|f|>g}` uniformly small. -/
def UniformIntegrableByTailEnvelope (f : ι → α → E) (μ : Measure α) : Prop :=
  (∀ i, Integrable (f i) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∃ g : α → ℝ, Integrable g μ ∧ 0 ≤ᵐ[μ] g ∧
      ∀ i, (∫ x, if g x < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) < ε

private theorem integrable_subtractiveEnvelope (hf : Integrable (f : α → E) μ)
    (hg : Integrable (g : α → ℝ) μ) (hg0 : 0 ≤ᵐ[μ] g) :
    Integrable (fun x ↦ max (‖f x‖ - g x) 0) μ := by
  apply Integrable.mono' hf.norm
  · fun_prop
  · filter_upwards [hg0] with x hx
    change (0 : ℝ) ≤ g x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (norm_nonneg _)

private theorem integrable_tailEnvelope (hf : Integrable (f : α → E) μ)
    (hg : Integrable (g : α → ℝ) μ) :
    Integrable (fun x ↦ if g x < ‖f x‖ then ‖f x‖ else 0) μ := by
  apply Integrable.mono' hf.norm
  · have hs : NullMeasurableSet {x | g x < ‖f x‖} μ :=
      nullMeasurableSet_lt hg.aestronglyMeasurable.aemeasurable
        hf.norm.aestronglyMeasurable.aemeasurable
    have hm := hf.norm.aestronglyMeasurable.aemeasurable.indicator₀ hs
    apply hm.aestronglyMeasurable.congr
    exact ae_of_all _ fun x ↦ by
      by_cases hx : g x < ‖f x‖ <;> simp [Set.indicator, hx]
  · filter_upwards with x
    split_ifs <;> simp

/-- The literal subtractive and tail envelope formulations of Klenke uniform integrability are
equivalent on arbitrary measure spaces. -/
theorem uniformIntegrableBySubtractiveEnvelope_iff_tailEnvelope
    {f : ι → α → E} :
    UniformIntegrableBySubtractiveEnvelope f μ ↔
      UniformIntegrableByTailEnvelope f μ := by
  constructor
  · rintro ⟨hf, hsub⟩
    refine ⟨hf, fun ε hε ↦ ?_⟩
    obtain ⟨g, hg, hg0, hsmall⟩ := hsub (ε / 3) (by linarith)
    refine ⟨fun x ↦ 2 * g x, hg.const_mul 2, ?_, fun i ↦ ?_⟩
    · filter_upwards [hg0] with x hx
      change (0 : ℝ) ≤ g x at hx
      exact mul_nonneg (by norm_num) hx
    · have htailInt := integrable_tailEnvelope (hf i) (hg.const_mul 2)
      have hresInt := integrable_subtractiveEnvelope (hf i) hg hg0
      have hbound :
          (∫ x, if 2 * g x < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) ≤
            ∫ x, 2 * max (‖f i x‖ - g x) 0 ∂μ := by
        apply integral_mono_ae htailInt (hresInt.const_mul 2)
        filter_upwards [hg0] with x hx
        change (0 : ℝ) ≤ g x at hx
        split_ifs with hlt
        · have hg_le : g x ≤ 2 * g x := by linarith
          have hpos : 0 < ‖f i x‖ - g x := sub_pos.mpr (hg_le.trans_lt hlt)
          rw [max_eq_left hpos.le]
          linarith
        · positivity
      rw [integral_const_mul] at hbound
      linarith [hsmall i]
  · rintro ⟨hf, htail⟩
    refine ⟨hf, fun ε hε ↦ ?_⟩
    obtain ⟨g, hg, hg0, hsmall⟩ := htail ε hε
    refine ⟨g, hg, hg0, fun i ↦ ?_⟩
    have hresInt := integrable_subtractiveEnvelope (hf i) hg hg0
    have htailInt := integrable_tailEnvelope (hf i) hg
    have hbound : (∫ x, max (‖f i x‖ - g x) 0 ∂μ) ≤
        ∫ x, if g x < ‖f i x‖ then ‖f i x‖ else 0 ∂μ := by
      apply integral_mono_ae hresInt htailInt
      filter_upwards [hg0] with x hx
      change (0 : ℝ) ≤ g x at hx
      split_ifs with hlt
      · exact max_le (sub_le_self _ hx) (norm_nonneg _)
      · rw [max_eq_right]
        linarith
    exact hbound.trans_lt (hsmall i)

end

end MeasureTheory
