/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# A de la Vallée-Poussin envelope criterion

This file supplies the generic sufficient direction of the de la Vallée-Poussin criterion. If a
family has uniformly bounded integrals through a nonnegative superlinear envelope, its `L¹` tails
are uniformly small. The result is exposed both for Mathlib's measure-theoretic
`UnifIntegrable` and, on finite measure spaces, its probability-style `UniformIntegrable`.

Convexity and monotonicity of the envelope are useful when constructing an envelope from uniform
integrability, but are not needed for this sufficient direction.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

noncomputable section

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
variable [NormedAddCommGroup E]

/-- A nonnegative envelope is superlinear if `Φ(t) / t` tends to infinity. -/
def SuperlinearEnvelope (Φ : ℝ≥0 → ℝ≥0) : Prop :=
  Tendsto (fun t ↦ Φ t / t) atTop atTop

namespace SuperlinearEnvelope

/-- A uniform bound on superlinear-envelope integrals gives a uniform `L¹` tail estimate. -/
theorem exists_eLpNorm_indicator_le {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (C : ℝ≥0)
    (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ≥0, ∀ i,
      eLpNorm ({x | M ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε := by
  let e : ℝ≥0 := ⟨ε, hε.le⟩
  let R : ℝ≥0 := (C + 1) / e
  have hepos : 0 < e := hε
  have hRpos : 0 < R := div_pos (by positivity) hepos
  have hratio : ∀ᶠ t in atTop, R ≤ Φ t / t := (tendsto_atTop.1 hΦ) R
  obtain ⟨M, hM⟩ := eventually_atTop.1 hratio
  refine ⟨M, fun i ↦ ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ x, ‖{x | M ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ∂μ ≤
        ∫⁻ x, ((R : ℝ≥0∞)⁻¹ * (Φ ‖f i x‖₊ : ℝ≥0∞)) ∂μ := by
      apply lintegral_mono
      intro x
      change ‖{x | M ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ≤
        (R : ℝ≥0∞)⁻¹ * (Φ ‖f i x‖₊ : ℝ≥0∞)
      by_cases hx : M ≤ ‖f i x‖₊
      · have hxmem : x ∈ {y : α | M ≤ ‖f i y‖₊} := hx
        rw [Set.indicator_of_mem hxmem]
        have hquot := hM ‖f i x‖₊ hx
        have hnormpos : 0 < ‖f i x‖₊ := by
          by_contra hn
          have hnzero : ‖f i x‖₊ = 0 := le_antisymm (not_lt.mp hn) zero_le
          rw [hnzero, div_zero] at hquot
          exact (not_le_of_gt hRpos) hquot
        have hmul : R * ‖f i x‖₊ ≤ Φ ‖f i x‖₊ := (le_div_iff₀ hnormpos).mp hquot
        have hnn : ‖f i x‖₊ ≤ R⁻¹ * Φ ‖f i x‖₊ := by
          calc
            ‖f i x‖₊ = R⁻¹ * (R * ‖f i x‖₊) := by field_simp
            _ ≤ R⁻¹ * Φ ‖f i x‖₊ := mul_le_mul_of_nonneg_left hmul zero_le
        rw [enorm_eq_nnnorm, ← ENNReal.coe_inv hRpos.ne', ← ENNReal.coe_mul]
        exact ENNReal.coe_le_coe.mpr hnn
      · have hxmem : x ∉ {y : α | M ≤ ‖f i y‖₊} := hx
        rw [Set.indicator_of_notMem hxmem, enorm_zero]
        exact zero_le
    _ ≤ (R : ℝ≥0∞)⁻¹ * ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ := by
      have hmeas : AEMeasurable (fun x ↦ (Φ ‖f i x‖₊ : ℝ≥0∞)) μ :=
        (hΦmeas.comp_aemeasurable (hf i).nnnorm.aemeasurable).coe_nnreal_ennreal
      exact (lintegral_const_mul'' (R : ℝ≥0∞)⁻¹ hmeas).le
    _ ≤ (R : ℝ≥0∞)⁻¹ * (C : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_left (hC i) zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [show ENNReal.ofReal ε = (e : ℝ≥0∞) by
        have he : NNReal.mk ε hε.le = e := by
          apply NNReal.eq
          rfl
        exact (ENNReal.ofReal_eq_coe_nnreal hε.le).trans (congrArg ((↑) : ℝ≥0 → ℝ≥0∞) he)]
      have hfinal : R⁻¹ * C ≤ e := by
        dsimp [R]
        rw [inv_div]
        calc
          e / (C + 1) * C ≤ e / (C + 1) * (C + 1) := by
            exact mul_le_mul_of_nonneg_left (le_add_right (le_refl C)) zero_le
          _ = e := by field_simp
      rw [← ENNReal.coe_inv hRpos.ne', ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr hfinal

end SuperlinearEnvelope

/-- Superlinear-envelope control implies measure-theoretic uniform integrability in `L¹`. -/
theorem unifIntegrable_of_superlinearEnvelope {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ≥0) (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞)) :
    UnifIntegrable f 1 μ :=
  unifIntegrable_of le_rfl ENNReal.one_ne_top hf fun _ hε ↦
    hΦ.exists_eLpNorm_indicator_le hΦmeas hf C hC hε

/-- On a finite measure space, superlinear-envelope control also implies Mathlib's
probability-style uniform integrability in `L¹`. -/
theorem uniformIntegrable_of_superlinearEnvelope [IsFiniteMeasure μ]
    {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ≥0) (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞)) :
    UniformIntegrable f 1 μ :=
  uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun _ hε ↦
    hΦ.exists_eLpNorm_indicator_le hΦmeas hf C hC hε

end

end MeasureTheory
