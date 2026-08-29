/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.UnifTight
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

/-- Klenke's sigma-finite uniform-integrability notion, expressed through Mathlib's canonical
decomposition into uniform absolute continuity and uniform tightness. On finite measure spaces the
tightness conjunct is automatic, while on infinite spaces it records the spatial envelope control
that ordinary `UniformIntegrable` does not provide. -/
def UniformIntegrableByEnvelope (f : ι → α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  UniformIntegrable f p μ ∧ UnifTight f p μ

namespace UniformIntegrableByEnvelope

variable {f g : ι → α → E} {p : ℝ≥0∞}

theorem uniformIntegrable (hf : UniformIntegrableByEnvelope f p μ) :
    UniformIntegrable f p μ := hf.1

theorem unifIntegrable (hf : UniformIntegrableByEnvelope f p μ) :
    UnifIntegrable f p μ := hf.1.unifIntegrable

theorem unifTight (hf : UniformIntegrableByEnvelope f p μ) :
    UnifTight f p μ := hf.2

theorem aestronglyMeasurable (hf : UniformIntegrableByEnvelope f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ := hf.1.aestronglyMeasurable i

theorem memLp (hf : UniformIntegrableByEnvelope f p μ) (i : ι) :
    MemLp (f i) p μ := hf.1.memLp i

theorem ae_eq (hf : UniformIntegrableByEnvelope f p μ)
    (hfg : ∀ i, f i =ᵐ[μ] g i) : UniformIntegrableByEnvelope g p μ :=
  ⟨hf.1.ae_eq hfg, hf.2.aeeq hfg⟩

/-- Envelope uniform integrability is closed under negation. -/
theorem neg (hf : UniformIntegrableByEnvelope f p μ) :
    UniformIntegrableByEnvelope (-f) p μ := by
  refine ⟨⟨fun i ↦ (hf.aestronglyMeasurable i).neg, hf.1.2.1.neg, ?_⟩, hf.2.neg⟩
  obtain ⟨C, hC⟩ := hf.1.2.2
  exact ⟨C, fun i ↦ by simpa using hC i⟩

/-- Envelope uniform integrability is closed under addition. -/
theorem add (hf : UniformIntegrableByEnvelope f p μ)
    (hg : UniformIntegrableByEnvelope g p μ) (hp : 1 ≤ p) :
    UniformIntegrableByEnvelope (f + g) p μ := by
  obtain ⟨Cf, hCf⟩ := hf.1.2.2
  obtain ⟨Cg, hCg⟩ := hg.1.2.2
  refine ⟨⟨fun i ↦ (hf.aestronglyMeasurable i).add (hg.aestronglyMeasurable i),
      hf.1.2.1.add hg.1.2.1 hp (fun i ↦ hf.aestronglyMeasurable i)
        (fun i ↦ hg.aestronglyMeasurable i), ⟨Cf + Cg, fun i ↦ ?_⟩⟩,
    hf.2.add hg.2 (fun i ↦ hf.aestronglyMeasurable i)
      (fun i ↦ hg.aestronglyMeasurable i)⟩
  simpa only [Pi.add_apply, ENNReal.coe_add] using
    (eLpNorm_add_le (hf.aestronglyMeasurable i) (hg.aestronglyMeasurable i) hp).trans
      (add_le_add (hCf i) (hCg i))

/-- Envelope uniform integrability is closed under subtraction. -/
theorem sub (hf : UniformIntegrableByEnvelope f p μ)
    (hg : UniformIntegrableByEnvelope g p μ) (hp : 1 ≤ p) :
    UniformIntegrableByEnvelope (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp

/-- A dominated measurable family inherits envelope uniform integrability. -/
theorem mono_enorm {F : Type*} [NormedAddCommGroup F] {g : ι → α → F}
    (hf : UniformIntegrableByEnvelope f p μ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hgf : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ₑ ≤ ‖f i x‖ₑ) :
    UniformIntegrableByEnvelope g p μ := by
  obtain ⟨C, hC⟩ := hf.1.2.2
  refine ⟨⟨hg, ?_, ⟨C, fun i ↦ (eLpNorm_mono_enorm_ae (hgf i)).trans (hC i)⟩⟩, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hfδ⟩ := hf.1.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    apply (eLpNorm_mono_enorm_ae ?_).trans (hfδ i s hs hμs)
    filter_upwards [hgf i] with x hx
    by_cases hxs : x ∈ s <;> simp [hxs, hx]
  · intro ε hε
    obtain ⟨s, hμs, hfε⟩ := hf.2 hε
    refine ⟨s, hμs, fun i ↦ ?_⟩
    apply (eLpNorm_mono_enorm_ae ?_).trans (hfε i)
    filter_upwards [hgf i] with x hx
    by_cases hxs : x ∈ sᶜ <;> simp [hxs, hx]

/-- A finite family of `Lᵖ` functions is envelope uniformly integrable. -/
theorem finite [Finite ι] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrableByEnvelope f p μ :=
  ⟨uniformIntegrable_finite hp hp' hf, unifTight_finite hp' hf⟩

end UniformIntegrableByEnvelope

/-- On a finite measure space, Mathlib's probability-style uniform integrability already includes
all of Klenke's envelope uniform integrability. -/
theorem uniformIntegrableByEnvelope_iff_uniformIntegrable [IsFiniteMeasure μ]
    {f : ι → α → E} {p : ℝ≥0∞} :
    UniformIntegrableByEnvelope f p μ ↔ UniformIntegrable f p μ := by
  constructor
  · exact UniformIntegrableByEnvelope.uniformIntegrable
  · intro hf
    refine ⟨hf, ?_⟩
    intro ε hε
    refine ⟨Set.univ, measure_ne_top _ _, fun i ↦ ?_⟩
    simp

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
