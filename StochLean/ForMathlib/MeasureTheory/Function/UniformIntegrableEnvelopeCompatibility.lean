/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.DeLaValleePoussin
public import StochLean.ForMathlib.MeasureTheory.Function.UniformIntegrableEnvelope
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Compatibility for Klenke's envelope uniform integrability

This file connects the literal formulations in Klenke 6.16--6.17 to Mathlib's finite-measure
uniform-integrability predicate and to StochLean's sigma-finite canonical package.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

noncomputable section

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E]

/-- On a finite measure space, Mathlib uniform integrability supplies Klenke's literal tail
envelopes. A constant envelope is enough in this direction. -/
theorem UniformIntegrable.uniformIntegrableByTailEnvelope [IsFiniteMeasure μ]
    {f : ι → α → E} (hf : UniformIntegrable f 1 μ) :
    UniformIntegrableByTailEnvelope f μ := by
  refine ⟨fun i ↦ memLp_one_iff_integrable.mp (hf.memLp i), fun ε hε ↦ ?_⟩
  obtain ⟨C, hC⟩ :=
    ((uniformIntegrable_iff (f := f) (μ := μ) le_rfl ENNReal.one_ne_top).mp hf).2
      (ε / 2) (by linarith)
  refine ⟨fun _ ↦ (C : ℝ), (integrable_const (C : ℝ)),
    Filter.Eventually.of_forall fun _ ↦ C.coe_nonneg, fun i ↦ ?_⟩
  have hfi : Integrable (f i) μ := memLp_one_iff_integrable.mp (hf.memLp i)
  have htail : Integrable (fun x ↦ if (C : ℝ) < ‖f i x‖ then ‖f i x‖ else 0) μ := by
    apply Integrable.mono' hfi.norm
    · have hs : NullMeasurableSet {x | (C : ℝ) < ‖f i x‖} μ :=
        nullMeasurableSet_lt aemeasurable_const hfi.norm.aestronglyMeasurable.aemeasurable
      have hm := hfi.norm.aestronglyMeasurable.aemeasurable.indicator₀ hs
      apply hm.aestronglyMeasurable.congr
      exact ae_of_all _ fun x ↦ by
        by_cases hx : (C : ℝ) < ‖f i x‖ <;> simp [Set.indicator, hx]
    · filter_upwards with x
      split_ifs <;> simp
  have hpoint : ∀ x,
      (if (C : ℝ) < ‖f i x‖ then ‖f i x‖ else 0) ≤
        ‖({x | C ≤ ‖f i x‖₊}.indicator (f i)) x‖ := by
    intro x
    by_cases hx : (C : ℝ) < ‖f i x‖
    · have hmem : x ∈ {x | C ≤ ‖f i x‖₊} := by
        rw [Set.mem_ofPred_eq, ← NNReal.coe_le_coe, coe_nnnorm]
        exact hx.le
      simp [hx, hmem]
    · rw [if_neg hx]
      positivity
  have hmeas : NullMeasurableSet {x | C ≤ ‖f i x‖₊} μ :=
    nullMeasurableSet_le aemeasurable_const
      (hf.aestronglyMeasurable i).nnnorm.aemeasurable
  have hindicator : Integrable ({x | C ≤ ‖f i x‖₊}.indicator (f i)) μ :=
    hfi.indicator₀ hmeas
  have hleReal :
      (∫ x, if (C : ℝ) < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) ≤
        ∫ x, ‖({x | C ≤ ‖f i x‖₊}.indicator (f i)) x‖ ∂μ := by
    apply integral_mono_ae htail hindicator.norm
    exact ae_of_all _ hpoint
  have hle : ENNReal.ofReal (∫ x, if (C : ℝ) < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) ≤
      eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hindicator]
    exact ENNReal.ofReal_le_ofReal hleReal
  have hof : ENNReal.ofReal (∫ x, if (C : ℝ) < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) ≤
      ENNReal.ofReal (ε / 2) := hle.trans (hC i)
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ ε / 2)] at hof
  linarith

private theorem eLpNorm_indicator_le_tailEnvelope_add
    {f : α → E} {g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : 0 ≤ᵐ[μ] g) {s : Set α} (hs : NullMeasurableSet s μ) :
    eLpNorm (s.indicator f) 1 μ ≤
      ENNReal.ofReal (∫ x, if g x < ‖f x‖ then ‖f x‖ else 0 ∂μ) +
        eLpNorm (s.indicator g) 1 μ := by
  let tail : α → ℝ := fun x ↦ if g x < ‖f x‖ then ‖f x‖ else 0
  have htail : Integrable tail μ := by
    apply Integrable.mono' hf.norm
    · have ht : NullMeasurableSet {x | g x < ‖f x‖} μ :=
        nullMeasurableSet_lt hg.aestronglyMeasurable.aemeasurable
          hf.norm.aestronglyMeasurable.aemeasurable
      have hm := hf.norm.aestronglyMeasurable.aemeasurable.indicator₀ ht
      apply hm.aestronglyMeasurable.congr
      exact ae_of_all _ fun x ↦ by
        by_cases hx : g x < ‖f x‖ <;> simp [tail, Set.indicator, hx]
    · filter_upwards with x
      simp only [tail]
      split_ifs <;> simp
  have hsg : Integrable (s.indicator g) μ := hg.indicator₀ hs
  have hmono : ∀ᵐ x ∂μ,
      ‖s.indicator f x‖ₑ ≤ ‖tail x + s.indicator g x‖ₑ := by
    filter_upwards [hg0] with x hx
    change (0 : ℝ) ≤ g x at hx
    have hreal : ‖s.indicator f x‖ ≤ |tail x + s.indicator g x| := by
      by_cases hxs : x ∈ s
      · by_cases hfg : g x < ‖f x‖
        · simp only [tail, hfg, ↓reduceIte, Set.indicator_of_mem hxs]
          rw [abs_of_nonneg (add_nonneg (norm_nonneg _) hx)]
          exact le_add_of_nonneg_right hx
        · have hgf : ‖f x‖ ≤ g x := le_of_not_gt hfg
          simp [tail, hxs, hfg, abs_of_nonneg hx, hgf]
      · simp [tail, hxs]
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    exact hreal
  calc
    eLpNorm (s.indicator f) 1 μ ≤ eLpNorm (tail + s.indicator g) 1 μ :=
      eLpNorm_mono_enorm_ae hmono
    _ ≤ eLpNorm tail 1 μ + eLpNorm (s.indicator g) 1 μ :=
      eLpNorm_add_le htail.aestronglyMeasurable hsg.aestronglyMeasurable le_rfl
    _ = ENNReal.ofReal (∫ x, if g x < ‖f x‖ then ‖f x‖ else 0 ∂μ) +
        eLpNorm (s.indicator g) 1 μ := by
      congr 1
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm htail]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      simp only [tail, Real.norm_eq_abs]
      split_ifs <;> simp

/-- Klenke's literal tail-envelope condition implies the canonical sigma-finite package: uniform
absolute continuity, a common `L¹` bound, and uniform spatial tightness. -/
theorem UniformIntegrableByTailEnvelope.uniformIntegrableByEnvelope
    {f : ι → α → E} (hf : UniformIntegrableByTailEnvelope f μ) :
    UniformIntegrableByEnvelope f 1 μ := by
  rcases hf with ⟨hfint, htail⟩
  have hUI : UniformIntegrable f 1 μ := by
    refine ⟨fun i ↦ (hfint i).aestronglyMeasurable, ?_, ?_⟩
    · intro ε hε
      obtain ⟨g, hg, hg0, hsmall⟩ := htail (ε / 2) (by linarith)
      have hgUI : UniformIntegrable (fun _ : ι ↦ g) 1 μ :=
        uniformIntegrable_const le_rfl ENNReal.one_ne_top
          (memLp_one_iff_integrable.mpr hg)
      obtain ⟨δ, hδ, hgδ⟩ :=
        (hgUI.unifIntegrable) (by linarith : 0 < ε / 2)
      refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
      have hbound := eLpNorm_indicator_le_tailEnvelope_add (hfint i) hg hg0
        hs.nullMeasurableSet
      refine hbound.trans ?_
      calc
        ENNReal.ofReal (∫ x, if g x < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) +
            eLpNorm (s.indicator g) 1 μ ≤
            ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal (hsmall i).le) (hgδ i s hs hμs)
        _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
    · obtain ⟨g, hg, hg0, hsmall⟩ := htail 1 one_pos
      let B : ENNReal := ENNReal.ofReal 1 + eLpNorm g 1 μ
      have hBtop : B ≠ ⊤ := by
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
          (memLp_one_iff_integrable.mpr hg).eLpNorm_lt_top.ne⟩
      refine ⟨B.toNNReal, fun i ↦ ?_⟩
      have hbound := eLpNorm_indicator_le_tailEnvelope_add (hfint i) hg hg0
        (s := Set.univ) nullMeasurableSet_univ
      simp only [Set.indicator_univ] at hbound
      refine hbound.trans ?_
      rw [ENNReal.coe_toNNReal hBtop]
      exact add_le_add (ENNReal.ofReal_le_ofReal (hsmall i).le) le_rfl
  refine ⟨hUI, ?_⟩
  rw [unifTight_iff_real]
  intro ε hε
  obtain ⟨g, hg, hg0, hsmall⟩ := htail (ε / 2) (by linarith)
  have hgTight : UnifTight (fun _ : ι ↦ g) 1 μ :=
    unifTight_const ENNReal.one_ne_top (memLp_one_iff_integrable.mpr hg)
  obtain ⟨s, hs, hμs, hgsmall⟩ := hgTight.exists_measurableSet_indicator
    (ε := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  refine ⟨s, hμs.ne, fun i ↦ ?_⟩
  have hbound := eLpNorm_indicator_le_tailEnvelope_add (hfint i) hg hg0
    hs.compl.nullMeasurableSet
  refine hbound.trans ?_
  calc
    ENNReal.ofReal (∫ x, if g x < ‖f i x‖ then ‖f i x‖ else 0 ∂μ) +
        eLpNorm (sᶜ.indicator g) 1 μ ≤
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (ENNReal.ofReal_le_ofReal (hsmall i).le) (hgsmall i)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

/-- The canonical sigma-finite package supplies Klenke's literal tail envelopes.  The envelope is
a constant height on a common finite-measure core; the two errors are the magnitude tail and the
spatial tail. -/
theorem UniformIntegrableByEnvelope.uniformIntegrableByTailEnvelope
    {f : ι → α → E} (hf : UniformIntegrableByEnvelope f 1 μ) :
    UniformIntegrableByTailEnvelope f μ := by
  refine ⟨fun i ↦ memLp_one_iff_integrable.mp (hf.memLp i), fun ε hε ↦ ?_⟩
  obtain ⟨C, hC⟩ := hf.uniformIntegrable.spec one_ne_zero ENNReal.one_ne_top
    (by linarith : 0 < ε / 3)
  obtain ⟨s, hs, hμs, hout⟩ := hf.unifTight.exists_measurableSet_indicator
    (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  let g : α → ℝ := s.indicator fun _ ↦ (C : ℝ)
  have hg : Integrable g μ := by
    exact (integrableOn_const (C := (C : ℝ)) hμs.ne).integrable_indicator hs
  have hg0 : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall fun x ↦ by
    simp only [g]
    by_cases hxs : x ∈ s <;> simp [hxs, C.coe_nonneg]
  refine ⟨g, hg, hg0, fun i ↦ ?_⟩
  let tail : α → ℝ := fun x ↦ if g x < ‖f i x‖ then ‖f i x‖ else 0
  let high : α → E := {x | C ≤ ‖f i x‖₊}.indicator (f i)
  let outside : α → E := sᶜ.indicator (f i)
  have hfi : Integrable (f i) μ := memLp_one_iff_integrable.mp (hf.memLp i)
  have htail : Integrable tail μ := by
    apply Integrable.mono' hfi.norm
    · have ht : NullMeasurableSet {x | g x < ‖f i x‖} μ :=
        nullMeasurableSet_lt hg.aestronglyMeasurable.aemeasurable
          hfi.norm.aestronglyMeasurable.aemeasurable
      have hm := hfi.norm.aestronglyMeasurable.aemeasurable.indicator₀ ht
      apply hm.aestronglyMeasurable.congr
      exact ae_of_all _ fun x ↦ by
        by_cases hx : g x < ‖f i x‖ <;> simp [tail, Set.indicator, hx]
    · filter_upwards with x
      simp only [tail]
      split_ifs <;> simp
  have hhighSet : NullMeasurableSet {x | C ≤ ‖f i x‖₊} μ :=
    nullMeasurableSet_le aemeasurable_const
      (hf.aestronglyMeasurable i).nnnorm.aemeasurable
  have hhigh : Integrable high μ := hfi.indicator₀ hhighSet
  have houtInt : Integrable outside μ := hfi.indicator hs.compl
  have hpoint : ∀ x, tail x ≤ ‖high x‖ + ‖outside x‖ := by
    intro x
    by_cases hxs : x ∈ s
    · by_cases hbig : (C : ℝ) < ‖f i x‖
      · have hmem : x ∈ {x | C ≤ ‖f i x‖₊} := by
          rw [Set.mem_ofPred_eq, ← NNReal.coe_le_coe, coe_nnnorm]
          exact hbig.le
        simp [tail, g, high, outside, hxs, hbig, hmem]
      · simp [tail, g, high, outside, hxs, hbig]
    · by_cases hpos : 0 < ‖f i x‖
      · by_cases hmem : x ∈ {x | C ≤ ‖f i x‖₊}
        · simp [tail, g, high, outside, hxs, hpos, hmem]
        · simp [tail, g, high, outside, hxs, hpos, hmem]
      · have hzero : ‖f i x‖ = 0 := le_antisymm (le_of_not_gt hpos) (norm_nonneg _)
        simp [tail, g, high, outside, hxs, hzero]
  have hbound : (∫ x, tail x ∂μ) ≤
      (∫ x, ‖high x‖ ∂μ) + ∫ x, ‖outside x‖ ∂μ := by
    rw [← integral_add hhigh.norm houtInt.norm]
    exact integral_mono htail (hhigh.norm.add houtInt.norm) hpoint
  have hhighBound : (∫ x, ‖high x‖ ∂μ) ≤ ε / 3 := by
    have hi := hC i
    change eLpNorm high 1 μ ≤ ENNReal.ofReal (ε / 3) at hi
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hhigh] at hi
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ ε / 3)).mp hi
  have houtBound : (∫ x, ‖outside x‖ ∂μ) ≤ ε / 3 := by
    have hi := hout i
    change eLpNorm outside 1 μ ≤ ENNReal.ofReal (ε / 3) at hi
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm houtInt] at hi
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ ε / 3)).mp hi
  change (∫ x, tail x ∂μ) < ε
  linarith

/-- On arbitrary measure spaces, Klenke's two literal envelope formulations and the canonical
`UniformIntegrable ∧ UnifTight` package have exactly the same `L¹` semantics. -/
theorem uniformIntegrableByTailEnvelope_iff_uniformIntegrableByEnvelope
    {f : ι → α → E} :
    UniformIntegrableByTailEnvelope f μ ↔ UniformIntegrableByEnvelope f 1 μ :=
  ⟨UniformIntegrableByTailEnvelope.uniformIntegrableByEnvelope,
    UniformIntegrableByEnvelope.uniformIntegrableByTailEnvelope⟩

/-- Finite-measure compatibility requested by Klenke 6.17: the literal tail-envelope definition
coincides with Mathlib's standard uniform integrability. -/
theorem uniformIntegrableByTailEnvelope_iff_uniformIntegrable [IsFiniteMeasure μ]
    {f : ι → α → E} :
    UniformIntegrableByTailEnvelope f μ ↔ UniformIntegrable f 1 μ := by
  rw [uniformIntegrableByTailEnvelope_iff_uniformIntegrableByEnvelope,
    uniformIntegrableByEnvelope_iff_uniformIntegrable]

/-- Klenke 6.24 in the canonical decomposition: envelope uniform integrability is exactly
measurability, uniform absolute continuity of the `L¹` integrals, a common `L¹` bound, and uniform
spatial tightness. -/
theorem klenke_uniformIntegrable_iff_uniformAbsoluteContinuity_and_tightness
    {f : ι → α → E} :
    UniformIntegrableByTailEnvelope f μ ↔
      (∀ i, AEStronglyMeasurable (f i) μ) ∧ UnifIntegrable f 1 μ ∧
        (∃ C : NNReal, ∀ i, eLpNorm (f i) 1 μ ≤ C) ∧ UnifTight f 1 μ := by
  rw [uniformIntegrableByTailEnvelope_iff_uniformIntegrableByEnvelope]
  constructor
  · rintro ⟨⟨hmeas, huac, hbound⟩, htight⟩
    exact ⟨hmeas, huac, hbound, htight⟩
  · rintro ⟨hmeas, huac, hbound, htight⟩
    exact ⟨⟨hmeas, huac, hbound⟩, htight⟩

/-- Quantitative absolute continuity of a finite measure.  This is the epsilon--delta form used
to pass from a finite-measure core to an equivalent finite reference measure. -/
theorem Measure.AbsolutelyContinuous.measure_le_of_measure_le {ν : Measure α}
    [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, MeasurableSet s →
      ν s ≤ ENNReal.ofReal δ → μ s ≤ ENNReal.ofReal ε := by
  let g : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hg : Integrable g ν := Measure.integrable_toReal_rnDeriv
  obtain ⟨δ, hδ, hsmall⟩ :=
    (unifIntegrable_const (ι := Unit) le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr hg)) hε
  refine ⟨δ, hδ, fun s hs hνs ↦ ?_⟩
  have hnorm := hsmall () s hs hνs
  have hrestrict : Integrable (s.indicator g) ν := hg.indicator hs
  have heLp : eLpNorm (s.indicator g) 1 ν = μ s := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hrestrict]
    have hnormeq : (fun x ↦ ‖s.indicator g x‖) = s.indicator g := by
      funext x
      by_cases hx : x ∈ s <;> simp [g, hx]
    rw [hnormeq, integral_indicator hs]
    change ENNReal.ofReal (∫ x in s, (μ.rnDeriv ν x).toReal ∂ν) = μ s
    rw [Measure.setIntegral_toReal_rnDeriv_eq_withDensity' hs,
      Measure.withDensity_rnDeriv_eq _ _ hμν, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  rwa [heLp] at hnorm

/-- Klenke 6.24(ii): one fixed nonnegative integrable density controls the integrals of every
member of the family on all measurable sets. -/
def UniformAbsoluteContinuityByDensity (f : ι → α → E) (μ : Measure α) : Prop :=
  ∃ h : α → ℝ, Integrable h μ ∧ 0 ≤ᵐ[μ] h ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i s,
      MeasurableSet s → (∫ x in s, h x ∂μ) < δ →
        (∫ x in s, ‖f i x‖ ∂μ) < ε

/-- The literal right-hand side of Klenke 6.24: the family lies in `L¹`, has a common `L¹`
bound, and satisfies the fixed-density absolute-continuity condition. -/
def KlenkeUniformIntegrableByDensity (f : ι → α → E) (μ : Measure α) : Prop :=
  (∀ i, Integrable (f i) μ) ∧
    (∃ C : ℝ, ∀ i, (∫ x, ‖f i x‖ ∂μ) ≤ C) ∧
      UniformAbsoluteContinuityByDensity f μ

private lemma eLpNorm_indicator_one_eq_ofReal_integral_norm
    {f : α → E} (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) 1 μ = ENNReal.ofReal (∫ x in s, ‖f x‖ ∂μ) := by
  have hfi : Integrable (s.indicator f) μ := hf.indicator hs
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hfi]
  have hfun : (fun x ↦ ‖s.indicator f x‖) = s.indicator (fun x ↦ ‖f x‖) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hfun, integral_indicator hs]

private lemma eLpNorm_one_eq_ofReal_integral_norm
    {f : α → E} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) := by
  simpa using eLpNorm_indicator_one_eq_ofReal_integral_norm hf MeasurableSet.univ

private lemma integral_norm_le_of_eLpNorm_indicator_le
    {f : α → E} (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : eLpNorm (s.indicator f) 1 μ ≤ ENNReal.ofReal ε) :
    (∫ x in s, ‖f x‖ ∂μ) ≤ ε := by
  rw [eLpNorm_indicator_one_eq_ofReal_integral_norm hf hs] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp h

private lemma eLpNorm_indicator_le_of_integral_norm_lt
    {f : α → E} (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s)
    {ε : ℝ} (h : (∫ x in s, ‖f x‖ ∂μ) < ε) :
    eLpNorm (s.indicator f) 1 μ ≤ ENNReal.ofReal ε := by
  rw [eLpNorm_indicator_one_eq_ofReal_integral_norm hf hs]
  exact ENNReal.ofReal_le_ofReal h.le

/-- Klenke 6.24 in its literal fixed-density form.  On a sigma-finite space, envelope uniform
integrability is equivalent to a common `L¹` bound together with uniform absolute continuity
measured by one fixed nonnegative integrable density. -/
theorem uniformIntegrableByTailEnvelope_iff_klenkeUniformIntegrableByDensity
    [SigmaFinite μ] {f : ι → α → E} :
    UniformIntegrableByTailEnvelope f μ ↔ KlenkeUniformIntegrableByDensity f μ := by
  rw [uniformIntegrableByTailEnvelope_iff_uniformIntegrableByEnvelope]
  constructor
  · intro hf
    refine ⟨fun i ↦ memLp_one_iff_integrable.mp (hf.memLp i), ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hf.uniformIntegrable.2.2
      refine ⟨C, fun i ↦ ?_⟩
      have hi := hC i
      rw [eLpNorm_one_eq_ofReal_integral_norm
        (memLp_one_iff_integrable.mp (hf.memLp i))] at hi
      exact (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp (by simpa using hi)
    · let ν : Measure α := μ.toFinite
      let h : α → ℝ := fun x ↦ (ν.rnDeriv μ x).toReal
      have hh : Integrable h μ := Measure.integrable_toReal_rnDeriv
      refine ⟨h, hh, Filter.Eventually.of_forall fun x ↦ ENNReal.toReal_nonneg,
        fun ε hε ↦ ?_⟩
      obtain ⟨B, hB, hμB, hout⟩ := hf.unifTight.exists_measurableSet_indicator
        (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      obtain ⟨η, hη, huac⟩ := hf.uniformIntegrable.unifIntegrable
        (by linarith : 0 < ε / 3)
      let lam : Measure α := μ.restrict B
      let _ : IsFiniteMeasure lam := ⟨by simpa [lam] using hμB⟩
      have hlamν : lam ≪ ν :=
        (Measure.restrict_le_self.absolutelyContinuous).trans (absolutelyContinuous_toFinite μ)
      obtain ⟨δ, hδ, hδac⟩ := hlamν.measure_le_of_measure_le hη
      refine ⟨δ, hδ, fun i s hs hhs ↦ ?_⟩
      have hνsreal : ν.real s < δ := by
        change (∫ x in s, (ν.rnDeriv μ x).toReal ∂μ) < δ at hhs
        rw [Measure.setIntegral_toReal_rnDeriv_eq_withDensity' hs,
          Measure.withDensity_rnDeriv_eq ν μ (toFinite_absolutelyContinuous μ)] at hhs
        exact hhs
      have hνs : ν s ≤ ENNReal.ofReal δ := by
        rw [← ENNReal.toReal_le_toReal (measure_ne_top ν s) ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hδ.le]
        exact hνsreal.le
      have hlams := hδac s hs hνs
      have hμinter : μ (s ∩ B) ≤ ENNReal.ofReal η := by
        simpa only [lam, Measure.restrict_apply hs] using hlams
      have hin := huac i (s ∩ B) (hs.inter hB) hμinter
      have hout' : eLpNorm ((s \ B).indicator (f i)) 1 μ ≤ ENNReal.ofReal (ε / 3) :=
        (eLpNorm_mono (fun x ↦ by
          by_cases hx : x ∈ s \ B
          · have hxc : x ∈ Bᶜ := hx.2
            simp [hx, hxc]
          · simp [hx])).trans (hout i)
      have hfin := memLp_one_iff_integrable.mp (hf.memLp i)
      have hinReal := integral_norm_le_of_eLpNorm_indicator_le hfin (hs.inter hB)
        (by linarith : 0 ≤ ε / 3) hin
      have houtReal := integral_norm_le_of_eLpNorm_indicator_le hfin (hs.diff hB)
        (by linarith : 0 ≤ ε / 3) hout'
      have hsplit : (∫ x in s, ‖f i x‖ ∂μ) =
          (∫ x in s ∩ B, ‖f i x‖ ∂μ) + (∫ x in s \ B, ‖f i x‖ ∂μ) := by
        have hu := setIntegral_union (μ := μ) (f := fun x ↦ ‖f i x‖)
          (s := s ∩ B) (t := s \ B)
          (Set.disjoint_left.2 fun _ hx hxd ↦ hxd.2 hx.2) (hs.diff hB)
          hfin.norm.integrableOn hfin.norm.integrableOn
        simpa only [Set.inter_union_sdiff] using hu
      rw [hsplit]
      linarith
  · rintro ⟨hfint, ⟨C, hC⟩, hden⟩
    rcases hden with ⟨h, hh, hh0, hsmall⟩
    refine ⟨?_, ?_⟩
    · refine ⟨fun i ↦ (hfint i).aestronglyMeasurable, ?_, ?_⟩
      · intro ε hε
        obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
        have hhUI : UnifIntegrable (fun _ : Unit ↦ h) 1 μ :=
          unifIntegrable_const le_rfl ENNReal.one_ne_top
            (memLp_one_iff_integrable.mpr hh)
        obtain ⟨η, hη, hηsmall⟩ := hhUI (ε := δ / 2) (by linarith)
        refine ⟨η, hη, fun i s hs hμs ↦ ?_⟩
        have hhNorm := hηsmall () s hs hμs
        have hhIntNorm := integral_norm_le_of_eLpNorm_indicator_le hh hs
          (by linarith : 0 ≤ δ / 2) hhNorm
        have hhInt : (∫ x in s, h x ∂μ) ≤ δ / 2 := by
          have heq : (∫ x in s, ‖h x‖ ∂μ) = ∫ x in s, h x ∂μ := by
            apply setIntegral_congr_ae hs
            filter_upwards [hh0] with x hx
            intro _
            rw [Real.norm_eq_abs, abs_of_nonneg hx]
          linarith [hhIntNorm]
        exact eLpNorm_indicator_le_of_integral_norm_lt (hfint i) hs
          (hδsmall i s hs (by linarith))
      · refine ⟨(ENNReal.ofReal C).toNNReal, fun i ↦ ?_⟩
        rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top,
          eLpNorm_one_eq_ofReal_integral_norm (hfint i)]
        exact ENNReal.ofReal_le_ofReal (hC i)
    · rw [unifTight_iff_real]
      intro ε hε
      obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
      obtain ⟨s, hs, hμs, hhout⟩ :=
        (memLp_one_iff_integrable.mpr hh).exists_eLpNorm_indicator_compl_lt
          ENNReal.one_ne_top (ENNReal.ofReal_pos.mpr hδ).ne'
      refine ⟨s, hμs.ne, fun i ↦ ?_⟩
      have hhInt : (∫ x in sᶜ, h x ∂μ) < δ := by
        have heq : (∫ x in sᶜ, ‖h x‖ ∂μ) = ∫ x in sᶜ, h x ∂μ := by
          apply setIntegral_congr_ae hs.compl
          filter_upwards [hh0] with x hx
          intro _
          rw [Real.norm_eq_abs, abs_of_nonneg hx]
        rw [← heq]
        rw [eLpNorm_indicator_one_eq_ofReal_integral_norm hh hs.compl] at hhout
        exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hhout
      exact eLpNorm_indicator_le_of_integral_norm_lt (hfint i) hs.compl
        (hδsmall i sᶜ hs.compl hhInt)

end

end MeasureTheory
