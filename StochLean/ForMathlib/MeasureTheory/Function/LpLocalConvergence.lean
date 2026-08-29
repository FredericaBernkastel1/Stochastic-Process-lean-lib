/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Convergence.LocalVitali
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Klenke's powered-family presentation of local `Lᵖ` convergence

For finite nonzero `p`, the `Lᵖ` envelope condition on `fₙ` is equivalent to the literal Klenke
condition that `x ↦ ‖fₙ x‖ ^ p.toReal` be envelope uniformly integrable in `L¹`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory

noncomputable section

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E]

private theorem eLpNorm_indicator_norm_rpow
    {p : ENNReal} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) (f : α → E) (s : Set α) :
    eLpNorm (s.indicator (fun x ↦ ‖f x‖ ^ p.toReal)) 1 μ =
      eLpNorm (s.indicator f) p μ ^ p.toReal := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  calc
    eLpNorm (s.indicator (fun x ↦ ‖f x‖ ^ p.toReal)) 1 μ =
        eLpNorm (fun x ↦ ‖s.indicator f x‖ ^ p.toReal) 1 μ := by
      congr 1
      funext x
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs, Real.zero_rpow hpReal.ne']
    _ = eLpNorm (s.indicator f) (1 * ENNReal.ofReal p.toReal) μ ^ p.toReal :=
      eLpNorm_norm_rpow (s.indicator f) hpReal
    _ = eLpNorm (s.indicator f) p μ ^ p.toReal := by
      rw [one_mul, ENNReal.ofReal_toReal hpTop]

private theorem ofReal_rpow_inv_rpow (x q : ℝ) (hx : 0 < x) (hq : 0 < q) :
    ENNReal.ofReal (x ^ (1 / q)) ^ q = ENNReal.ofReal x := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hx _),
    ← Real.rpow_mul hx.le (1 / q) q]
  have hq0 : q ≠ 0 := hq.ne'
  rw [one_div, inv_mul_cancel₀ hq0, Real.rpow_one]

private theorem ofReal_rpow (x q : ℝ) (hx : 0 ≤ x) (hq : 0 ≤ q) :
    ENNReal.ofReal (x ^ q) = ENNReal.ofReal x ^ q :=
  (ENNReal.ofReal_rpow_of_nonneg hx hq).symm

private theorem unifIntegrable_norm_rpow_iff
    {p : ENNReal} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) {f : ℕ → α → E} :
    UnifIntegrable (fun n x ↦ ‖f n x‖ ^ p.toReal) 1 μ ↔
      UnifIntegrable f p μ := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  constructor
  · intro hpow ε hε
    have hεpow : 0 < ε ^ p.toReal := Real.rpow_pos_of_pos hε _
    obtain ⟨δ, hδ, hsmall⟩ := hpow hεpow
    refine ⟨δ, hδ, fun n s hs hμs ↦ ?_⟩
    have hi := hsmall n s hs hμs
    rw [eLpNorm_indicator_norm_rpow hp0 hpTop] at hi
    have hi' : eLpNorm (s.indicator (f n)) p μ ^ p.toReal ≤
        ENNReal.ofReal ε ^ p.toReal := by
      rw [← ofReal_rpow ε p.toReal hε.le hpReal.le]
      exact hi
    exact (ENNReal.rpow_le_rpow_iff hpReal).mp hi'
  · intro h ε hε
    let r : ℝ := ε ^ (1 / p.toReal)
    have hr : 0 < r := Real.rpow_pos_of_pos hε _
    obtain ⟨δ, hδ, hsmall⟩ := h hr
    refine ⟨δ, hδ, fun n s hs hμs ↦ ?_⟩
    rw [eLpNorm_indicator_norm_rpow hp0 hpTop]
    exact (ENNReal.rpow_le_rpow (hsmall n s hs hμs) hpReal.le).trans_eq
      (ofReal_rpow_inv_rpow ε p.toReal hε hpReal)

private theorem unifTight_norm_rpow_iff
    {p : ENNReal} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) {f : ℕ → α → E} :
    UnifTight (fun n x ↦ ‖f n x‖ ^ p.toReal) 1 μ ↔ UnifTight f p μ := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  constructor
  · intro h ε hε
    let r : NNReal := ε ^ p.toReal
    have hr : 0 < r := NNReal.rpow_pos hε
    obtain ⟨s, hμs, hsmall⟩ := h hr
    refine ⟨s, hμs, fun n ↦ ?_⟩
    have hi := hsmall n
    rw [eLpNorm_indicator_norm_rpow hp0 hpTop] at hi
    have hi' : eLpNorm (sᶜ.indicator (f n)) p μ ^ p.toReal ≤
        (ε : ENNReal) ^ p.toReal := by
      simpa only [r, ENNReal.coe_rpow_of_nonneg _ hpReal.le] using hi
    exact (ENNReal.rpow_le_rpow_iff hpReal).mp hi'
  · intro h ε hε
    let r : NNReal := ε ^ (1 / p.toReal)
    have hr : 0 < r := NNReal.rpow_pos hε
    obtain ⟨s, hμs, hsmall⟩ := h hr
    refine ⟨s, hμs, fun n ↦ ?_⟩
    rw [eLpNorm_indicator_norm_rpow hp0 hpTop]
    refine (ENNReal.rpow_le_rpow (hsmall n) hpReal.le).trans_eq ?_
    rw [← ENNReal.coe_rpow_of_nonneg _ hpReal.le]
    apply ENNReal.coe_inj.mpr
    dsimp only [r]
    rw [← NNReal.rpow_mul]
    have hp0Real : p.toReal ≠ 0 := hpReal.ne'
    rw [one_div, inv_mul_cancel₀ hp0Real, NNReal.rpow_one]

/-- The canonical `Lᵖ` envelope condition is equivalent to Klenke's explicit uniform
integrability of the powered norms. -/
theorem uniformIntegrableByEnvelope_norm_rpow_iff
    {p : ENNReal} (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) {f : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) p μ) :
    UniformIntegrableByEnvelope (fun n x ↦ ‖f n x‖ ^ p.toReal) 1 μ ↔
      UniformIntegrableByEnvelope f p μ := by
  have hpowMeas : ∀ n, AEStronglyMeasurable (fun x ↦ ‖f n x‖ ^ p.toReal) μ :=
    fun n ↦ ((hf n).aestronglyMeasurable.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable
  constructor
  · rintro ⟨⟨_, huac, C, hC⟩, htight⟩
    have hnorm : ∀ n, eLpNorm (f n) p μ ≤
        (C : ENNReal) ^ (1 / p.toReal) := by
      intro n
      have hi := hC n
      have hId := eLpNorm_indicator_norm_rpow (μ := μ) hp0 hpTop (f n) Set.univ
      simp only [Set.indicator_univ] at hId
      rw [hId] at hi
      have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
      apply (ENNReal.rpow_le_rpow_iff hpReal).mp
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpReal.ne',
        ENNReal.rpow_one]
      exact hi
    refine ⟨⟨fun n ↦ (hf n).aestronglyMeasurable,
      (unifIntegrable_norm_rpow_iff hp0 hpTop).mp huac,
      ⟨((C : ENNReal) ^ (1 / p.toReal)).toNNReal, fun n ↦ ?_⟩⟩,
      (unifTight_norm_rpow_iff hp0 hpTop).mp htight⟩
    rw [ENNReal.coe_toNNReal]
    · exact hnorm n
    · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  · rintro ⟨⟨hmeas, huac, C, hC⟩, htight⟩
    refine ⟨⟨hpowMeas,
      (unifIntegrable_norm_rpow_iff hp0 hpTop).mpr huac,
      ⟨C ^ p.toReal, fun n ↦ ?_⟩⟩,
      (unifTight_norm_rpow_iff hp0 hpTop).mpr htight⟩
    have hId := eLpNorm_indicator_norm_rpow (μ := μ) hp0 hpTop (f n) Set.univ
    simp only [Set.indicator_univ] at hId
    rw [hId, ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
    exact ENNReal.rpow_le_rpow (hC n) ENNReal.toReal_nonneg

/-- Klenke 7.3: global `Lᵖ` convergence is equivalent to local convergence in measure plus
envelope uniform integrability of the literal powered family `‖fₙ‖^p`. -/
theorem tendstoLocallyInMeasure_and_poweredEnvelope_iff_tendsto_eLpNorm
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤) (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoLocallyInMeasure μ f atTop g ∧
        UniformIntegrableByEnvelope (fun n x ↦ ‖f n x‖ ^ p.toReal) 1 μ ↔
      Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [uniformIntegrableByEnvelope_norm_rpow_iff
    (lt_of_lt_of_le zero_lt_one hp).ne' hpTop hf]
  exact tendstoLocallyInMeasure_and_uniformIntegrableByEnvelope_iff_tendsto_eLpNorm
    hp hpTop hf hg

end

end MeasureTheory
