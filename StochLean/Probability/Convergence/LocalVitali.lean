/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureLocal
public import StochLean.ForMathlib.MeasureTheory.Function.DeLaValleePoussin
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Local Vitali convergence

This module applies Mathlib's finite-measure Vitali theorem on every measurable finite-measure
restriction. It is the local bridge appropriate for sigma-finite and more general ambient spaces.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E]

/-- Uniform integrability on every measurable set of finite measure. -/
def LocallyUnifIntegrable (f : ℕ → α → E) (p : ENNReal) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → UnifIntegrable f p (μ.restrict s)

/-- Local `Lᵖ` membership on every measurable set of finite measure. -/
def LocallyMemLp (g : α → E) (p : ENNReal) (μ : Measure α) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → MemLp g p (μ.restrict s)

/-- Local convergence in measure plus local uniform integrability implies `Lᵖ` convergence on each
finite-measure restriction. -/
theorem TendstoLocallyInMeasure.tendsto_eLpNorm_restrict
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : LocallyMemLp g p μ) (hui : LocallyUnifIntegrable f p μ)
    (hfg : TendstoLocallyInMeasure μ f atTop g)
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p (μ.restrict s)) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  exact tendsto_Lp_finite_of_tendstoInMeasure hp hp' (fun n ↦ (hf n).restrict)
    (hg s hs hμs) (hui s hs hμs) (hfg s hs hμs)

/-- Sigma-finite-style Vitali convergence: local convergence in measure, uniform absolute
continuity, and uniform tightness imply global `Lᵖ` convergence. No finiteness assumption on the
ambient measure is required. -/
theorem TendstoLocallyInMeasure.tendsto_eLpNorm
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoLocallyInMeasure μ f atTop g) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact ⟨0, fun n _ ↦ hεtop.symm ▸ le_top⟩
  have hεthird : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ :=
    hg.exists_eLpNorm_indicator_compl_lt hp' hεthird.ne'
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut.exists_measurableSet_indicator hεthird.ne'
  let A : Set α := Ef ∪ Eg
  have hmA : MeasurableSet A := hmEf.union hmEg
  have hμA : μ A < ∞ :=
    (measure_union_le Ef Eg).trans_lt (ENNReal.add_lt_top.mpr ⟨hμEf, hμEg⟩)
  have hlocal := hfg.tendsto_eLpNorm_restrict hp hp' hf
    (fun s _ _ ↦ hg.restrict s)
    (fun s _ _ ↦ hui.restrict s) A hmA hμA.ne
  rw [ENNReal.tendsto_atTop_zero] at hlocal
  obtain ⟨N, hN⟩ := hlocal (ε / 3) hεthird
  refine ⟨N, fun n hn ↦ ?_⟩
  have hfA : AEStronglyMeasurable (A.indicator (f n - g)) μ :=
    ((hf n).sub hg.aestronglyMeasurable).indicator hmA
  have hfAc : AEStronglyMeasurable (Aᶜ.indicator (f n - g)) μ :=
    ((hf n).sub hg.aestronglyMeasurable).indicator hmA.compl
  have hfnAc : eLpNorm (Aᶜ.indicator (f n)) p μ ≤ ε / 3 := by
    calc
      eLpNorm (Aᶜ.indicator (f n)) p μ ≤
          eLpNorm (Efᶜ.indicator (f n)) p μ := by
        apply eLpNorm_mono
        exact norm_indicator_le_of_subset
          (Set.compl_subset_compl.mpr Set.subset_union_left) _
      _ ≤ ε / 3 := hfε n
  have hgAc : eLpNorm (Aᶜ.indicator g) p μ ≤ ε / 3 := by
    calc
      eLpNorm (Aᶜ.indicator g) p μ ≤ eLpNorm (Egᶜ.indicator g) p μ := by
        apply eLpNorm_mono
        exact norm_indicator_le_of_subset
          (Set.compl_subset_compl.mpr Set.subset_union_right) _
      _ ≤ ε / 3 := hgε.le
  have hdiffAc : eLpNorm (Aᶜ.indicator (f n - g)) p μ ≤ ε / 3 + ε / 3 := by
    rw [Set.indicator_sub']
    exact (eLpNorm_sub_le ((hf n).indicator hmA.compl)
      (hg.aestronglyMeasurable.indicator hmA.compl) hp).trans
        (add_le_add hfnAc hgAc)
  have hdiffA : eLpNorm (A.indicator (f n - g)) p μ ≤ ε / 3 := by
    calc
      eLpNorm (A.indicator (f n - g)) p μ =
          eLpNorm (f n - g) p (μ.restrict A) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hmA
      _ ≤ ε / 3 := hN n hn
  calc
    eLpNorm (f n - g) p μ =
        eLpNorm (Aᶜ.indicator (f n - g) + A.indicator (f n - g)) p μ := by
      congr 1
      exact (A.indicator_compl_add_self _).symm
    _ ≤ eLpNorm (Aᶜ.indicator (f n - g)) p μ +
        eLpNorm (A.indicator (f n - g)) p μ :=
      eLpNorm_add_le hfAc hfA hp
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hdiffAc hdiffA
    _ = ε := ENNReal.add_thirds ε

/-- Klenke's envelope-uniform-integrability form of the sigma-finite Vitali theorem. -/
theorem TendstoLocallyInMeasure.tendsto_eLpNorm_of_uniformIntegrableByEnvelope
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hg : MemLp g p μ)
    (hui : UniformIntegrableByEnvelope f p μ)
    (hfg : TendstoLocallyInMeasure μ f atTop g) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  hfg.tendsto_eLpNorm hp hp'
    (fun n ↦ hui.aestronglyMeasurable n) hg hui.unifIntegrable hui.unifTight

set_option maxHeartbeats 400000 in
-- The finite-prefix norm bound expands the nested `UniformIntegrable` structure and needs a
-- slightly larger elaboration budget than the project default.
/-- `Lᵖ` convergence supplies the full sigma-finite envelope-uniform-integrability package.
The explicit uniform norm bound is separated from Mathlib's `UnifIntegrable`/`UnifTight`
Vitali pair and obtained from convergence plus the finitely many initial terms. -/
theorem uniformIntegrableByEnvelope_of_tendsto_eLpNorm
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ)
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0)) :
    UniformIntegrableByEnvelope f p μ := by
  have hcanonical := (tendstoInMeasure_iff_tendsto_Lp hp hp' hf hg).mpr hfg
  have hzero := hfg
  rw [ENNReal.tendsto_atTop_zero] at hzero
  obtain ⟨N, hN⟩ := hzero 1 zero_lt_one
  obtain ⟨C₀, hC₀⟩ :=
    (uniformIntegrable_finite hp hp' (fun n : Fin N ↦ hf n)).2.2
  let Cg : NNReal := (eLpNorm g p μ).toNNReal
  let C : NNReal := max C₀ (1 + Cg)
  have hCg : eLpNorm g p μ = (Cg : ENNReal) := by
    exact (ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne).symm
  have hbound : ∀ n, eLpNorm (f n) p μ ≤ (C : ENNReal) := by
    intro n
    by_cases hn : n < N
    · calc
        eLpNorm (f n) p μ ≤ (C₀ : ENNReal) := hC₀ ⟨n, hn⟩
        _ ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_left _ _)
    · calc
        eLpNorm (f n) p μ ≤ eLpNorm (f n - g) p μ + eLpNorm g p μ := by
          simpa only [Pi.sub_apply, Pi.add_apply, sub_add_cancel] using
            eLpNorm_add_le ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable)
              hg.aestronglyMeasurable hp
        _ ≤ 1 + (Cg : ENNReal) := add_le_add (hN n (Nat.le_of_not_gt hn)) hCg.le
        _ = ((1 + Cg : NNReal) : ENNReal) := by simp
        _ ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_right _ _)
  exact ⟨⟨fun n ↦ (hf n).aestronglyMeasurable, hcanonical.2.1, ⟨C, hbound⟩⟩,
    hcanonical.2.2⟩

/-- Exact sigma-finite local Vitali equivalence in the StochLean semantics. -/
theorem tendstoLocallyInMeasure_and_uniformIntegrableByEnvelope_iff_tendsto_eLpNorm
    {p : ENNReal} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoLocallyInMeasure μ f atTop g ∧ UniformIntegrableByEnvelope f p μ ↔
      Tendsto (fun n ↦ eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  constructor
  · rintro ⟨hlocal, hui⟩
    exact hlocal.tendsto_eLpNorm_of_uniformIntegrableByEnvelope hp hp' hg hui
  · intro hLp
    refine ⟨?_, uniformIntegrableByEnvelope_of_tendsto_eLpNorm hp hp' hf hg hLp⟩
    exact (tendstoInMeasure_of_tendsto_eLpNorm
      (lt_of_lt_of_le zero_lt_one hp).ne' (fun n ↦ (hf n).aestronglyMeasurable)
        hg.aestronglyMeasurable hLp).locally

end MeasureTheory
