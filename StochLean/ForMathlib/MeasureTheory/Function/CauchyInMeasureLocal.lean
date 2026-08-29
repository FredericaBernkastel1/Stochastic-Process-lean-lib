/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.FastConvergenceLocal
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cauchy sequences for local convergence in measure

This file gives the local Cauchy notion and proves Klenke's completeness theorem 6.15.  The
construction selects a fast diagonal subsequence on the canonical sigma-finite spanning sets,
uses Borel--Cantelli to obtain an almost-everywhere limit, and then returns to the full sequence.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α F : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- A sequence is Cauchy locally in measure when it is Cauchy after every measurable
finite-measure restriction. -/
def CauchyLocallyInMeasure [PseudoMetricSpace F] (μ : Measure α)
    (f : ℕ → α → F) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → ∀ ε : ℝ, 0 < ε →
    ∀ δ : ENNReal, 0 < δ → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      (μ.restrict s) {x | ε ≤ dist (f m x) (f n x)} ≤ δ

/-- Every locally-in-measure convergent sequence is locally Cauchy in measure. -/
theorem TendstoLocallyInMeasure.cauchy [PseudoMetricSpace F]
    {f : ℕ → α → F} {g : α → F} (hfg : TendstoLocallyInMeasure μ f atTop g) :
    CauchyLocallyInMeasure μ f := by
  intro s hs hμs r hr η hη
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  have hres := hfg s hs hμs
  rw [tendstoInMeasure_iff_dist] at hres
  have hηhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hres (r / 2) (by positivity))
    (η / 2) hηhalf
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  let A := {x | r / 2 ≤ dist (f m x) (g x)}
  let B := {x | r / 2 ≤ dist (f n x) (g x)}
  have hsubset : {x | r ≤ dist (f m x) (f n x)} ⊆ A ∪ B := by
    intro x hx
    change r ≤ dist (f m x) (f n x) at hx
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, A, B] at hnot
    have htri := dist_triangle (f m x) (g x) (f n x)
    rw [dist_comm (g x) (f n x)] at htri
    linarith
  calc
    (μ.restrict s) {x | r ≤ dist (f m x) (f n x)}
        ≤ (μ.restrict s) (A ∪ B) := measure_mono hsubset
    _ ≤ (μ.restrict s) A + (μ.restrict s) B := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hN m hm) (hN n hn)
    _ = η := ENNReal.add_halves η

/-- Klenke 6.15: a strongly measurable sequence which is Cauchy locally in measure has a
strongly measurable local-in-measure limit whenever the target metric space is complete. -/
theorem CauchyLocallyInMeasure.exists_tendsto [SigmaFinite μ]
    [MetricSpace F] [CompleteSpace F] [Nonempty F]
    {f : ℕ → α → F} (hC : CauchyLocallyInMeasure μ f)
    (hf : ∀ n, StronglyMeasurable (f n)) :
    ∃ g : α → F, StronglyMeasurable g ∧ TendstoLocallyInMeasure μ f atTop g := by
  let ε : ℕ → ℝ := fun k ↦ (2 : ℝ)⁻¹ ^ k
  let δ : ℕ → ENNReal := fun k ↦ (2 : ENNReal)⁻¹ ^ k
  let N : ℕ → ℕ := fun k ↦ Classical.choose
    (hC (spanningSets μ k) (measurableSet_spanningSets μ k)
      (measure_spanningSets_lt_top μ k).ne (ε k) (by simp [ε]) (δ k) (by
        exact ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) _))
  have hN (k m n : ℕ) (hm : N k ≤ m) (hn : N k ≤ n) :
      (μ.restrict (spanningSets μ k)) {x | ε k ≤ dist (f m x) (f n x)} ≤ δ k :=
    Classical.choose_spec
      (hC (spanningSets μ k) (measurableSet_spanningSets μ k)
        (measure_spanningSets_lt_top μ k).ne (ε k) (by simp [ε]) (δ k) (by
          exact ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) _)) m n hm hn
  let ns : ℕ → ℕ := fun n ↦
    Nat.rec (N 0) (fun k previous ↦ max (N (k + 1)) (previous + 1)) n
  have hns_succ (k : ℕ) : ns (k + 1) = max (N (k + 1)) (ns k + 1) := by
    simp [ns]
  have hns : StrictMono ns := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    rw [hns_succ]
    exact lt_of_lt_of_le (lt_add_one (ns k)) (le_max_right _ _)
  have hNns (k : ℕ) : N k ≤ ns k := by
    cases k with
    | zero => simp [ns]
    | succ k => rw [hns_succ]; exact le_max_left _ _
  have hmeasure (k : ℕ) :
      (μ.restrict (spanningSets μ k))
        {x | ε k < dist (f (ns k) x) (f (ns (k + 1)) x)} ≤ δ k := by
    refine (measure_mono ?_).trans (hN k (ns k) (ns (k + 1)) (hNns k) ?_)
    · intro x hx
      change ε k < dist (f (ns k) x) (f (ns (k + 1)) x) at hx
      change ε k ≤ dist (f (ns k) x) (f (ns (k + 1)) x)
      exact hx.le
    · exact (hNns k).trans (Nat.le_of_lt (hns (Nat.lt_succ_self k)))
  have hsum : (∑' k, (μ.restrict (spanningSets μ k))
      {x | ε k < dist (f (ns k) x) (f (ns (k + 1)) x)}) ≠ ∞ := by
    have hgeom : (∑' k, δ k) ≠ ∞ := by
      simpa only [δ, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
        ENNReal.ofNat_ne_top
    exact ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum hmeasure)
  have hε : Summable ε := by
    simpa only [ε, one_div] using summable_geometric_two
  obtain ⟨g, hg, hsubae⟩ :=
    exists_stronglyMeasurable_tendsto_ae_of_fast_cauchy_spanning
      (μ := μ) (f := fun k ↦ f (ns k)) (ε := ε) (fun k ↦ hf (ns k)) hε hsum
  refine ⟨g, hg, ?_⟩
  intro s hs hμs
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  rw [tendstoInMeasure_iff_dist]
  intro r hr
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  have hηhalf : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨Nc, hNc⟩ := hC s hs hμs (r / 2) (by positivity) (η / 2) hηhalf
  have hsub : TendstoInMeasure (μ.restrict s) (fun k ↦ f (ns k)) atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (hf (ns k)).aestronglyMeasurable.restrict)
      (ae_restrict_of_ae hsubae)
  rw [tendstoInMeasure_iff_dist] at hsub
  obtain ⟨K, hK⟩ := ENNReal.tendsto_atTop_zero.mp (hsub (r / 2) (by positivity))
    (η / 2) hηhalf
  let k := max K Nc
  have hnsk : Nc ≤ ns k := (le_max_right K Nc).trans hns.le_apply
  refine ⟨Nc, fun n hn ↦ ?_⟩
  let A := {x | r / 2 ≤ dist (f n x) (f (ns k) x)}
  let B := {x | r / 2 ≤ dist (f (ns k) x) (g x)}
  have hsubset : {x | r ≤ dist (f n x) (g x)} ⊆ A ∪ B := by
    intro x hx
    change r ≤ dist (f n x) (g x) at hx
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, A, B] at hnot
    have htri := dist_triangle (f n x) (f (ns k) x) (g x)
    linarith
  calc
    (μ.restrict s) {x | r ≤ dist (f n x) (g x)}
        ≤ (μ.restrict s) (A ∪ B) := measure_mono hsubset
    _ ≤ (μ.restrict s) A + (μ.restrict s) B := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add
      (hNc n (ns k) hn hnsk) (hK k (le_max_left K Nc))
    _ = η := ENNReal.add_halves η

/-- Completeness characterized as existence of a strongly measurable local-in-measure limit. -/
theorem cauchyLocallyInMeasure_iff_exists_tendsto [SigmaFinite μ]
    [MetricSpace F] [CompleteSpace F] [Nonempty F]
    {f : ℕ → α → F} (hf : ∀ n, StronglyMeasurable (f n)) :
    CauchyLocallyInMeasure μ f ↔
      ∃ g : α → F, StronglyMeasurable g ∧ TendstoLocallyInMeasure μ f atTop g := by
  constructor
  · intro h
    exact h.exists_tendsto hf
  · rintro ⟨g, _hg, hfg⟩
    exact hfg.cauchy

end MeasureTheory
