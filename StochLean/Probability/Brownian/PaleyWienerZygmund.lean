/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.PathProperties
public import Mathlib.Probability.Independence.Basic

/-!
# The Paley--Wiener--Zygmund path obstruction

This file develops the finite-grid estimate behind the theorem that Brownian paths are almost
surely nowhere Hoelder of order strictly greater than one half.  The argument is internal to
StochLean and uses only Mathlib's Gaussian density and independent-increment APIs.

The first lemma is deliberately stated for a general centered real Gaussian law.  It is useful
independently of Brownian motion and keeps every normalization constant visible.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- A centered real Gaussian puts at most interval length times the maximum of its density in a
symmetric interval.  This elementary small-ball estimate is the analytic input to PWZ. -/
theorem gaussianReal_Icc_zero_le (v : ℝ≥0) (hv : v ≠ 0) (e : ℝ) (he : 0 ≤ e) :
    (gaussianReal 0 v).real (Icc (-e) e) ≤
      (2 * e) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  have hpdf (x : ℝ) : gaussianPDF 0 v x ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    apply ENNReal.ofReal_le_ofReal
    simp only [gaussianPDFReal, sub_zero]
    apply mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)
  have hmeasure : gaussianReal 0 v (Icc (-e) e) ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        ENNReal.ofReal (2 * e) := by
    rw [gaussianReal_of_var_ne_zero 0 hv, withDensity_apply _ measurableSet_Icc]
    calc
      (∫⁻ x in Icc (-e) e, gaussianPDF 0 v x) ≤
          ∫⁻ _x in Icc (-e) e,
            ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ :=
        setLIntegral_mono measurable_const fun x _ ↦ hpdf x
      _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          ENNReal.ofReal (2 * e) := by
        rw [setLIntegral_const, Real.volume_Icc]
        congr 1
        ring_nf
  rw [Measure.real_def]
  have hfinite : gaussianReal 0 v (Icc (-e) e) ≠ ∞ := measure_ne_top _ _
  have hrfinite : ENNReal.ofReal (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
      ENNReal.ofReal (2 * e) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hfinite hrfinite).mpr hmeasure
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) he)] at hreal
  nlinarith

/-- `ENNReal` form of `gaussianReal_Icc_zero_le`, convenient for probability products. -/
theorem gaussianReal_Icc_zero_le_ennreal (v : ℝ≥0) (hv : v ≠ 0) (e : ℝ) (he : 0 ≤ e) :
    gaussianReal 0 v (Icc (-e) e) ≤
      ENNReal.ofReal ((2 * e) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal]
  · exact gaussianReal_Icc_zero_le v hv e he
  · exact mul_nonneg (mul_nonneg (by positivity) he) (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Equally spaced points on `[a, a + L]`. -/
noncomputable def uniformGrid (a L : ℝ≥0) (n : ℕ) (i : Fin (n + 1)) : ℝ≥0 :=
  a + (i.val : ℝ≥0) * (L / (n : ℝ≥0))

theorem uniformGrid_monotone (a L : ℝ≥0) (n : ℕ) : Monotone (uniformGrid a L n) := by
  intro i j hij
  simp only [uniformGrid]
  gcongr
  exact_mod_cast hij

theorem uniformGrid_mem_Icc (a L : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    uniformGrid a L n i ∈ Icc a (a + L) := by
  constructor
  · simp [uniformGrid]
  · simp only [uniformGrid]
    gcongr
    calc
      (i.val : ℝ≥0) * (L / n) = ((i.val : ℝ≥0) / n) * L := by ring
      _ ≤ 1 * L := by
        apply mul_le_mul_of_nonneg_right
        · exact (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast i.is_le)
        · exact L.property
      _ = L := one_mul L

theorem nndist_uniformGrid_succ_castSucc (a L : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (i : Fin n) :
    nndist (uniformGrid a L n i.succ) (uniformGrid a L n i.castSucc) = L / n := by
  have hle : uniformGrid a L n i.castSucc ≤ uniformGrid a L n i.succ :=
    uniformGrid_monotone a L n Fin.castSucc_lt_succ.le
  rw [NNReal.nndist_eq, tsub_eq_zero_of_le hle, max_zero]
  apply NNReal.eq
  rw [NNReal.coe_sub hle]
  simp only [uniformGrid, Fin.val_castSucc, Fin.val_succ, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_div]
  field_simp
  push_cast
  ring

theorem nndist_coe_uniformGrid_succ_castSucc (a L : ℝ≥0) {n : ℕ} (hn : 0 < n)
    (i : Fin n) :
    nndist (uniformGrid a L n i.succ : ℝ) (uniformGrid a L n i.castSucc : ℝ) = L / n := by
  apply NNReal.eq
  rw [coe_nndist, Real.dist_eq, ← NNReal.dist_eq, ← coe_nndist]
  exact congrArg ((↑) : ℝ≥0 → ℝ) (nndist_uniformGrid_succ_castSucc a L hn i)

/-- The increment over one cell of `uniformGrid`. -/
noncomputable def uniformGridIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a L : ℝ≥0)
    (n : ℕ) (i : Fin n) (ω : Ω) : ℝ :=
  B (uniformGrid a L n i.succ) ω - B (uniformGrid a L n i.castSucc) ω

theorem IsPreBrownianReal.uniformGridIncrement_hasLaw
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a L : ℝ≥0) {n : ℕ} (hn : 0 < n) (i : Fin n) :
    HasLaw (uniformGridIncrement B a L n i) (gaussianReal 0 (L / n)) P := by
  have h := hB.hasLaw_sub (uniformGrid a L n i.succ) (uniformGrid a L n i.castSucc)
  convert h using 1
  · rfl
  · exact congrArg (gaussianReal 0) (nndist_coe_uniformGrid_succ_castSucc a L hn i).symm

theorem IsPreBrownianReal.measure_uniformGridIncrements_Icc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a L : ℝ≥0) {n : ℕ} (hn : 0 < n) (e : ℝ) :
    P (⋂ i : Fin n, uniformGridIncrement B a L n i ⁻¹' Icc (-e) e) =
      ∏ _i : Fin n, gaussianReal 0 (L / n) (Icc (-e) e) := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  have hIndep : iIndepFun (uniformGridIncrement B a L n) P := by
    exact hB.hasIndepIncrements n (uniformGrid a L n) (uniformGrid_monotone a L n)
  rw [hIndep.meas_iInter]
  · apply Finset.prod_congr rfl
    intro i _
    have hLaw := hB.uniformGridIncrement_hasLaw a L hn i
    rw [← hLaw.map_eq, Measure.map_apply_of_aemeasurable hLaw.aemeasurable measurableSet_Icc]
  · intro i
    exact MeasurableSpace.measurableSet_comap.2 ⟨Icc (-e) e, measurableSet_Icc, rfl⟩

theorem IsPreBrownianReal.measure_uniformGridIncrements_Icc_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a : ℝ≥0) {L : ℝ≥0} (hL : L ≠ 0)
    {n : ℕ} (hn : 0 < n) (e : ℝ) (he : 0 ≤ e) :
    P (⋂ i : Fin n, uniformGridIncrement B a L n i ⁻¹' Icc (-e) e) ≤
      (ENNReal.ofReal ((2 * e) *
        (Real.sqrt (2 * Real.pi * ((L / n : ℝ≥0) : ℝ)))⁻¹)) ^ n := by
  rw [hB.measure_uniformGridIncrements_Icc a L hn e]
  calc
    (∏ _i : Fin n, gaussianReal 0 (L / n) (Icc (-e) e)) ≤
        ∏ _i : Fin n, ENNReal.ofReal ((2 * e) *
          (Real.sqrt (2 * Real.pi * ((L / n : ℝ≥0) : ℝ)))⁻¹) := by
      apply Finset.prod_le_prod
      · intro i _
        exact bot_le
      · intro i _
        exact gaussianReal_Icc_zero_le_ennreal (L / n)
          (div_ne_zero hL (by exact_mod_cast hn.ne')) e he
    _ = (ENNReal.ofReal ((2 * e) *
        (Real.sqrt (2 * Real.pi * ((L / n : ℝ≥0) : ℝ)))⁻¹)) ^ n := by simp

theorem holderOnWith_uniformGridIncrement_mem_Icc
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {C γ a L : ℝ≥0} {n : ℕ} (hn : 0 < n)
    (hω : HolderOnWith C γ (B · ω) (Icc a (a + L))) (i : Fin n) :
    uniformGridIncrement B a L n i ω ∈
      Icc (-(C * (L / n) ^ (γ : ℝ) : ℝ)) (C * (L / n) ^ (γ : ℝ) : ℝ) := by
  have h := hω.dist_le (uniformGrid_mem_Icc a L hn i.succ)
    (uniformGrid_mem_Icc a L hn i.castSucc)
  have hdist : dist (uniformGrid a L n i.succ) (uniformGrid a L n i.castSucc) =
      (L / n : ℝ≥0) := by
    rw [← coe_nndist]
    exact congrArg ((↑) : ℝ≥0 → ℝ) (nndist_uniformGrid_succ_castSucc a L hn i)
  rw [Real.dist_eq, hdist] at h
  exact abs_le.mp h

theorem holderOnWith_event_subset_uniformGridIncrements
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {C γ a L : ℝ≥0} {n : ℕ} (hn : 0 < n) :
    {ω | HolderOnWith C γ (B · ω) (Icc a (a + L))} ⊆
      ⋂ i : Fin n, uniformGridIncrement B a L n i ⁻¹'
        Icc (-(C * (L / n) ^ (γ : ℝ) : ℝ)) (C * (L / n) ^ (γ : ℝ) : ℝ) := by
  intro ω hω
  simp only [mem_iInter]
  intro i
  exact holderOnWith_uniformGridIncrement_mem_Icc hn hω i

theorem smallBallHolderBase_eq (C δ γ : ℝ) (hδ : 0 < δ) :
    (2 * (C * δ ^ γ)) * (Real.sqrt (2 * Real.pi * δ))⁻¹ =
      (2 * C * (Real.sqrt (2 * Real.pi))⁻¹) * δ ^ (γ - (2 : ℝ)⁻¹) := by
  rw [show 2 * Real.pi * δ = (2 * Real.pi) * δ by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (2 * Real.pi),
    Real.sqrt_eq_rpow δ, Real.rpow_sub hδ]
  field_simp

theorem tendsto_smallBallHolderBase (C L γ : ℝ) (hL : 0 < L)
    (hγ : (2 : ℝ)⁻¹ < γ) :
    Tendsto (fun n : ℕ =>
      (2 * (C * (L / (n + 1 : ℕ)) ^ γ)) *
        (Real.sqrt (2 * Real.pi * (L / (n + 1 : ℕ))))⁻¹)
      atTop (nhds 0) := by
  have hδ : Tendsto (fun n : ℕ => L / (n + 1 : ℕ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat L).comp (tendsto_add_atTop_nat 1)
  have hr := hδ.rpow_const_nhds_zero (sub_pos.mpr hγ)
  have hc : Tendsto (fun _ : ℕ => 2 * C * (Real.sqrt (2 * Real.pi))⁻¹) atTop
      (nhds (2 * C * (Real.sqrt (2 * Real.pi))⁻¹)) := tendsto_const_nhds
  have hmain : Tendsto (fun n : ℕ =>
      (2 * C * (Real.sqrt (2 * Real.pi))⁻¹) *
        (L / (n + 1 : ℕ)) ^ (γ - (2 : ℝ)⁻¹)) atTop (nhds 0) :=
    by simpa using hc.mul hr
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  exact (smallBallHolderBase_eq C (L / (n + 1 : ℕ)) γ (div_pos hL (by positivity))).symm

theorem IsPreBrownianReal.measure_holderOnWith_Icc_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a C : ℝ≥0) {L γ : ℝ≥0} (hL : 0 < L)
    (hγ : (2 : ℝ)⁻¹ < γ) :
    P {ω | HolderOnWith C γ (B · ω) (Icc a (a + L))} = 0 := by
  apply le_antisymm _ bot_le
  let r : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)⁻¹)
  have hr : r < 1 := by simp [r]
  have hpow : Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (nhds 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr).comp (tendsto_add_atTop_nat 1)
  apply ge_of_tendsto hpow
  have hbase := tendsto_smallBallHolderBase (C : ℝ) (L : ℝ) (γ : ℝ)
    (by exact_mod_cast hL) hγ
  have hevent : ∀ᶠ n : ℕ in atTop,
      (2 * ((C : ℝ) * ((L : ℝ) / (n + 1 : ℕ)) ^ (γ : ℝ))) *
        (Real.sqrt (2 * Real.pi * ((L : ℝ) / (n + 1 : ℕ))))⁻¹ ≤ (2 : ℝ)⁻¹ :=
    ((tendsto_order.1 hbase).2 _ (by positivity)).mono fun _ h => h.le
  filter_upwards [hevent] with n hn
  let e : ℝ := (C * (L / (n + 1 : ℕ)) ^ (γ : ℝ) : ℝ≥0)
  have he : 0 ≤ e := by
    exact_mod_cast (show 0 ≤ C * (L / (n + 1 : ℕ)) ^ (γ : ℝ) from bot_le)
  calc
    P {ω | HolderOnWith C γ (B · ω) (Icc a (a + L))} ≤
        P (⋂ i : Fin (n + 1), uniformGridIncrement B a L (n + 1) i ⁻¹' Icc (-e) e) := by
      apply measure_mono
      simpa only [e, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div, NNReal.coe_natCast]
        using holderOnWith_event_subset_uniformGridIncrements
          (B := B) (C := C) (γ := γ) (a := a) (L := L) (Nat.succ_pos n)
    _ ≤ (ENNReal.ofReal ((2 * e) *
          (Real.sqrt (2 * Real.pi * ((L / (n + 1 : ℕ) : ℝ≥0) : ℝ)))⁻¹)) ^ (n + 1) :=
      hB.measure_uniformGridIncrements_Icc_le a hL.ne' (Nat.succ_pos n) e he
    _ ≤ r ^ (n + 1) := by
      apply pow_le_pow_left'
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
      simpa only [e, r, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div,
        NNReal.coe_natCast] using hn

theorem IsPreBrownianReal.ae_not_exists_holderOnWith_Icc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a : ℝ≥0) {L γ : ℝ≥0} (hL : 0 < L)
    (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ¬ ∃ C : ℝ≥0, HolderOnWith C γ (B · ω) (Icc a (a + L)) := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ¬ HolderOnWith (n : ℝ≥0) γ (B · ω) (Icc a (a + L)) := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    simpa only [not_not] using hB.measure_holderOnWith_Icc_eq_zero a n hL hγ
  filter_upwards [hall] with ω hω
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_ge C
  exact hω n (hC.mono_const hn)

theorem exists_nnrat_Icc_subset_of_mem_nhds {t : ℝ≥0} {U : Set ℝ≥0}
    (hU : U ∈ nhds t) :
    ∃ q r : ℚ≥0, q < r ∧ Icc (q : ℝ≥0) (r : ℝ≥0) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨q : ℚ, htq, hq⟩ := exists_rat_btwn
    (show (t : ℝ) < (t : ℝ) + ε / 4 by linarith)
  obtain ⟨r : ℚ, htr, hr⟩ := exists_rat_btwn
    (show (t : ℝ) + ε / 2 < (t : ℝ) + 3 * ε / 4 by linarith)
  let q₀ : ℚ≥0 := ⟨q, by exact_mod_cast (le_trans t.property htq.le)⟩
  let r₀ : ℚ≥0 := ⟨r, by exact_mod_cast (le_trans t.property (by linarith : (t : ℝ) ≤ r))⟩
  refine ⟨q₀, r₀, ?_, ?_⟩
  · exact_mod_cast (by linarith : (q : ℝ) < r)
  · intro s hs
    apply hball
    rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg]
    · have hsr : s ≤ (r₀ : ℝ≥0) := hs.2
      change (s : ℝ) - (t : ℝ) < ε
      have hsle : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hsr
      linarith
    · have hsq : (q₀ : ℝ≥0) ≤ s := hs.1
      have htq₀ : t ≤ (q₀ : ℝ≥0) := by exact_mod_cast htq.le
      exact sub_nonneg.mpr (htq₀.trans hsq)

theorem IsPreBrownianReal.ae_no_nnrat_holderInterval
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {γ : ℝ≥0} (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ∀ q r : ℚ≥0, q < r →
      ¬ ∃ C : ℝ≥0, HolderOnWith C γ (B · ω) (Icc (q : ℝ≥0) (r : ℝ≥0)) := by
  let _ : Countable ℚ≥0 := Subtype.val_injective.countable
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro r
  by_cases hqr : q < r
  · have hL : 0 < (r : ℝ≥0) - (q : ℝ≥0) :=
      tsub_pos_iff_lt.mpr (by exact_mod_cast hqr)
    filter_upwards [hB.ae_not_exists_holderOnWith_Icc (q : ℝ≥0) hL hγ] with ω hω
    intro _
    rintro ⟨C, hC⟩
    apply hω
    refine ⟨C, ?_⟩
    simpa only [add_tsub_cancel_of_le (show (q : ℝ≥0) ≤ (r : ℝ≥0) by exact_mod_cast hqr.le)]
      using hC
  · exact ae_of_all P fun _ h => (hqr h).elim

/-- Almost surely a pre-Brownian path is not uniformly Hoelder of order `γ > 1/2` on any
neighborhood.  This is the uniform-neighborhood precursor to the stronger pointwise PWZ theorem. -/
theorem IsPreBrownianReal.ae_nowhere_locallyHolderOnWith_gt_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {γ : ℝ≥0} (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ¬ ∃ U ∈ nhds t, ∃ C : ℝ≥0, HolderOnWith C γ (B · ω) U := by
  filter_upwards [hB.ae_no_nnrat_holderInterval hγ] with ω hω
  intro t
  rintro ⟨U, hUt, C, hC⟩
  obtain ⟨q, r, hqr, hsub⟩ := exists_nnrat_Icc_subset_of_mem_nhds hUt
  exact hω q r hqr ⟨C, hC.mono hsub⟩

end ProbabilityTheory
