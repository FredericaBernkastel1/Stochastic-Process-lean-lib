/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.PaleyWienerZygmund

/-!
# Pointwise Paley--Wiener--Zygmund theorem

This file internalizes the adjacent-block proof of the pointwise PWZ obstruction.  It strengthens
the uniform-interval result to simultaneous pointwise non-Hoelder regularity and derives nowhere
finite differentiability for real Brownian paths indexed by nonnegative time.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- Pointwise Hoelder control at `t`, with a fixed constant on some neighborhood of `t`. -/
def HolderAtWith (C γ : ℝ≥0) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  ∃ U ∈ nhds t, ∀ s ∈ U, dist (f s) (f t) ≤ C * dist s t ^ (γ : ℝ)

/-- A block of `k` consecutive mesh increments, starting at mesh index `i`. -/
noncomputable def pwzBlockEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ≥0) (k n i : ℕ) (N γ : ℝ≥0) : Set Ω :=
  ⋂ l : Fin k,
    uniformGridIncrement B (a + (i : ℝ≥0) / n) ((k : ℝ≥0) / n) k l ⁻¹'
      Icc (-((N : ℝ) * ((n : ℝ) ⁻¹) ^ (γ : ℝ)))
        ((N : ℝ) * ((n : ℝ) ⁻¹) ^ (γ : ℝ))

/-- The finite union over every possible mesh location in a unit time interval. -/
noncomputable def pwzMeshEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ≥0) (k n : ℕ) (N γ : ℝ≥0) : Set Ω :=
  ⋃ i : Fin (n + 1), pwzBlockEvent B a k n i N γ

theorem div_div_cancel_natCast {k n : ℕ} (hk : 0 < k) :
    ((k : ℝ≥0) / n) / k = (1 : ℝ≥0) / n := by
  rcases n with _ | n
  · norm_num [← Nat.cast_add]
  · apply NNReal.eq
    push_cast
    field_simp

theorem IsPreBrownianReal.measure_pwzBlockEvent_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a : ℝ≥0) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (i : ℕ) (N γ : ℝ≥0) :
    P (pwzBlockEvent B a k n i N γ) ≤
      (ENNReal.ofReal ((2 * ((N : ℝ) * ((n : ℝ)⁻¹) ^ (γ : ℝ))) *
        (Real.sqrt (2 * Real.pi * ((1 : ℝ) / n)))⁻¹)) ^ k := by
  rw [pwzBlockEvent]
  have hL : (k : ℝ≥0) / n ≠ 0 :=
    div_ne_zero (by exact_mod_cast hk.ne') (by exact_mod_cast hn.ne')
  have h := hB.measure_uniformGridIncrements_Icc_le
    (a + (i : ℝ≥0) / n) hL hk
    ((N : ℝ) * ((n : ℝ)⁻¹) ^ (γ : ℝ)) (by positivity)
  rw [div_div_cancel_natCast hk] at h
  simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_inv, one_div] using h

theorem IsPreBrownianReal.measure_pwzMeshEvent_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a : ℝ≥0) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (N γ : ℝ≥0) :
    P (pwzMeshEvent B a k n N γ) ≤
      (n + 1) *
        (ENNReal.ofReal ((2 * ((N : ℝ) * ((n : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((1 : ℝ) / n)))⁻¹)) ^ k := by
  rw [pwzMeshEvent]
  calc
    P (⋃ i : Fin (n + 1), pwzBlockEvent B a k n i N γ) ≤
        ∑ i : Fin (n + 1), P (pwzBlockEvent B a k n i N γ) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n + 1),
        (ENNReal.ofReal ((2 * ((N : ℝ) * ((n : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((1 : ℝ) / n)))⁻¹)) ^ k := by
      gcongr with i
      exact hB.measure_pwzBlockEvent_le a hk hn i N γ
    _ = (n + 1) *
        (ENNReal.ofReal ((2 * ((N : ℝ) * ((n : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((1 : ℝ) / n)))⁻¹)) ^ k := by simp

theorem pwzMeshBoundReal_eq (N γ x : ℝ) (k : ℕ) (hx : 0 < x) :
    x * ((2 * (N * x⁻¹ ^ γ)) * (Real.sqrt (2 * Real.pi * x⁻¹))⁻¹) ^ k =
      (2 * N * (Real.sqrt (2 * Real.pi))⁻¹) ^ k *
        x ^ (1 - (γ - (2 : ℝ)⁻¹) * k) := by
  rw [smallBallHolderBase_eq N x⁻¹ γ (inv_pos.mpr hx)]
  rw [← Real.rpow_neg_eq_inv_rpow]
  rw [mul_pow, ← Real.rpow_mul_natCast (le_of_lt hx)]
  rw [show 1 - (γ - (2 : ℝ)⁻¹) * (k : ℝ) =
      1 + (-(γ - (2 : ℝ)⁻¹)) * k by ring]
  rw [Real.rpow_add hx, Real.rpow_one]
  ring

theorem tendsto_pwzMeshBoundReal (N γ : ℝ) (k : ℕ)
    (hkγ : 1 < (γ - (2 : ℝ)⁻¹) * k) :
    Tendsto (fun n : ℕ =>
      (n + 1 : ℝ) *
        ((2 * (N * ((n + 1 : ℝ)⁻¹) ^ γ)) *
          (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)⁻¹))⁻¹) ^ k)
      atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hexp : 0 < (γ - (2 : ℝ)⁻¹) * k - 1 := sub_pos.mpr hkγ
  have hr := (tendsto_rpow_neg_atTop hexp).comp hx
  have hc : Tendsto (fun _ : ℕ =>
      (2 * N * (Real.sqrt (2 * Real.pi))⁻¹) ^ k) atTop
      (nhds ((2 * N * (Real.sqrt (2 * Real.pi))⁻¹) ^ k)) := tendsto_const_nhds
  have hmain : Tendsto (fun n : ℕ =>
      (2 * N * (Real.sqrt (2 * Real.pi))⁻¹) ^ k *
        (n + 1 : ℝ) ^ (-((γ - (2 : ℝ)⁻¹) * k - 1))) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hc.mul hr
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  rw [show -((γ - (2 : ℝ)⁻¹) * k - 1) =
      1 - (γ - (2 : ℝ)⁻¹) * k by ring]
  exact (pwzMeshBoundReal_eq N γ (n + 1) k (by positivity)).symm

theorem tendsto_pwzMeshCoreBound (N γ : ℝ≥0) (k : ℕ)
    (hkγ : 1 < ((γ : ℝ) - (2 : ℝ)⁻¹) * k) :
    Tendsto (fun n : ℕ =>
      (n + 1 : ℝ≥0∞) *
        (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k)
      atTop (nhds 0) := by
  have hreal := tendsto_pwzMeshBoundReal (N : ℝ) (γ : ℝ) k hkγ
  have hof : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((n + 1 : ℝ) *
        ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹) ^ k)) atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine hof.congr' (Eventually.of_forall fun n => ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow]
  · have hncast : ENNReal.ofReal ((n : ℝ) + 1) = (n : ℝ≥0∞) + 1 := by
      calc
        ENNReal.ofReal ((n : ℝ) + 1) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by norm_num
        _ = ((n + 1 : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
        _ = (n : ℝ≥0∞) + 1 := by norm_num
    rw [hncast]
  · positivity

theorem tendsto_pwzMeshBound (N γ : ℝ≥0) (k : ℕ)
    (hkγ : 1 < ((γ : ℝ) - (2 : ℝ)⁻¹) * k) :
    Tendsto (fun n : ℕ =>
      (n + 2 : ℝ≥0∞) *
        (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
          (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k)
      atTop (nhds 0) := by
  let q : ℕ → ℝ≥0∞ := fun n =>
    (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
      (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k
  have hcore : Tendsto (fun n : ℕ => (n + 1 : ℝ≥0∞) * q n) atTop (nhds 0) := by
    simpa only [q] using tendsto_pwzMeshCoreBound N γ k hkγ
  have hupp : Tendsto (fun n : ℕ => 2 * ((n + 1 : ℝ≥0∞) * q n))
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hcore (Or.inr (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
  · intro n
    exact bot_le
  · intro n
    simp only [q]
    calc
      (n + 2 : ENNReal) *
          (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
            (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k ≤
        (2 * (n + 1 : ENNReal)) *
          (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
            (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k := by
          apply mul_le_mul_left
          exact_mod_cast (show n + 2 ≤ 2 * (n + 1) by omega)
      _ = 2 * ((n + 1 : ENNReal) *
          (ENNReal.ofReal ((2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ))) *
            (Real.sqrt (2 * Real.pi * ((n + 1 : ℝ)⁻¹)))⁻¹)) ^ k) := mul_assoc _ _ _

theorem IsPreBrownianReal.tendsto_measure_pwzMeshEvent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a N γ : ℝ≥0) {k : ℕ} (hk : 0 < k)
    (hkγ : 1 < ((γ : ℝ) - (2 : ℝ)⁻¹) * k) :
    Tendsto (fun n : ℕ => P (pwzMeshEvent B a k (n + 1) N γ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_pwzMeshBound N γ k hkγ)
  · intro n
    exact bot_le
  · intro n
    have h := hB.measure_pwzMeshEvent_le a hk (Nat.succ_pos n) N γ
    norm_num [one_div, Nat.cast_add, Nat.cast_one, add_assoc] at h ⊢
    exact h

theorem IsPreBrownianReal.measure_liminf_pwzMeshEvent_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a N γ : ℝ≥0) {k : ℕ} (hk : 0 < k)
    (hkγ : 1 < ((γ : ℝ) - (2 : ℝ)⁻¹) * k) :
    P (liminf (fun n : ℕ => pwzMeshEvent B a k (n + 1) N γ) atTop) = 0 := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat', iSup_eq_iUnion, measure_iUnion_null_iff]
  intro m
  rw [iInf_eq_iInter]
  apply le_antisymm _ bot_le
  have hlim := (hB.tendsto_measure_pwzMeshEvent a N γ hk hkγ).comp (tendsto_add_atTop_nat m)
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => measure_mono (iInter_subset (fun i =>
    pwzMeshEvent B a k (i + m + 1) N γ) n)

theorem exists_uniform_mesh_bracket (a t : NNReal) (ht : t ∈ Ico a (a + 1))
    {n : ℕ} (hn : 0 < n) :
    ∃ i : Fin (n + 1),
      a + (i : NNReal) / n ≤ t ∧ t < a + ((i : ℕ) + 1 : NNReal) / n := by
  let x : NNReal := (t - a) * n
  have hxlt : x < n := by
    simp only [x]
    have hsub : t - a < 1 := by
      rw [tsub_lt_iff_left ht.1]
      simpa [add_comm] using ht.2
    calc
      (t - a) * (n : NNReal) < 1 * n :=
        mul_lt_mul_of_pos_right hsub (by exact_mod_cast hn)
      _ = n := one_mul _
  have hfloorlt : ⌊x⌋₊ < n := (Nat.floor_lt bot_le).2 hxlt
  let i : Fin (n + 1) := ⟨⌊x⌋₊, hfloorlt.trans (Nat.lt_succ_self n)⟩
  refine ⟨i, ?_, ?_⟩
  · have hfloor : (⌊x⌋₊ : NNReal) ≤ x := Nat.floor_le bot_le
    have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hn.ne'
    have hdiv : (⌊x⌋₊ : NNReal) / n ≤ t - a := by
      apply (div_le_iff₀ (by exact_mod_cast hn)).2
      simpa only [x, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hn0, mul_one] using hfloor
    simpa only [i, add_comm] using (le_tsub_iff_right ht.1).1 hdiv
  · have hlt : x < (⌊x⌋₊ : NNReal) + 1 := Nat.lt_floor_add_one x
    have hn0 : (n : NNReal) ≠ 0 := by exact_mod_cast hn.ne'
    have hdiv : t - a < ((⌊x⌋₊ : NNReal) + 1) / n := by
      apply (lt_div_iff₀ (by exact_mod_cast hn)).2
      simpa only [x, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hn0, mul_one] using hlt
    simpa only [i, Nat.cast_add, Nat.cast_one, add_comm] using
      (tsub_lt_iff_left ht.1).1 hdiv

theorem uniformGrid_block_castSucc (a : NNReal) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (i : ℕ) (l : Fin k) :
    uniformGrid (a + (i : NNReal) / n) ((k : NNReal) / n) k l.castSucc =
      a + ((i + l : ℕ) : NNReal) / n := by
  apply NNReal.eq
  simp only [uniformGrid, Fin.val_castSucc, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_mul, Nat.cast_add]
  field_simp
  ring

theorem uniformGrid_block_succ (a : NNReal) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (i : ℕ) (l : Fin k) :
    uniformGrid (a + (i : NNReal) / n) ((k : NNReal) / n) k l.succ =
      a + ((i + l + 1 : ℕ) : NNReal) / n := by
  apply NNReal.eq
  simp only [uniformGrid, Fin.val_succ, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  push_cast
  ring

theorem dist_mesh_point_le_block (a t : NNReal) {k n i j : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hj : j ≤ k)
    (hleft : a + (i : NNReal) / n ≤ t)
    (hright : t < a + ((i + 1 : ℕ) : NNReal) / n) :
    dist (a + ((i + j : ℕ) : NNReal) / n) t ≤ ((k : NNReal) / n : NNReal) := by
  rw [NNReal.dist_eq, abs_le]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hjR : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hleftR : (a : ℝ) + i / (n : ℝ) ≤ t := by exact_mod_cast hleft
  have hrightR : (t : ℝ) < a + (i + 1 : ℝ) / n := by exact_mod_cast hright
  constructor <;>
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast, Nat.cast_add]
  · have hone : (1 : ℝ) / n ≤ k / n := (div_le_div_iff_of_pos_right hnR).2 hkR
    have hjnonneg : (0 : ℝ) ≤ j / n := div_nonneg (by positivity) hnR.le
    have hij : (i + j : ℝ) / n = i / n + j / n := by field_simp
    have hi1 : (i + 1 : ℝ) / n = i / n + 1 / n := by field_simp
    rw [hij]
    rw [hi1] at hrightR
    linarith
  · have hji : (j : ℝ) / n ≤ k / n := (div_le_div_iff_of_pos_right hnR).2 hjR
    have hij : (i + j : ℝ) / n = i / n + j / n := by field_simp
    rw [hij]
    linarith

theorem holderAtWith_eventually_mem_pwzMeshEvent
    {Ω : Type*} {B : NNReal → Ω → ℝ} {ω : Ω} {a t C γ : NNReal}
    (ht : t ∈ Ico a (a + 1)) (hω : HolderAtWith C γ (B · ω) t)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop,
      ω ∈ pwzMeshEvent B a k (n + 1) (2 * C * (k : NNReal) ^ (γ : ℝ)) γ := by
  obtain ⟨U, hU, hcontrol⟩ := hω
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hsmall : Tendsto (fun n : ℕ => (k : ℝ) / (n + 1 : ℝ)) atTop (nhds 0) :=
    by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hevent : ∀ᶠ n : ℕ in atTop, (k : ℝ) / (n + 1 : ℝ) < ε :=
    (tendsto_order.1 hsmall).2 ε hε
  filter_upwards [hevent] with n hnsmall
  obtain ⟨i, hleft, hright⟩ := exists_uniform_mesh_bracket a t ht (Nat.succ_pos n)
  rw [pwzMeshEvent]
  simp only [mem_iUnion]
  refine ⟨i, ?_⟩
  rw [pwzBlockEvent]
  simp only [mem_iInter]
  intro l
  let x₀ : NNReal := uniformGrid
    (a + (i : NNReal) / ((n + 1 : ℕ) : NNReal))
      ((k : NNReal) / ((n + 1 : ℕ) : NNReal)) k l.castSucc
  let x₁ : NNReal := uniformGrid
    (a + (i : NNReal) / ((n + 1 : ℕ) : NNReal))
      ((k : NNReal) / ((n + 1 : ℕ) : NNReal)) k l.succ
  have hx₀ : x₀ = a + ((i + l : ℕ) : NNReal) / ((n + 1 : ℕ) : NNReal) :=
    by simpa only [Nat.succ_eq_add_one] using
      uniformGrid_block_castSucc a hk (Nat.succ_pos n) i l
  have hx₁ : x₁ = a + ((i + l + 1 : ℕ) : NNReal) / ((n + 1 : ℕ) : NNReal) :=
    by simpa only [Nat.succ_eq_add_one] using
      uniformGrid_block_succ a hk (Nat.succ_pos n) i l
  have hright' : t < a + (((i : ℕ) + 1 : ℕ) : NNReal) /
      ((n + 1 : ℕ) : NNReal) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using hright
  have hd₀ : dist x₀ t ≤ ((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) := by
    rw [hx₀]
    exact dist_mesh_point_le_block a t hk (Nat.succ_pos n) (i := (i : ℕ)) (j := (l : ℕ))
      l.is_lt.le hleft hright'
  have hd₁ : dist x₁ t ≤ ((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) := by
    rw [hx₁]
    simpa only [Nat.add_assoc] using
      dist_mesh_point_le_block a t hk (Nat.succ_pos n) (i := i) (j := l + 1)
        (Nat.succ_le_of_lt l.is_lt) hleft hright'
  have hx₀U : x₀ ∈ U := hball (by
    rw [Metric.mem_ball]
    exact hd₀.trans_lt (by exact_mod_cast hnsmall))
  have hx₁U : x₁ ∈ U := hball (by
    rw [Metric.mem_ball]
    exact hd₁.trans_lt (by exact_mod_cast hnsmall))
  have hpow₀ : dist x₀ t ^ (γ : ℝ) ≤
      (((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) : ℝ) ^ (γ : ℝ) :=
    Real.rpow_le_rpow (dist_nonneg) hd₀ (γ.property)
  have hpow₁ : dist x₁ t ^ (γ : ℝ) ≤
      (((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) : ℝ) ^ (γ : ℝ) :=
    Real.rpow_le_rpow (dist_nonneg) hd₁ (γ.property)
  have hc₀ := hcontrol x₀ hx₀U
  have hc₁ := hcontrol x₁ hx₁U
  have habs : |B x₁ ω - B x₀ ω| ≤
      ((2 * C * (k : NNReal) ^ (γ : ℝ) : NNReal) : ℝ) *
        ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
    rw [← Real.dist_eq]
    calc
      dist (B x₁ ω) (B x₀ ω) ≤ dist (B x₁ ω) (B t ω) + dist (B x₀ ω) (B t ω) :=
        dist_triangle_right _ _ _
      _ ≤ (C : ℝ) * (((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) : ℝ) ^ (γ : ℝ) +
          (C : ℝ) * (((k : NNReal) / ((n + 1 : ℕ) : NNReal) : NNReal) : ℝ) ^ (γ : ℝ) := by
        exact add_le_add
          (hc₁.trans (mul_le_mul_of_nonneg_left hpow₁ C.property))
          (hc₀.trans (mul_le_mul_of_nonneg_left hpow₀ C.property))
      _ = ((2 * C * (k : NNReal) ^ (γ : ℝ) : NNReal) : ℝ) *
          ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_rpow, NNReal.coe_natCast,
          NNReal.coe_div]
        rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
        norm_num [Nat.cast_add, Nat.cast_one, add_comm]
        ring
  simp only [Set.mem_preimage]
  simpa only [uniformGridIncrement, x₀, x₁, mem_Icc, Nat.cast_add, Nat.cast_one] using
    (abs_le.mp habs)

theorem exists_nat_pwz_exponent {γ : NNReal} (hγ : (2 : ℝ)⁻¹ < γ) :
    ∃ k : ℕ, 0 < k ∧ 1 < ((γ : ℝ) - (2 : ℝ)⁻¹) * k := by
  let d : ℝ := (γ : ℝ) - (2 : ℝ)⁻¹
  have hd : 0 < d := sub_pos.mpr hγ
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / d)
  refine ⟨k, ?_, ?_⟩
  · by_contra hk0
    simp only [not_lt, nonpos_iff_eq_zero] at hk0
    subst k
    simpa using (div_pos zero_lt_one hd).trans hk
  · change 1 < d * (k : ℝ)
    calc
      1 = d * (1 / d) := by field_simp
      _ < d * (k : ℝ) := mul_lt_mul_of_pos_left hk hd

theorem HolderAtWith.mono_const {C D γ : NNReal} {f : NNReal → ℝ} {t : NNReal}
    (h : HolderAtWith C γ f t) (hCD : C ≤ D) : HolderAtWith D γ f t := by
  obtain ⟨U, hU, hf⟩ := h
  refine ⟨U, hU, fun s hs => (hf s hs).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCD)
    (Real.rpow_nonneg (dist_nonneg) _)

theorem IsPreBrownianReal.measure_exists_holderAtWith_Ico_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a C : NNReal) {γ : NNReal}
    (hγ : (2 : ℝ)⁻¹ < γ) :
    P {ω | ∃ t ∈ Ico a (a + 1), HolderAtWith C γ (B · ω) t} = 0 := by
  obtain ⟨k, hk, hkγ⟩ := exists_nat_pwz_exponent hγ
  let N : NNReal := 2 * C * (k : NNReal) ^ (γ : ℝ)
  apply le_antisymm _ bot_le
  calc
    P {ω | ∃ t ∈ Ico a (a + 1), HolderAtWith C γ (B · ω) t} ≤
        P (liminf (fun n : ℕ => pwzMeshEvent B a k (n + 1) N γ) atTop) := by
      apply measure_mono
      intro ω hω
      obtain ⟨t, ht, hholder⟩ := hω
      rw [mem_liminf_iff_eventually_mem]
      simpa only [N] using holderAtWith_eventually_mem_pwzMeshEvent ht hholder hk
    _ = 0 := hB.measure_liminf_pwzMeshEvent_eq_zero a N γ hk hkγ

theorem IsPreBrownianReal.ae_no_holderAtWith_on_unitInterval
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (a : NNReal) {γ : NNReal}
    (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Ico a (a + 1), ∀ C : NNReal,
      ¬ HolderAtWith C γ (B · ω) t := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ¬ ∃ t ∈ Ico a (a + 1), HolderAtWith (n : NNReal) γ (B · ω) t := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    simpa only [not_not] using
      hB.measure_exists_holderAtWith_Ico_eq_zero a n hγ
  filter_upwards [hall] with ω hω
  intro t ht C hholder
  obtain ⟨n, hn⟩ := exists_nat_ge C
  exact hω n ⟨t, ht, hholder.mono_const hn⟩

/-- Paley--Wiener--Zygmund: almost every real Brownian path is pointwise non-Hoelder of every
order strictly larger than one half, at every nonnegative time. -/
theorem IsPreBrownianReal.ae_nowhere_holderAtWith_gt_half
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {γ : NNReal} (hγ : (2 : ℝ)⁻¹ < γ) :
    ∀ᵐ ω ∂P, ∀ t C : NNReal, ¬ HolderAtWith C γ (B · ω) t := by
  have hall : ∀ᵐ ω ∂P, ∀ a : ℕ, ∀ t ∈ Ico (a : NNReal) ((a : NNReal) + 1),
      ∀ C : NNReal, ¬ HolderAtWith C γ (B · ω) t := by
    rw [ae_all_iff]
    intro a
    exact hB.ae_no_holderAtWith_on_unitInterval a hγ
  filter_upwards [hall] with ω hω
  intro t C
  let a : ℕ := ⌊t⌋₊
  apply hω a t
  constructor
  · exact Nat.floor_le bot_le
  · exact Nat.lt_floor_add_one t

/-- Difference quotient used for differentiability of paths whose time domain is `NNReal`. -/
noncomputable def nnrealDifferenceQuotient (f : NNReal → ℝ) (t s : NNReal) : ℝ :=
  if s = t then 0 else (f s - f t) / ((s : ℝ) - (t : ℝ))

/-- Existence of a finite derivative along the relative topology of nonnegative time. -/
def HasFiniteDerivativeAt (f : NNReal → ℝ) (t : NNReal) : Prop :=
  ∃ d : ℝ, Tendsto (nnrealDifferenceQuotient f t) (nhds t) (nhds d)

theorem HasFiniteDerivativeAt.holderAtWith_one {f : NNReal → ℝ} {t : NNReal}
    (h : HasFiniteDerivativeAt f t) :
    ∃ C : NNReal, HolderAtWith C 1 f t := by
  obtain ⟨d, hd⟩ := h
  let C : NNReal := ⟨|d| + 1, by positivity⟩
  let U : Set NNReal := {s | dist (nnrealDifferenceQuotient f t s) d < 1}
  have hU : U ∈ nhds t := by
    exact hd (Metric.ball_mem_nhds d zero_lt_one)
  refine ⟨C, U, hU, ?_⟩
  intro s hs
  by_cases hst : s = t
  · subst s
    simp
  · have hslope : |nnrealDifferenceQuotient f t s| ≤ |d| + 1 := by
      have hdist : |nnrealDifferenceQuotient f t s - d| < 1 := by
        simpa only [U, Set.mem_ofPred_eq, Real.dist_eq] using hs
      calc
        |nnrealDifferenceQuotient f t s| =
            |(nnrealDifferenceQuotient f t s - d) + d| := by ring_nf
        _ ≤ |nnrealDifferenceQuotient f t s - d| + |d| := abs_add_le _ _
        _ ≤ |d| + 1 := by linarith
    have hden : (s : ℝ) - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hst)
    have hfactor : f s - f t =
        nnrealDifferenceQuotient f t s * ((s : ℝ) - (t : ℝ)) := by
      simp only [nnrealDifferenceQuotient, if_neg hst]
      field_simp
    rw [Real.dist_eq, NNReal.dist_eq, hfactor, abs_mul]
    simp only [NNReal.coe_one, Real.rpow_one]
    change |nnrealDifferenceQuotient f t s| * |(s : ℝ) - (t : ℝ)| ≤
      (|d| + 1) * |(s : ℝ) - (t : ℝ)|
    exact mul_le_mul_of_nonneg_right hslope (abs_nonneg _)

/-- Almost every real Brownian path has no finite derivative at any nonnegative time. -/
theorem IsPreBrownianReal.ae_nowhere_hasFiniteDerivativeAt
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : NNReal, ¬ HasFiniteDerivativeAt (B · ω) t := by
  have hPWZ := hB.ae_nowhere_holderAtWith_gt_half
    (γ := (1 : NNReal)) (by norm_num)
  filter_upwards [hPWZ] with ω hω
  intro t hdiff
  obtain ⟨C, hholder⟩ := hdiff.holderAtWith_one
  exact hω t C hholder

end ProbabilityTheory
