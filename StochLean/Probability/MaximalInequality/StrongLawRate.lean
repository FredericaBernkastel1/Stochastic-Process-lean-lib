/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.MaximalInequality.Kolmogorov
public import Mathlib.Analysis.PSeries

/-!
# Kolmogorov--Borel--Cantelli rate principle

This module isolates the rate argument following Kolmogorov's maximal inequality.  The first
lemma is a reusable countable-threshold form of the first Borel--Cantelli lemma; later results
specialize it to independent centered partial sums.
-/

@[expose] public section

open Finset Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Squared dyadic normalization used in Klenke's rate proof.  On the horizon `2^(n+1)` it is
`2^(n+1) * (n+1)^(1+2ε)`. -/
noncomputable def dyadicRateSq (ε : ℝ) (n : ℕ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (n + 1) * (n + 1 : ℝ≥0) ^ (1 + 2 * ε)

/-- Positive square root of `dyadicRateSq`. -/
noncomputable def dyadicRate (ε : ℝ) (n : ℕ) : ℝ≥0 :=
  NNReal.sqrt (dyadicRateSq ε n)

@[simp]
theorem dyadicRate_sq (ε : ℝ) (n : ℕ) : dyadicRate ε n ^ 2 = dyadicRateSq ε n := by
  exact NNReal.sq_sqrt _

/-- Maximum squared partial sum through the dyadic horizon `2^(n+1)`. -/
noncomputable def dyadicMaxSq (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (range (2 ^ (n + 1) - 1 + 1)).sup' nonempty_range_add_one
    fun k => partialSum X (k + 1) ω ^ 2

theorem dyadicMaxSq_nonneg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicMaxSq X n ω := by
  apply (sq_nonneg (partialSum X 1 ω)).trans
  unfold dyadicMaxSq
  apply Finset.le_sup' (fun k => partialSum X (k + 1) ω ^ 2)
  simp

/-- Dyadic maximal partial sum normalized at Klenke's rate. -/
noncomputable def dyadicNormalizedMax (X : ℕ → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (dyadicMaxSq X n ω) / dyadicRate ε n

theorem dyadicNormalizedMax_nonneg (X : ℕ → Ω → ℝ) (ε : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicNormalizedMax X ε n ω := by
  exact div_nonneg (Real.sqrt_nonneg _) (dyadicRate ε n).2

private lemma dyadicRate_pos (ε : ℝ) (n : ℕ) : 0 < (dyadicRate ε n : ℝ) := by
  have hsq : 0 < dyadicRateSq ε n := by
    exact mul_pos (by positivity) (NNReal.rpow_pos (by positivity))
  exact_mod_cast NNReal.sqrt_pos.mpr hsq

/-- A normalized dyadic maximal event is exactly the squared event used by Kolmogorov's
inequality. -/
theorem dyadicNormalizedMax_ge_iff (X : ℕ → Ω → ℝ) (ε : ℝ) (δ : ℝ≥0)
    (n : ℕ) (ω : Ω) :
    (δ : ℝ) ≤ dyadicNormalizedMax X ε n ω ↔
      (((δ * dyadicRate ε n : ℝ≥0) : ℝ) ^ 2 ≤ dyadicMaxSq X n ω) := by
  rw [dyadicNormalizedMax]
  constructor
  · intro h
    have h' := (le_div_iff₀ (dyadicRate_pos ε n)).mp h
    have hs := (Real.le_sqrt (mul_nonneg δ.2 (dyadicRate_pos ε n).le)
      (dyadicMaxSq_nonneg X n ω)).mp h'
    change ((δ : ℝ) * (dyadicRate ε n : ℝ)) ^ 2 ≤ dyadicMaxSq X n ω
    exact hs
  · intro h
    apply (le_div_iff₀ (dyadicRate_pos ε n)).mpr
    apply (Real.le_sqrt (mul_nonneg δ.2 (dyadicRate_pos ε n).le)
      (dyadicMaxSq_nonneg X n ω)).mpr
    change ((δ : ℝ) * (dyadicRate ε n : ℝ)) ^ 2 ≤ dyadicMaxSq X n ω at h
    exact h

/-- If every reciprocal threshold is exceeded only finitely often almost surely, a nonnegative
sequence converges to zero almost surely.  Summability of the corresponding event measures is
packaged in exactly the form consumed by the first Borel--Cantelli lemma. -/
theorem ae_tendsto_zero_of_tsum_measure_ge_ne_top (Y : ℕ → Ω → ℝ)
    (hY : ∀ n ω, 0 ≤ Y n ω)
    (hsum : ∀ m : ℕ, (∑' n, P {ω | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Y n ω}) ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 0) := by
  have hAE : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ᶠ n : ℕ in atTop,
      ω ∉ {ω | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Y n ω} :=
    ae_all_iff.mpr fun m => ae_eventually_notMem (hsum m)
  filter_upwards [hAE] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m : ℕ, hm⟩ : ∃ m : ℕ, ((m + 1 : ℕ) : ℝ)⁻¹ < ε := by
    convert exists_nat_one_div_lt hε using 1
    norm_num
  obtain ⟨N, hN⟩ := (hω m).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hnot := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hY n ω)]
  exact (lt_of_not_ge hnot).trans hm

/-- Kolmogorov's inequality on a dyadic block, with a uniform variance bound. -/
theorem measure_dyadicMaxSq_ge_le [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    (ε : ℝ) (δ : ℝ≥0) (hδ : δ ≠ 0) (n : ℕ) :
    P {ω | (((δ * dyadicRate ε n : ℝ≥0) : ℝ) ^ 2 ≤ dyadicMaxSq X n ω)} ≤
      ENNReal.ofReal (((2 : ℝ) ^ (n + 1)) * V) /
        ((δ * dyadicRate ε n : ℝ≥0) : ℝ≥0∞) ^ 2 := by
  have hN : 2 ^ (n + 1) - 1 + 1 = 2 ^ (n + 1) := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
  have hK := kolmogorov_maximal_ineq_div hXstrong hX2 hcenter hindep
    (δ * dyadicRate ε n) (mul_ne_zero hδ (by simp [dyadicRate, dyadicRateSq]))
    (2 ^ (n + 1) - 1)
  refine hK.trans ?_
  gcongr
  calc
    ∑ i ∈ range (2 ^ (n + 1) - 1 + 1), Var[X i; P] ≤
        ∑ _i ∈ range (2 ^ (n + 1) - 1 + 1), (V : ℝ) := by
      exact sum_le_sum fun i _ => hvar i
    _ = ((2 ^ (n + 1) - 1 + 1 : ℕ) : ℝ) * V := by simp
    _ = ((2 : ℝ) ^ (n + 1)) * V := by rw [hN]; norm_cast

private lemma dyadicKolmogorovBound_eq (V δ : ℝ≥0) (hδ : δ ≠ 0) (ε : ℝ) (n : ℕ) :
    ENNReal.ofReal (((2 : ℝ) ^ (n + 1)) * V) /
        ((δ * dyadicRate ε n : ℝ≥0) : ℝ≥0∞) ^ 2 =
      ((V / δ ^ 2 / (n + 1 : ℝ≥0) ^ (1 + 2 * ε) : ℝ≥0) : ℝ≥0∞) := by
  have hrate : (δ * dyadicRate ε n) ^ 2 =
      δ ^ 2 * ((2 : ℝ≥0) ^ (n + 1) * (n + 1 : ℝ≥0) ^ (1 + 2 * ε)) := by
    rw [mul_pow, dyadicRate_sq, dyadicRateSq]
  have hpow : (n + 1 : ℝ≥0) ^ (1 + 2 * ε) ≠ 0 :=
    (NNReal.rpow_pos (by positivity)).ne'
  have htwo : (2 : ℝ≥0) ^ (n + 1) ≠ 0 := by positivity
  have hden : (δ * dyadicRate ε n) ^ 2 ≠ 0 := by
    rw [hrate]
    exact mul_ne_zero (pow_ne_zero 2 hδ) (mul_ne_zero htwo hpow)
  have hnn :
      ((2 : ℝ≥0) ^ (n + 1) * V) / (δ * dyadicRate ε n) ^ 2 =
        V / δ ^ 2 / (n + 1 : ℝ≥0) ^ (1 + 2 * ε) := by
    rw [hrate]
    field_simp [hδ, htwo, hpow]
  rw [show ENNReal.ofReal (((2 : ℝ) ^ (n + 1)) * V) =
      (((2 : ℝ≥0) ^ (n + 1) * V : ℝ≥0) : ℝ≥0∞) by norm_num,
    ← ENNReal.coe_pow, ← ENNReal.coe_div]
  · exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hnn
  · exact hden

/-- The dyadic maximal events are summable when the variances are uniformly bounded and the
logarithmic exponent is positive. -/
theorem tsum_measure_dyadicNormalizedMax_ge_ne_top [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (∑' n, P {ω | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ dyadicNormalizedMax X ε n ω}) ≠ ∞ := by
  let δ : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0)⁻¹
  have hδ : δ ≠ 0 := by simp [δ]
  have hpoint : ∀ n,
      P {ω | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ dyadicNormalizedMax X ε n ω} ≤
        (((V / δ ^ 2) * (n + 1 : ℝ≥0) ^ (-(1 + 2 * ε)) : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have hbound := measure_dyadicMaxSq_ge_le hXstrong hX2 hcenter hindep V hvar ε δ hδ n
    rw [dyadicKolmogorovBound_eq V δ hδ ε n] at hbound
    have hevent : {ω | ((m + 1 : ℕ) : ℝ)⁻¹ ≤ dyadicNormalizedMax X ε n ω} =
        {ω | (((δ * dyadicRate ε n : ℝ≥0) : ℝ) ^ 2 ≤ dyadicMaxSq X n ω)} := by
      ext ω
      change ((m + 1 : ℕ) : ℝ)⁻¹ ≤ dyadicNormalizedMax X ε n ω ↔
        (((δ * dyadicRate ε n : ℝ≥0) : ℝ) ^ 2 ≤ dyadicMaxSq X n ω)
      simpa only [δ, NNReal.coe_inv, NNReal.coe_natCast] using
        dyadicNormalizedMax_ge_iff X ε δ n ω
    rw [hevent]
    simpa only [div_eq_mul_inv, NNReal.rpow_neg] using hbound
  have hp : -(1 + 2 * ε) < (-1 : ℝ) := by linarith
  have hs0 : Summable (fun n : ℕ => (n : ℝ≥0) ^ (-(1 + 2 * ε))) :=
    NNReal.summable_rpow.mpr hp
  have hs1 : Summable (fun n : ℕ => (n + 1 : ℝ≥0) ^ (-(1 + 2 * ε))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      NNReal.summable_nat_add (fun n : ℕ => (n : ℝ≥0) ^ (-(1 + 2 * ε))) hs0 1
  have hs : Summable (fun n : ℕ =>
      (V / δ ^ 2) * (n + 1 : ℝ≥0) ^ (-(1 + 2 * ε))) := by
    exact hs1.mul_left (V / δ ^ 2)
  have htop : (∑' n : ℕ,
      ((((V / δ ^ 2) * (n + 1 : ℝ≥0) ^ (-(1 + 2 * ε))) : ℝ≥0) : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr (NNReal.summable_coe.mpr hs)
  have hle := ENNReal.summable.tsum_le_tsum hpoint ENNReal.summable
  exact (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr htop)).ne

/-- Borel--Cantelli consequence: the normalized dyadic maxima converge almost surely to zero. -/
theorem tendsto_dyadicNormalizedMax_ae [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicNormalizedMax X ε n ω) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_tsum_measure_ge_ne_top (dyadicNormalizedMax X ε)
  · exact dyadicNormalizedMax_nonneg X ε
  · exact tsum_measure_dyadicNormalizedMax_ge_ne_top hXstrong hX2 hcenter hindep V hvar hε

private theorem tendsto_log2_atTop : Tendsto Nat.log2 atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with n hn
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  exact (Nat.le_log2 hn0).mpr hn

/-- Every partial sum is controlled by the dyadic maximal block selected by `Nat.log2`. -/
theorem normalizedPartialSum_le_dyadicNormalizedMax (X : ℕ → Ω → ℝ)
    (ε : ℝ) (n : ℕ) (ω : Ω) :
    |partialSum X n ω| / (dyadicRate ε (Nat.log2 n) : ℝ) ≤
      dyadicNormalizedMax X ε (Nat.log2 n) ω := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa [partialSum] using dyadicNormalizedMax_nonneg X ε 0 ω
  have hN : 2 ^ (Nat.log2 n + 1) - 1 + 1 = 2 ^ (Nat.log2 n + 1) := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
  have hnlt : n < 2 ^ (Nat.log2 n + 1) := by
    simpa only [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hmem : n - 1 ∈ range (2 ^ (Nat.log2 n + 1) - 1 + 1) := by
    simp only [mem_range, hN]
    omega
  have hsq : partialSum X n ω ^ 2 ≤ dyadicMaxSq X (Nat.log2 n) ω := by
    unfold dyadicMaxSq
    have h := Finset.le_sup'
      (fun k => partialSum X (k + 1) ω ^ 2) hmem
    simpa only [Nat.sub_add_cancel hn] using h
  apply div_le_div_of_nonneg_right (Real.abs_le_sqrt hsq)
  exact (dyadicRate ε (Nat.log2 n)).2

/-- Klenke 5.29 in its exact dyadic-envelope form.  The denominator is the square root of
`2^(log₂ n + 1) * (log₂ n + 1)^(1+2ε)`, the blockwise envelope used in the proof and
asymptotically equivalent to `sqrt n * (log n)^(1/2+ε)`. -/
theorem kolmogorov_strongLaw_rate_dyadicEnvelope [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => |partialSum X n ω| / (dyadicRate ε (Nat.log2 n) : ℝ)) atTop (𝓝 0) := by
  filter_upwards [tendsto_dyadicNormalizedMax_ae hXstrong hX2 hcenter hindep V hvar hε]
    with ω hω
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (dyadicRate _ _).2
  · exact Eventually.of_forall fun n => normalizedPartialSum_le_dyadicNormalizedMax X ε n ω
  · exact hω.comp tendsto_log2_atTop

/-- The textbook rate with logarithm to base two.  Changing the logarithm base only multiplies
this by a fixed positive constant. -/
noncomputable def klenkeLog2Rate (ε : ℝ) (n : ℕ) : ℝ≥0 :=
  NNReal.sqrt n * (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε)

@[simp]
theorem klenkeLog2Rate_sq (ε : ℝ) (n : ℕ) :
    klenkeLog2Rate ε n ^ 2 =
      (n : ℝ≥0) * (Nat.log2 n : ℝ≥0) ^ (1 + 2 * ε) := by
  rw [klenkeLog2Rate, mul_pow, NNReal.sq_sqrt, ← NNReal.rpow_natCast,
    ← NNReal.rpow_mul]
  congr 2
  ring

private theorem eventually_dyadicRate_half_le_klenkeLog2Rate {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      dyadicRate (ε / 2) (Nat.log2 n) ≤ klenkeLog2Rate ε n := by
  have hjtop : Tendsto (fun n : ℕ => (Nat.log2 n : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_log2_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ≥0) ^ (2 + ε) ≤ (Nat.log2 n : ℝ≥0) ^ ε :=
    (Filter.tendsto_atTop.mp ((NNReal.tendsto_rpow_atTop hε).comp hjtop))
      ((2 : ℝ≥0) ^ (2 + ε))
  have hjone : ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.log2 n :=
    (Filter.tendsto_atTop.mp tendsto_log2_atTop) 1
  filter_upwards [hlarge, hjone] with n hnlarge hj
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    simp at hj
  have hpowNat : 2 ^ Nat.log2 n ≤ n := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn0
  have hpow : (2 : ℝ≥0) ^ Nat.log2 n ≤ n := by exact_mod_cast hpowNat
  have htwoPow : (2 : ℝ≥0) ^ (Nat.log2 n + 1) ≤ 2 * n := by
    rw [pow_succ, mul_comm]
    gcongr
  have hjadd : (Nat.log2 n + 1 : ℝ≥0) ≤ 2 * Nat.log2 n := by
    norm_cast
    omega
  apply (sq_le_sq₀ (show (0 : ℝ≥0) ≤ dyadicRate (ε / 2) (Nat.log2 n) from bot_le)
    (show (0 : ℝ≥0) ≤ klenkeLog2Rate ε n from bot_le)).mp
  rw [dyadicRate_sq, dyadicRateSq, klenkeLog2Rate_sq]
  have hexp : 1 + 2 * (ε / 2) = 1 + ε := by ring
  rw [hexp]
  calc
    (2 : ℝ≥0) ^ (Nat.log2 n + 1) *
          (Nat.log2 n + 1 : ℝ≥0) ^ (1 + ε) ≤
        (2 * n) * (2 * Nat.log2 n : ℝ≥0) ^ (1 + ε) := by
      exact mul_le_mul htwoPow (NNReal.rpow_le_rpow hjadd (by linarith)) (by positivity)
        (by positivity)
    _ = (2 : ℝ≥0) ^ (2 + ε) * n *
          (Nat.log2 n : ℝ≥0) ^ (1 + ε) := by
      have hconst : (2 : ℝ≥0) * (2 : ℝ≥0) ^ (1 + ε) =
          (2 : ℝ≥0) ^ (2 + ε) := by
        calc
          (2 : ℝ≥0) * (2 : ℝ≥0) ^ (1 + ε) =
              (2 : ℝ≥0) ^ (1 : ℝ) * (2 : ℝ≥0) ^ (1 + ε) := by simp
          _ = (2 : ℝ≥0) ^ ((1 : ℝ) + (1 + ε)) :=
            (NNReal.rpow_add (by norm_num) 1 (1 + ε)).symm
          _ = (2 : ℝ≥0) ^ (2 + ε) := by congr 1; ring
      rw [NNReal.mul_rpow, ← hconst]
      ring
    _ ≤ (Nat.log2 n : ℝ≥0) ^ ε * n *
          (Nat.log2 n : ℝ≥0) ^ (1 + ε) := by gcongr
    _ = (n : ℝ≥0) * (Nat.log2 n : ℝ≥0) ^ (1 + 2 * ε) := by
      have hj0 : (Nat.log2 n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
      have hpowcombine : (Nat.log2 n : ℝ≥0) ^ ε *
          (Nat.log2 n : ℝ≥0) ^ (1 + ε) =
          (Nat.log2 n : ℝ≥0) ^ (1 + 2 * ε) := by
        calc
          (Nat.log2 n : ℝ≥0) ^ ε * (Nat.log2 n : ℝ≥0) ^ (1 + ε) =
              (Nat.log2 n : ℝ≥0) ^ (ε + (1 + ε)) :=
            (NNReal.rpow_add hj0 ε (1 + ε)).symm
          _ = (Nat.log2 n : ℝ≥0) ^ (1 + 2 * ε) := by congr 1; ring
      rw [← hpowcombine]
      ring

/-- Klenke 5.29 with logarithm to base two. -/
theorem kolmogorov_strongLaw_rate_log2 [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => |partialSum X n ω| / (klenkeLog2Rate ε n : ℝ)) atTop (𝓝 0) := by
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [kolmogorov_strongLaw_rate_dyadicEnvelope hXstrong hX2 hcenter hindep
    V hvar hhalf] with ω hω
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (klenkeLog2Rate _ _).2
  · filter_upwards [eventually_dyadicRate_half_le_klenkeLog2Rate hε] with n hn
    apply div_le_div_of_nonneg_left (abs_nonneg _)
      (dyadicRate_pos (ε / 2) (Nat.log2 n))
    exact_mod_cast hn
  · exact hω

/-- The natural logarithm of a natural number, bundled as a nonnegative real. -/
noncomputable def natLogNNReal (n : ℕ) : ℝ≥0 :=
  ⟨Real.log n, Real.log_natCast_nonneg n⟩

/-- The literal normalization in Klenke 5.29:
`sqrt n * (log n)^(1/2+ε)`. -/
noncomputable def klenkeStrongLawRate (ε : ℝ) (n : ℕ) : ℝ≥0 :=
  NNReal.sqrt n * natLogNNReal n ^ ((1 : ℝ) / 2 + ε)

@[simp, norm_cast]
theorem coe_natLogNNReal (n : ℕ) : (natLogNNReal n : ℝ) = Real.log n := rfl

@[simp]
theorem coe_klenkeStrongLawRate (ε : ℝ) (n : ℕ) :
    (klenkeStrongLawRate ε n : ℝ) =
      Real.sqrt n * Real.log n ^ ((1 : ℝ) / 2 + ε) := by
  rw [klenkeStrongLawRate, NNReal.coe_mul, Real.coe_sqrt, NNReal.coe_rpow,
    coe_natLogNNReal]
  norm_num

private theorem eventually_klenkeLog2Rate_half_le_naturalRate {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, klenkeLog2Rate (ε / 2) n ≤ klenkeStrongLawRate ε n := by
  let c : ℝ≥0 := ⟨Real.log 2, Real.log_nonneg (by norm_num)⟩
  have hcpos : 0 < c := by
    change 0 < Real.log 2
    exact Real.log_pos (by norm_num)
  have hjtop : Tendsto (fun n : ℕ => (Nat.log2 n : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_log2_atTop
  have hdiff : 0 < ε / 2 := by positivity
  have hlarge : ∀ᶠ n : ℕ in atTop,
      c ^ (-((1 : ℝ) / 2 + ε)) ≤ (Nat.log2 n : ℝ≥0) ^ (ε / 2) :=
    (Filter.tendsto_atTop.mp ((NNReal.tendsto_rpow_atTop hdiff).comp hjtop))
      (c ^ (-((1 : ℝ) / 2 + ε)))
  have hjone : ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.log2 n :=
    (Filter.tendsto_atTop.mp tendsto_log2_atTop) 1
  filter_upwards [hlarge, hjone] with n hnlarge hj
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    simp at hj
  have hpowNat : 2 ^ Nat.log2 n ≤ n := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn0
  have hlog : (Nat.log2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpowNat)
  have hlogNN : c * (Nat.log2 n : ℝ≥0) ≤ natLogNNReal n := by
    change Real.log 2 * (Nat.log2 n : ℝ) ≤ Real.log n
    simpa only [mul_comm] using hlog
  have hj0 : (Nat.log2 n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hc0 : c ≠ 0 := hcpos.ne'
  have hsplit : (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε) =
      (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) *
        (Nat.log2 n : ℝ≥0) ^ (ε / 2) := by
    calc
      (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε) =
          (Nat.log2 n : ℝ≥0) ^ (((1 : ℝ) / 2 + ε / 2) + ε / 2) := by
        congr 1
        ring
      _ = _ := NNReal.rpow_add hj0 _ _
  have hcinv : c ^ ((1 : ℝ) / 2 + ε) * c ^ (-((1 : ℝ) / 2 + ε)) = 1 := by
    rw [← NNReal.rpow_add hc0]
    simp
  have hprod : 1 ≤ c ^ ((1 : ℝ) / 2 + ε) *
      (Nat.log2 n : ℝ≥0) ^ (ε / 2) := by
    rw [← hcinv]
    exact mul_le_mul_of_nonneg_left hnlarge (by positivity)
  have hpower : (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) ≤
      (c * (Nat.log2 n : ℝ≥0)) ^ ((1 : ℝ) / 2 + ε) := by
    rw [NNReal.mul_rpow, hsplit]
    calc
      (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) =
          1 * (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) := by simp
      _ ≤ (c ^ ((1 : ℝ) / 2 + ε) * (Nat.log2 n : ℝ≥0) ^ (ε / 2)) *
          (Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = c ^ ((1 : ℝ) / 2 + ε) *
          ((Nat.log2 n : ℝ≥0) ^ ((1 : ℝ) / 2 + ε / 2) *
            (Nat.log2 n : ℝ≥0) ^ (ε / 2)) := by ring
  rw [klenkeLog2Rate, klenkeStrongLawRate]
  gcongr
  exact hpower.trans (NNReal.rpow_le_rpow hlogNN (by linarith))

/-- **Klenke 5.29.** For independent centered real variables with uniformly bounded variance,
the partial sums are `o(sqrt n * (log n)^(1/2+ε))` almost surely for every `ε > 0`. -/
theorem kolmogorov_strongLaw_rate [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hX2 : ∀ i, MemLp (X i) 2 P) (hcenter : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hindep : iIndepFun X P) (V : ℝ≥0) (hvar : ∀ i, Var[X i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => |partialSum X n ω| /
        (Real.sqrt n * Real.log n ^ ((1 : ℝ) / 2 + ε))) atTop (𝓝 0) := by
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [kolmogorov_strongLaw_rate_log2 hXstrong hX2 hcenter hindep V hvar hhalf]
    with ω hω
  suffices h : Tendsto (fun n => |partialSum X n ω| / (klenkeStrongLawRate ε n : ℝ))
      atTop (𝓝 0) by
    simpa only [coe_klenkeStrongLawRate] using h
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (klenkeStrongLawRate _ _).2
  · filter_upwards [eventually_klenkeLog2Rate_half_le_naturalRate hε,
      (Filter.tendsto_atTop.mp tendsto_log2_atTop) 1] with n hn hj
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      simp at hj
    have hsource : 0 < klenkeLog2Rate (ε / 2) n := by
      rw [klenkeLog2Rate]
      exact mul_pos (NNReal.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0))
        (NNReal.rpow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)))
    apply div_le_div_of_nonneg_left (abs_nonneg _)
      (by exact_mod_cast hsource)
    exact_mod_cast hn
  · exact hω

end ProbabilityTheory
