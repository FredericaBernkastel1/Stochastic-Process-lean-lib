/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.IntervalAxiomsConverse
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Law identification for the converse Poisson interval characterization

This file completes the converse direction of Klenke, Theorem 5.34. Dyadic occupied-cell sums
approximate the total interval count in probability and in first moment. Their finite-dimensional
laws are Poisson-binomial; the triangular-array limit therefore identifies every interval count as
Poisson and packages the original interval axioms as an `IsPoissonProcess`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology BigOperators symmDiff

namespace ProbabilityTheory.SatisfiesPoissonIntervalAxioms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {X : NNReal → Ω → ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

lemma dyadic_card_nsmul_length (t : NNReal) (n : ℕ) :
    (2 ^ n) • dyadicIntervalLength t n = t := by
  ext
  simp [dyadicIntervalLength, nsmul_eq_mul]
  field_simp

lemma ae_sum_dyadicSubintervalCount_prefix
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n m : ℕ) :
    (fun ω ↦ ∑ i ∈ Finset.range m, dyadicSubintervalCount X t n i ω) =ᵐ[P]
      fun ω ↦ poissonIntervalCount X 0 (m • dyadicIntervalLength t n) ω := by
  induction m with
  | zero => simp [poissonIntervalCount]
  | succ m ih =>
      have hadd := hX.intervalAdditive 0 (m • dyadicIntervalLength t n)
        ((m + 1) • dyadicIntervalLength t n) bot_le
        (nsmul_le_nsmul_left (dyadicIntervalLength t n).2 (Nat.le_succ m))
      filter_upwards [ih, hadd] with ω hsum haddω
      rw [Finset.sum_range_succ, hsum, haddω]
      rfl

lemma ae_sum_dyadicSubintervalCount
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    (fun ω ↦ ∑ i : Fin (2 ^ n), dyadicSubintervalCount X t n i ω) =ᵐ[P]
      poissonIntervalCount X 0 t := by
  have h := hX.ae_sum_dyadicSubintervalCount_prefix t n (2 ^ n)
  filter_upwards [h] with ω hω
  rw [← Fin.sum_univ_eq_sum_range] at hω
  simpa only [dyadic_card_nsmul_length] using hω

def dyadicMultipleJumpEvent
    (X : NNReal → Ω → ℕ) (t : NNReal) (n : ℕ) : Set Ω :=
  ⋃ i : Fin (2 ^ n), {ω | 2 ≤ dyadicSubintervalCount X t n i ω}

lemma measureReal_dyadicMultipleJumpEvent_le
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    P.real (dyadicMultipleJumpEvent X t n) ≤
      ((2 : ℝ) ^ n) *
        P.real {ω | 2 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω} := by
  calc
    P.real (dyadicMultipleJumpEvent X t n) ≤
        ∑ i : Fin (2 ^ n),
          P.real {ω | 2 ≤ dyadicSubintervalCount X t n i ω} := by
      exact measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin (2 ^ n),
          P.real {ω | 2 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω} := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg ENNReal.toReal
        ((hX.identDistrib_dyadicSubintervalCount t n i).measure_mem_eq measurableSet_Ici) |>.symm
    _ = ((2 : ℝ) ^ n) *
        P.real {ω | 2 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω} := by
      simp

theorem tendsto_measureReal_dyadicMultipleJumpEvent
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto (fun n ↦ P.real (dyadicMultipleJumpEvent X t n)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ measureReal_nonneg
  · exact Eventually.of_forall fun n ↦ hX.measureReal_dyadicMultipleJumpEvent_le t n
  · simpa only [dyadicIntervalLength] using hX.tendsto_dyadic_multipleJump_error t

def dyadicOccupiedMismatchEvent
    (X : NNReal → Ω → ℕ) (t : NNReal) (n : ℕ) : Set Ω :=
  {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) ≠
    poissonIntervalCount X 0 t ω}

lemma ae_dyadicOccupiedSum_le
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    ∀ᵐ ω ∂P, (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) ≤
      poissonIntervalCount X 0 t ω := by
  filter_upwards [hX.ae_sum_dyadicSubintervalCount t n] with ω hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  simp only [dyadicSubintervalOccupied]
  split_ifs <;> omega

lemma ae_dyadicOccupiedMismatchEvent_subset
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    dyadicOccupiedMismatchEvent X t n ≤ᵐ[P] dyadicMultipleJumpEvent X t n := by
  filter_upwards [hX.ae_sum_dyadicSubintervalCount t n] with ω hsum
  intro hmismatch
  by_contra hbad
  have hcell : ∀ i : Fin (2 ^ n),
      dyadicSubintervalOccupied X t n i ω = dyadicSubintervalCount X t n i ω := by
    intro i
    have hi : ¬ 2 ≤ dyadicSubintervalCount X t n i ω := by
      intro hi
      apply hbad
      rw [dyadicMultipleJumpEvent]
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    simp only [dyadicSubintervalOccupied]
    split_ifs <;> omega
  apply hmismatch
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact hcell i

lemma measureReal_dyadicOccupiedMismatchEvent_le
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    P.real (dyadicOccupiedMismatchEvent X t n) ≤
      P.real (dyadicMultipleJumpEvent X t n) := by
  apply ENNReal.toReal_mono (by finiteness)
  exact measure_mono_ae (hX.ae_dyadicOccupiedMismatchEvent_subset t n)

theorem tendsto_measureReal_dyadicOccupiedMismatchEvent
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto (fun n ↦ P.real (dyadicOccupiedMismatchEvent X t n)) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ measureReal_nonneg
  · exact Eventually.of_forall fun n ↦ hX.measureReal_dyadicOccupiedMismatchEvent_le t n
  · exact hX.tendsto_measureReal_dyadicMultipleJumpEvent t

lemma integrable_natCast_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    Integrable (fun ω ↦ (dyadicSubintervalOccupied X t n i ω : ℝ)) P := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp_aemeasurable
      (hX.aemeasurable_dyadicSubintervalOccupied t n i)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [dyadicSubintervalOccupied]
    split_ifs <;> norm_num

lemma integral_natCast_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    (∫ ω, (dyadicSubintervalOccupied X t n i ω : ℝ) ∂P) =
      (dyadicOccupancyProbability X P t n : ℝ) := by
  have h := (hX.hasLaw_dyadicSubintervalOccupied t n i).integral_comp
    (f := fun k : ℕ ↦ (k : ℝ))
    (measurable_of_countable fun k : ℕ ↦ (k : ℝ)).aestronglyMeasurable
  change (∫ ω, (dyadicSubintervalOccupied X t n i ω : ℝ) ∂P) =
    ∫ k, (k : ℝ) ∂bernoulliMeasure (1 : ℕ) 0 (dyadicOccupancyProbability X P t n) at h
  rw [integral_bernoulliMeasure] at h
  simpa using h

lemma integral_natCast_dyadicOccupiedSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    (∫ ω, ((∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω : ℕ) : ℝ) ∂P) =
      ((2 : ℝ) ^ n) * (dyadicOccupancyProbability X P t n : ℝ) := by
  calc
    (∫ ω, ((∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω : ℕ) : ℝ) ∂P) =
        ∫ ω, ∑ i : Fin (2 ^ n), (dyadicSubintervalOccupied X t n i ω : ℝ) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω ↦ by simp
    _ = ∑ i : Fin (2 ^ n),
        ∫ ω, (dyadicSubintervalOccupied X t n i ω : ℝ) ∂P := by
      exact integral_finsetSum Finset.univ fun i _ ↦
        hX.integrable_natCast_dyadicSubintervalOccupied t n i
    _ = ∑ _i : Fin (2 ^ n), (dyadicOccupancyProbability X P t n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hX.integral_natCast_dyadicSubintervalOccupied t n i
    _ = ((2 : ℝ) ^ n) * (dyadicOccupancyProbability X P t n : ℝ) := by
      simp

lemma integrable_natCast_dyadicOccupiedSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    Integrable
      (fun ω ↦ ((∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω : ℕ) : ℝ)) P := by
  simpa only [Nat.cast_sum] using
    integrable_finsetSum (Finset.univ : Finset (Fin (2 ^ n))) fun i _ ↦
      hX.integrable_natCast_dyadicSubintervalOccupied t n i

lemma nullMeasurableSet_dyadicOccupiedMismatchEvent
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    NullMeasurableSet (dyadicOccupiedMismatchEvent X t n) P := by
  have hsum : AEMeasurable
      (fun ω ↦ ∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦
      hX.aemeasurable_dyadicSubintervalOccupied t n i
  have hcount : AEMeasurable (poissonIntervalCount X 0 t) P :=
    (hX.aemeasurable t).sub (hX.aemeasurable 0)
  simpa only [dyadicOccupiedMismatchEvent, ← Set.compl_ofPred] using
    (nullMeasurableSet_eq_fun hsum hcount).compl

theorem tendsto_integral_natCast_dyadicOccupiedSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto
      (fun n ↦ ∫ ω,
        ((∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω : ℕ) : ℝ) ∂P)
      atTop (𝓝 (hX.intervalMean t)) := by
  let N : Ω → ℝ := fun ω ↦ (poissonIntervalCount X 0 t ω : ℝ)
  let S : ℕ → Ω → ℝ := fun n ω ↦
    ((∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω : ℕ) : ℝ)
  let A : ℕ → Set Ω := fun n ↦ dyadicOccupiedMismatchEvent X t n
  change Tendsto (fun n ↦ ∫ ω, S n ω ∂P) atTop (𝓝 (hX.intervalMean t))
  have hN : Integrable N P := hX.finiteMean 0 t bot_le
  have hS : ∀ n, Integrable (S n) P := fun n ↦
    hX.integrable_natCast_dyadicOccupiedSum t n
  have hAreal := hX.tendsto_measureReal_dyadicOccupiedMismatchEvent t
  have hAmeasure : Tendsto (fun n ↦ P (A n)) atTop (𝓝 0) := by
    change Tendsto (fun n ↦ P.real (A n)) atTop (𝓝 0) at hAreal
    simpa only [measureReal_def,
      ENNReal.tendsto_toReal_zero_iff (fun n ↦ measure_ne_top P (A n))] using hAreal
  have hset : Tendsto (fun n ↦ ∫ ω in A n, N ω ∂P) atTop (𝓝 0) :=
    hN.tendsto_setIntegral_nhds_zero hAmeasure
  have hlower : Tendsto
      (fun n ↦ hX.intervalMean t - ∫ ω in A n, N ω ∂P)
      atTop (𝓝 (hX.intervalMean t)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hset
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    have hnull := hX.nullMeasurableSet_dyadicOccupiedMismatchEvent t n
    have hdiff : ∀ ω, N ω - S n ω ≤ (A n).indicator N ω := by
      intro ω
      by_cases hω : ω ∈ A n
      · rw [Set.indicator_of_mem hω]
        have hSnonneg : 0 ≤ S n ω := by
          dsimp only [S]
          positivity
        linarith
      · rw [Set.indicator_of_notMem hω]
        have heq : S n ω = N ω := by
          have heqNat :
              (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) =
                poissonIntervalCount X 0 t ω := by
            simpa only [A, dyadicOccupiedMismatchEvent, mem_ofPred_eq,
              not_not] using hω
          dsimp only [S, N]
          exact_mod_cast heqNat
        rw [heq, sub_self]
    have hdiffIntegral := integral_mono_ae (hN.sub (hS n)) (hN.indicator₀ hnull)
      (Eventually.of_forall hdiff)
    change (∫ x, N x - S n x ∂P) ≤
      ∫ x, (dyadicOccupiedMismatchEvent X t n).indicator N x ∂P at hdiffIntegral
    rw [integral_sub hN (hS n), integral_indicator₀ hnull] at hdiffIntegral
    change hX.intervalMean t - ∫ ω in A n, N ω ∂P ≤ ∫ ω, S n ω ∂P
    change (∫ ω, N ω ∂P) - ∫ ω in A n, N ω ∂P ≤ ∫ ω, S n ω ∂P
    linarith
  · intro n
    have hle : S n ≤ᵐ[P] N := by
      filter_upwards [hX.ae_dyadicOccupiedSum_le t n] with ω hω
      dsimp only [S, N]
      exact_mod_cast hω
    change (∫ ω, S n ω ∂P) ≤ hX.intervalMean t
    change (∫ ω, S n ω ∂P) ≤ ∫ ω, N ω ∂P
    exact integral_mono_ae (hS n) hN hle

@[simp]
lemma coe_dyadicOccupancyProbability
    (X : NNReal → Ω → ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (t : NNReal) (n : ℕ) :
    (dyadicOccupancyProbability X P t n : ℝ) =
      P.real {ω | 1 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω} := rfl

lemma measure_one_le_intervalMean
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    P.real {ω | 1 ≤ poissonIntervalCount X 0 t ω} ≤ hX.intervalMean t := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω ↦ (poissonIntervalCount X 0 t ω : ℝ))
    (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
    (hX.finiteMean 0 t bot_le) 1
  have hset : {ω | (1 : ℝ) ≤ (poissonIntervalCount X 0 t ω : ℝ)} =
      {ω | 1 ≤ poissonIntervalCount X 0 t ω} := by
    ext ω
    exact_mod_cast Iff.rfl
  rw [hset] at hm
  simpa only [one_mul, intervalMean] using hm

theorem tendsto_coe_dyadicOccupancyProbability
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto (fun n ↦ (dyadicOccupancyProbability X P t n : ℝ)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hlength : Tendsto (fun n ↦ (dyadicIntervalLength t n : ℝ)) atTop (𝓝 0) := by
    have h := hpow.const_mul (t : ℝ)
    convert h using 1 <;>
      simp [dyadicIntervalLength, div_eq_mul_inv]
  have hbound : ∀ n,
      (dyadicOccupancyProbability X P t n : ℝ) ≤
        (dyadicIntervalLength t n : ℝ) * hX.intervalMean 1 := by
    intro n
    rw [coe_dyadicOccupancyProbability, ← hX.intervalMean_linear]
    exact hX.measure_one_le_intervalMean (dyadicIntervalLength t n)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ (dyadicOccupancyProbability X P t n).property.1
  · exact Eventually.of_forall hbound
  · simpa only [zero_mul] using hlength.mul_const (hX.intervalMean 1)

theorem tendsto_dyadicOccupancyParameterSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto
      (fun n ↦ ((2 : ℝ) ^ n) * (dyadicOccupancyProbability X P t n : ℝ))
      atTop (𝓝 ((hX.intervalIntensity * t : NNReal) : ℝ)) := by
  have h := hX.tendsto_integral_natCast_dyadicOccupiedSum t
  have h' : Tendsto
      (fun n ↦ ((2 : ℝ) ^ n) * (dyadicOccupancyProbability X P t n : ℝ))
      atTop (𝓝 (hX.intervalMean t)) := by
    apply h.congr'
    exact Eventually.of_forall fun n ↦
      hX.integral_natCast_dyadicOccupiedSum t n
  have hmean : hX.intervalMean t = ((hX.intervalIntensity * t : NNReal) : ℝ) := by
    rw [hX.intervalMean_linear, NNReal.coe_mul, coe_intervalIntensity]
    ring
  rwa [← hmean]

lemma bernoulliRowSum_replicate (m : ℕ) (p : unitInterval) :
    bernoulliRowSum (List.replicate m p) = (m : ℝ) * (p : ℝ) := by
  induction m with
  | zero => simp [bernoulliRowSum]
  | succ m ih =>
      rw [List.replicate_succ]
      change (p : ℝ) + bernoulliRowSum (List.replicate m p) =
        ((m + 1 : ℕ) : ℝ) * (p : ℝ)
      rw [ih]
      push_cast
      ring

lemma bernoulliRowMax_replicate_succ (m : ℕ) (p : unitInterval) :
    bernoulliRowMax (List.replicate (m + 1) p) = (p : ℝ) := by
  induction m with
  | zero => simp [bernoulliRowMax, p.property.1]
  | succ m ih =>
      rw [List.replicate_succ, bernoulliRowMax]
      simp only [ih, max_self]

theorem tendsto_dyadicBernoulliRowSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto
      (fun n ↦ bernoulliRowSum
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n)))
      atTop (𝓝 ((hX.intervalIntensity * t : NNReal) : ℝ)) := by
  apply (hX.tendsto_dyadicOccupancyParameterSum t).congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [bernoulliRowSum_replicate]
    norm_num

theorem tendsto_dyadicBernoulliRowMax
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto
      (fun n ↦ bernoulliRowMax
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n)))
      atTop (𝓝 0) := by
  apply (hX.tendsto_coe_dyadicOccupancyProbability t).congr'
  exact Eventually.of_forall fun n ↦ by
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    dsimp only
    rw [show 2 ^ n = (2 ^ n - 1) + 1 by omega,
      bernoulliRowMax_replicate_succ]

theorem tendsto_dyadicPoissonBinomial_mass
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (k : ℕ) :
    Tendsto
      (fun n ↦ (PMF.poissonBinomial
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).massReal k)
      atTop (𝓝 ((PMF.poissonNat (hX.intervalIntensity * t)).massReal k)) :=
  poissonBinomial_tendsto_poissonNat_of_max
    (hX.tendsto_dyadicBernoulliRowSum t)
    (hX.tendsto_dyadicBernoulliRowMax t) k

lemma abs_measureReal_dyadicOccupied_eq_sub_intervalCount_eq_le
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n k : ℕ) :
    |P.real {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) = k} -
        P.real {ω | poissonIntervalCount X 0 t ω = k}| ≤
      P.real (dyadicOccupiedMismatchEvent X t n) := by
  let S : Ω → ℕ := fun ω ↦
    ∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω
  let N : Ω → ℕ := poissonIntervalCount X 0 t
  have hS : AEMeasurable S P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦
      hX.aemeasurable_dyadicSubintervalOccupied t n i
  have hN : AEMeasurable N P := (hX.aemeasurable t).sub (hX.aemeasurable 0)
  have hSk : NullMeasurableSet {ω | S ω = k} P :=
    nullMeasurableSet_eq_fun hS aemeasurable_const
  have hNk : NullMeasurableSet {ω | N ω = k} P :=
    nullMeasurableSet_eq_fun hN aemeasurable_const
  calc
    |P.real {ω | S ω = k} - P.real {ω | N ω = k}| ≤
        P.real ({ω | S ω = k} ∆ {ω | N ω = k}) :=
      abs_measureReal_sub_le_measureReal_symmDiff hSk hNk
    _ ≤ P.real (dyadicOccupiedMismatchEvent X t n) := by
      apply measureReal_mono (h₂ := by finiteness)
      intro ω hω
      simp only [mem_symmDiff, mem_ofPred_eq] at hω
      change S ω ≠ N ω
      rcases hω with ⟨hSkω, hNkω⟩ | ⟨hNkω, hSkω⟩
      · intro heq
        exact hNkω (heq ▸ hSkω)
      · intro heq
        exact hSkω (heq.symm ▸ hNkω)

theorem tendsto_measureReal_dyadicOccupied_eq
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (k : ℕ) :
    Tendsto
      (fun n ↦ P.real
        {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) = k})
      atTop (𝓝 (P.real {ω | poissonIntervalCount X 0 t ω = k})) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun n ↦ abs_nonneg _)
    (Eventually.of_forall fun n ↦
      hX.abs_measureReal_dyadicOccupied_eq_sub_intervalCount_eq_le t n k)
    (hX.tendsto_measureReal_dyadicOccupiedMismatchEvent t)

lemma measureReal_dyadicOccupied_eq
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n k : ℕ) :
    P.real {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) = k} =
      (PMF.poissonBinomial
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).massReal k := by
  have h := (hX.hasLaw_dyadicOccupiedSum t n).measureReal_eq
    (p := fun j : ℕ ↦ j = k) (MeasurableSet.singleton k)
  have hset : {j : ℕ | j = k} = {k} := by ext j; simp
  rw [hset] at h
  calc
    P.real {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) = k} =
        (PMF.poissonBinomial
          (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).toMeasure.real {k} := h
    _ = (PMF.poissonBinomial
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).massReal k := by
      rw [measureReal_def,
        PMF.toMeasure_apply_singleton _ k (MeasurableSet.singleton k)]
      rfl

theorem measureReal_intervalCount_eq_poissonNat_massReal
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (k : ℕ) :
    P.real {ω | poissonIntervalCount X 0 t ω = k} =
      (PMF.poissonNat (hX.intervalIntensity * t)).massReal k := by
  have hToCount := hX.tendsto_measureReal_dyadicOccupied_eq t k
  have hToPoisson := hX.tendsto_dyadicPoissonBinomial_mass t k
  have heq : (fun n ↦ P.real
      {ω | (∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω) = k}) =
      fun n ↦ (PMF.poissonBinomial
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).massReal k := by
    funext n
    exact hX.measureReal_dyadicOccupied_eq t n k
  rw [heq] at hToCount
  exact tendsto_nhds_unique hToCount hToPoisson

/-- The interval count on `(0, t]` has the Poisson law selected by the interval mean. -/
theorem hasLaw_intervalCount_zero
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    HasLaw (poissonIntervalCount X 0 t)
      (poissonMeasure (hX.intervalIntensity * t)) P := by
  have hmeas : AEMeasurable (poissonIntervalCount X 0 t) P :=
    (hX.aemeasurable t).sub (hX.aemeasurable 0)
  refine ⟨hmeas, ?_⟩
  apply MeasureTheory.Measure.ext_of_measureReal_singleton
  intro k
  rw [map_measureReal_apply_of_aemeasurable hmeas (MeasurableSet.singleton k)]
  change P.real {ω | poissonIntervalCount X 0 t ω = k} =
    (poissonMeasure (hX.intervalIntensity * t)).real {k}
  rw [hX.measureReal_intervalCount_eq_poissonNat_massReal t k,
    PMF.massReal_poissonNat, poissonMeasure_real_singleton]

/-- Every ordered interval count has its stationary Poisson law. -/
theorem hasLaw_intervalCount
    (hX : SatisfiesPoissonIntervalAxioms X P) (s t : NNReal) (hst : s ≤ t) :
    HasLaw (poissonIntervalCount X s t)
      (poissonMeasure (hX.intervalIntensity * (t - s))) P := by
  have hident := hX.stationaryIntervalLaw 0 (t - s) s t bot_le hst (by simp)
  exact IdentDistrib.hasLaw hident (hX.hasLaw_intervalCount_zero (t - s))

/-- Converse direction of Klenke's interval characterization: P1--P5, with the fixed common-event
path semantics, determine a Poisson process whose rate is the unit-interval mean. -/
theorem isPoissonProcess
    (hX : SatisfiesPoissonIntervalAxioms X P) :
    IsPoissonProcess X hX.intervalIntensity P := by
  refine
    { aemeasurable := hX.aemeasurable
      initial := hX.initial
      monotonePaths := hX.monotonePaths
      rightContinuousPaths := hX.rightContinuousPaths
      indepIncrements := hX.indepIncrements
      incrementLaw := ?_ }
  intro s t hst
  change HasLaw (poissonIntervalCount X s t)
    (poissonMeasure (hX.intervalIntensity * (t - s))) P
  exact hX.hasLaw_intervalCount s t hst

end ProbabilityTheory.SatisfiesPoissonIntervalAxioms
