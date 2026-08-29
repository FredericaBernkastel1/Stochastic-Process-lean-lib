/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Moments of independent random sums

This file develops the moment identities behind Wald's and Blackwell--Girshick's formulas.  The
count is independent of each summand; it is not treated as a stopping time.
-/

@[expose] public section

open Finset MeasureTheory

namespace ProbabilityTheory

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Sum of the first `T(ω)` members of a random sequence. -/
def stoppedSum (T : Ω → ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range (T ω), X i ω

/-- The real indicator of the event that the random count exceeds `i`. -/
def countIndicator (T : Ω → ℕ) (i : ℕ) (ω : Ω) : ℝ :=
  if i < T ω then 1 else 0

private theorem stoppedSum_eq_sum_countIndicator {T : Ω → ℕ} {X : ℕ → Ω → ℝ}
    {N : ℕ} {ω : Ω} (hT : T ω ≤ N) :
    stoppedSum T X ω = ∑ i ∈ range N, countIndicator T i ω * X i ω := by
  rw [stoppedSum]
  calc
    ∑ i ∈ range (T ω), X i ω =
        ∑ i ∈ (range N).filter (fun i ↦ i < T ω), X i ω := by
      congr 1
      ext i
      simp only [mem_range, mem_filter]
      omega
    _ = ∑ i ∈ range N, countIndicator T i ω * X i ω := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      by_cases hit : i < T ω <;> simp [countIndicator, hit]

private theorem stoppedSum_eq_tsum_countIndicator {T : Ω → ℕ} {X : ℕ → Ω → ℝ}
    (ω : Ω) :
    stoppedSum T X ω = ∑' i : ℕ, countIndicator T i ω * X i ω := by
  rw [tsum_eq_sum (s := range (T ω))]
  · apply sum_congr rfl
    intro i hi
    simp [countIndicator, mem_range.mp hi]
  · intro i hi
    simp only [mem_range, not_lt] at hi
    simp [countIndicator, hi]

private theorem sq_sum_range_eq (a : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, a i) ^ 2 =
      ∑ i ∈ range N, (a i) ^ 2 +
        2 * ∑ j ∈ range N, ∑ i ∈ range j, a i * a j := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [sum_range_succ]
      rw [← sum_mul]
      nlinarith [ih]

private theorem sq_stoppedSum_le_count_mul_stoppedSum_sq
    {T U : Ω → ℕ} {Y : ℕ → Ω → ℝ} {ω : Ω} (hUT : U ω ≤ T ω) :
    (stoppedSum U Y ω) ^ 2 ≤
      (T ω : ℝ) * stoppedSum T (fun i ω ↦ (Y i ω) ^ 2) ω := by
  rw [stoppedSum, stoppedSum]
  calc
    (∑ i ∈ range (U ω), Y i ω) ^ 2 ≤
        (U ω : ℝ) * ∑ i ∈ range (U ω), (Y i ω) ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := range (U ω)) (f := fun i ↦ Y i ω)
    _ ≤ (T ω : ℝ) * ∑ i ∈ range (T ω), (Y i ω) ^ 2 := by
      gcongr

private theorem tsum_measure_count_lt_eq_lintegral
    {T : Ω → ℕ} (hTmeas : Measurable T) :
    (∑' i : ℕ, P {ω | i < T ω}) = ∫⁻ ω, (T ω : ENNReal) ∂P := by
  have hset : ∀ i, MeasurableSet {ω | i < T ω} := fun i ↦
    measurableSet_lt measurable_const hTmeas
  calc
    (∑' i : ℕ, P {ω | i < T ω}) =
        ∫⁻ ω, ∑' i : ℕ, {ω | i < T ω}.indicator (fun _ ↦ (1 : ENNReal)) ω ∂P := by
          rw [lintegral_tsum]
          · congr 1
            funext i
            exact (lintegral_indicator_one (hset i)).symm
          · intro i
            exact aemeasurable_const.indicator (hset i)
    _ = ∫⁻ ω, (T ω : ENNReal) ∂P := by
      apply lintegral_congr
      intro ω
      rw [tsum_eq_sum (s := range (T ω))]
      · calc
          ∑ i ∈ range (T ω), {ω | i < T ω}.indicator
              (fun _ ↦ (1 : ENNReal)) ω =
              ∑ _i ∈ range (T ω), (1 : ENNReal) := by
                apply sum_congr rfl
                intro i hi
                simp [mem_range.mp hi]
          _ = (T ω : ENNReal) := by simp
      · intro i hi
        simp only [mem_range, not_lt] at hi
        simp [hi]
private theorem tsum_measure_count_lt_ne_top [IsProbabilityMeasure P]
    {T : Ω → ℕ} (hTmeas : Measurable T)
    (hTint : Integrable (fun ω ↦ (T ω : ℝ)) P) :
    (∑' i : ℕ, P {ω | i < T ω}) ≠ ⊤ := by
  rw [tsum_measure_count_lt_eq_lintegral hTmeas]
  apply ne_of_lt
  have hfin := hTint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  simpa using hfin

private theorem tsum_measureReal_count_lt_eq_integral [IsProbabilityMeasure P]
    {T : Ω → ℕ} (hTmeas : Measurable T)
    (hTint : Integrable (fun ω ↦ (T ω : ℝ)) P) :
    (∑' i : ℕ, P.real {ω | i < T ω}) = ∫ ω, (T ω : ℝ) ∂P := by
  calc
    (∑' i : ℕ, P.real {ω | i < T ω}) =
        (∑' i : ℕ, P {ω | i < T ω}).toReal := by
          exact (ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top P _)).symm
    _ = (∫⁻ ω, (T ω : ENNReal) ∂P).toReal := by
      rw [tsum_measure_count_lt_eq_lintegral hTmeas]
    _ = ∫ ω, (T ω : ℝ) ∂P := by
      symm
      simpa using integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω ↦ Nat.cast_nonneg (T ω))
        hTint.aestronglyMeasurable

private theorem summable_integral_count_mul_countIndicator [IsProbabilityMeasure P]
    {T : Ω → ℕ} (hTmeas : Measurable T)
    (hT2 : MemLp (fun ω ↦ (T ω : ℝ)) 2 P) :
    Summable fun i : ℕ ↦ ∫ ω, (T ω : ℝ) * countIndicator T i ω ∂P := by
  let G : ℕ → Ω → ℝ := fun i ω ↦ (T ω : ℝ) * countIndicator T i ω
  have hset : ∀ i, MeasurableSet {ω | i < T ω} := fun i ↦
    measurableSet_lt measurable_const hTmeas
  have hTint : Integrable (fun ω ↦ (T ω : ℝ)) P := hT2.integrable (by norm_num)
  have hGint : ∀ i, Integrable (G i) P := fun i ↦ by
    have heq : G i = {ω | i < T ω}.indicator (fun ω ↦ (T ω : ℝ)) := by
      funext ω
      by_cases hi : i < T ω <;> simp [G, countIndicator, hi]
    rw [heq]
    exact hTint.indicator (hset i)
  have hGnonneg : ∀ i ω, 0 ≤ G i ω := fun i ω ↦ by
    by_cases hi : i < T ω <;> simp [G, countIndicator, hi]
  have hGpoint : ∀ ω, ∑' i, G i ω = (T ω : ℝ) ^ 2 := fun ω ↦ by
    rw [tsum_eq_sum (s := range (T ω))]
    · calc
        ∑ i ∈ range (T ω), G i ω = ∑ _i ∈ range (T ω), (T ω : ℝ) := by
          apply sum_congr rfl
          intro i hi
          simp [G, countIndicator, mem_range.mp hi]
        _ = (T ω : ℝ) ^ 2 := by simp [pow_two]
    · intro i hi
      simp only [mem_range, not_lt] at hi
      simp [G, countIndicator, hi]
  have hsqInt : Integrable (fun ω ↦ (T ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hT2.aestronglyMeasurable).mp hT2
  have htsum_ne_top : (∑' i, ∫⁻ ω, ENNReal.ofReal (G i ω) ∂P) ≠ ⊤ := by
    rw [← lintegral_tsum (fun i ↦ (hGint i).aemeasurable.ennreal_ofReal)]
    have hpoint : ∀ ω, ∑' i, ENNReal.ofReal (G i ω) =
        ENNReal.ofReal ((T ω : ℝ) ^ 2) := fun ω ↦ by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ hGnonneg i ω)]
      · rw [hGpoint]
      · apply summable_of_ne_finset_zero (s := range (T ω))
        intro i hi
        simp only [mem_range, not_lt] at hi
        simp [G, countIndicator, hi]
    rw [lintegral_congr hpoint]
    apply ne_of_lt
    have hfin := hsqInt.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    simpa [Real.enorm_eq_ofReal (sq_nonneg _)] using hfin
  apply (ENNReal.summable_toReal htsum_ne_top).congr
  intro i
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω ↦ hGnonneg i ω) (hGint i).aestronglyMeasurable).symm

private theorem integrable_tsum_norm_of_summable_integral_norm
    (F : ℕ → Ω → ℝ) (hFint : ∀ i, Integrable (F i) P)
    (hpointSum : ∀ ω, Summable fun i ↦ ‖F i ω‖)
    (hsum : Summable fun i ↦ ∫ ω, ‖F i ω‖ ∂P) :
    Integrable (fun ω ↦ ∑' i, ‖F i ω‖) P := by
  constructor
  · exact AEStronglyMeasurable.tsum (fun i ↦ (hFint i).norm.aestronglyMeasurable)
  · rw [hasFiniteIntegral_iff_enorm]
    have hnonneg : ∀ ω, 0 ≤ ∑' i, ‖F i ω‖ := fun ω ↦ tsum_nonneg fun _ ↦ norm_nonneg _
    simp_rw [Real.enorm_eq_ofReal (hnonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun i ↦ norm_nonneg _) (hpointSum _)]
    rw [lintegral_tsum]
    · calc
        (∑' i, ∫⁻ ω, ENNReal.ofReal ‖F i ω‖ ∂P) =
            ∑' i, ENNReal.ofReal (∫ ω, ‖F i ω‖ ∂P) := by
              congr 1
              funext i
              simpa only [ofReal_norm, enorm_eq_nnnorm, coe_nnnorm] using
                lintegral_coe_eq_integral (fun ω ↦ ‖F i ω‖₊) (hFint i).norm
        _ = ENNReal.ofReal (∑' i, ∫ ω, ‖F i ω‖ ∂P) := by
          rw [ENNReal.ofReal_tsum_of_nonneg
            (fun i ↦ integral_nonneg fun _ ↦ norm_nonneg _) hsum]
        _ < ⊤ := ENNReal.ofReal_lt_top
    · intro i
      exact (hFint i).norm.aemeasurable.ennreal_ofReal

private theorem integral_sq_stoppedSum_eq_mul_of_bounded_centered [IsProbabilityMeasure P]
    {U : Ω → ℕ} {Y : ℕ → Ω → ℝ} (hUmeas : Measurable U)
    (hY2 : ∀ i, MemLp (Y i) 2 P)
    (hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hYcenter : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hYindep : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P)
    (hUindepSq : ∀ i, IndepFun U (fun ω ↦ (Y i ω) ^ 2) P)
    (hUindepMul : ∀ i j, IndepFun U (fun ω ↦ Y i ω * Y j ω) P)
    {N : ℕ} (hUbound : ∀ᵐ ω ∂P, U ω ≤ N) :
    ∫ ω, (stoppedSum U Y ω) ^ 2 ∂P =
      (∫ ω, (U ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P := by
  have hset : ∀ i, MeasurableSet {ω | i < U ω} := fun i ↦
    measurableSet_lt measurable_const hUmeas
  have hcind : ∀ i, AEStronglyMeasurable (countIndicator U i) P := fun i ↦ by
    have hm : Measurable (countIndicator U i) := by
      unfold countIndicator
      exact measurable_const.ite (hset i) measurable_const
    exact hm.aestronglyMeasurable
  have hcountIntegral : ∀ i, (∫ ω, countIndicator U i ω ∂P) =
      P.real {ω | i < U ω} := fun i ↦ by
    have hindicator : countIndicator U i = {ω | i < U ω}.indicator 1 := by
      funext ω
      by_cases hit : i < U ω <;> simp [countIndicator, hit]
    rw [hindicator]
    simpa using integral_indicator_one (μ := P) (hset i)
  have hYint : ∀ i, Integrable (Y i) P := fun i ↦ (hY2 i).integrable (by norm_num)
  have hYsqInt : ∀ i, Integrable (fun ω ↦ (Y i ω) ^ 2) P := fun i ↦
    (memLp_two_iff_integrable_sq (hY2 i).aestronglyMeasurable).mp (hY2 i)
  have hYmulInt : ∀ i j, i ≠ j → Integrable (fun ω ↦ Y i ω * Y j ω) P :=
    fun i j hij ↦ (hYindep hij).integrable_mul (hYint i) (hYint j)
  have hdiagInt : ∀ i, Integrable
      (fun ω ↦ countIndicator U i ω * (Y i ω) ^ 2) P := fun i ↦ by
    have heq : (fun ω ↦ countIndicator U i ω * (Y i ω) ^ 2) =
        {ω | i < U ω}.indicator (fun ω ↦ (Y i ω) ^ 2) := by
      funext ω
      by_cases hi : i < U ω <;> simp [countIndicator, hi]
    rw [heq]
    exact (hYsqInt i).indicator (hset i)
  have hcrossInt : ∀ j, ∀ i ∈ range j, Integrable
      (fun ω ↦ countIndicator U j ω * (Y i ω * Y j ω)) P := fun j i hi ↦ by
    have hij : i ≠ j := ne_of_lt (mem_range.mp hi)
    have heq : (fun ω ↦ countIndicator U j ω * (Y i ω * Y j ω)) =
        {ω | j < U ω}.indicator (fun ω ↦ Y i ω * Y j ω) := by
      funext ω
      by_cases hj : j < U ω <;> simp [countIndicator, hj]
    rw [heq]
    exact (hYmulInt i j hij).indicator (hset j)
  have hdecomp : ∀ᵐ ω ∂P, (stoppedSum U Y ω) ^ 2 =
      ∑ i ∈ range N, countIndicator U i ω * (Y i ω) ^ 2 +
        2 * ∑ j ∈ range N, ∑ i ∈ range j,
          countIndicator U j ω * (Y i ω * Y j ω) := by
    filter_upwards [hUbound] with ω hω
    rw [stoppedSum_eq_sum_countIndicator hω,
      sq_sum_range_eq (fun i ↦ countIndicator U i ω * Y i ω) N]
    congr 1
    · apply sum_congr rfl
      intro i hi
      by_cases hit : i < U ω <;> simp [countIndicator, hit]
    · congr 1
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro i hi
      by_cases hjt : j < U ω
      · have hit : i < U ω := (mem_range.mp hi).trans hjt
        simp [countIndicator, hit, hjt]
      · simp [countIndicator, hjt]
  have hdiagFactor : ∀ i, (∫ ω, countIndicator U i ω * (Y i ω) ^ 2 ∂P) =
      P.real {ω | i < U ω} * ∫ ω, (Y 0 ω) ^ 2 ∂P := by
    intro i
    have hiIndep : IndepFun (countIndicator U i) (fun ω ↦ (Y i ω) ^ 2) P := by
      change IndepFun (fun ω ↦ if i < U ω then (1 : ℝ) else 0)
        (fun ω ↦ (Y i ω) ^ 2) P
      simpa only [Function.comp_def, id_eq] using
        (hUindepSq i).comp
          (measurable_of_countable fun n : ℕ ↦ if i < n then (1 : ℝ) else 0) measurable_id
    have hi := hiIndep.integral_fun_mul_eq_mul_integral
      (hcind i) (hYsqInt i).aestronglyMeasurable
    have hsqIdent : IdentDistrib (fun ω ↦ (Y i ω) ^ 2) (fun ω ↦ (Y 0 ω) ^ 2) P P := by
      simpa only [Function.comp_def, id_eq] using (hYident i).comp (measurable_id.pow_const 2)
    rw [hi, hcountIntegral i, hsqIdent.integral_eq]
  have hcrossZero : ∀ j, ∀ i ∈ range j,
      (∫ ω, countIndicator U j ω * (Y i ω * Y j ω) ∂P) = 0 := by
    intro j i hi
    have hij : i ≠ j := ne_of_lt (mem_range.mp hi)
    have hprodMean : (∫ ω, Y i ω * Y j ω ∂P) = 0 := by
      rw [(hYindep hij).integral_fun_mul_eq_mul_integral
        (hY2 i).aestronglyMeasurable (hY2 j).aestronglyMeasurable, hYcenter i, hYcenter j,
        zero_mul]
    have hiIndep : IndepFun (countIndicator U j) (fun ω ↦ Y i ω * Y j ω) P := by
      change IndepFun (fun ω ↦ if j < U ω then (1 : ℝ) else 0)
        (fun ω ↦ Y i ω * Y j ω) P
      simpa only [Function.comp_def, id_eq] using
        (hUindepMul i j).comp
          (measurable_of_countable fun n : ℕ ↦ if j < n then (1 : ℝ) else 0) measurable_id
    rw [hiIndep.integral_fun_mul_eq_mul_integral (hcind j)
      (hYmulInt i j hij).aestronglyMeasurable, hprodMean, mul_zero]
  rw [integral_congr_ae hdecomp]
  rw [integral_add]
  · rw [integral_finsetSum _ (fun i _ ↦ hdiagInt i), integral_const_mul]
    have hcrossIntegral : (∫ ω, ∑ j ∈ range N, ∑ i ∈ range j,
        countIndicator U j ω * (Y i ω * Y j ω) ∂P) = 0 := by
      rw [integral_finsetSum _ (fun j _ ↦
        integrable_finsetSum _ fun i hi ↦ hcrossInt j i hi)]
      apply sum_eq_zero
      intro j hj
      rw [integral_finsetSum _ (fun i hi ↦ hcrossInt j i hi)]
      exact sum_eq_zero fun i hi ↦ hcrossZero j i hi
    rw [hcrossIntegral, mul_zero, add_zero]
    simp_rw [hdiagFactor, ← sum_mul]
    congr 1
    calc
      ∑ i ∈ range N, P.real {ω | i < U ω} =
          ∑ i ∈ range N, ∫ ω, countIndicator U i ω ∂P := by
            apply sum_congr rfl
            intro i hi
            exact (hcountIntegral i).symm
      _ = ∫ ω, ∑ i ∈ range N, countIndicator U i ω ∂P := by
        rw [integral_finsetSum _]
        intro i hi
        have hindicator : countIndicator U i = {ω | i < U ω}.indicator 1 := by
          funext ω
          by_cases hit : i < U ω <;> simp [countIndicator, hit]
        rw [hindicator]
        exact (integrable_const 1).indicator (hset i)
      _ = ∫ ω, (U ω : ℝ) ∂P := by
        apply integral_congr_ae
        filter_upwards [hUbound] with ω hω
        have hreprOne := stoppedSum_eq_sum_countIndicator
          (T := U) (X := fun _ _ ↦ 1) hω
        simpa only [stoppedSum, mul_one, sum_const, card_range, nsmul_eq_mul, mul_one]
          using hreprOne.symm
  · exact integrable_finsetSum _ fun i hi ↦ hdiagInt i
  · exact (integrable_finsetSum _ fun j hj ↦
      integrable_finsetSum _ fun i hi ↦ hcrossInt j i hi).const_mul 2

private theorem integrable_count_mul_stoppedSum_sq [IsProbabilityMeasure P]
    {T : Ω → ℕ} {Y : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hT2 : MemLp (fun ω ↦ (T ω : ℝ)) 2 P)
    (hY2 : ∀ i, MemLp (Y i) 2 P)
    (hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hTindepSq : ∀ i, IndepFun T (fun ω ↦ (Y i ω) ^ 2) P) :
    Integrable (fun ω ↦ (T ω : ℝ) * stoppedSum T (fun i ω ↦ (Y i ω) ^ 2) ω) P := by
  let G : ℕ → Ω → ℝ := fun i ω ↦ (T ω : ℝ) * countIndicator T i ω
  let F : ℕ → Ω → ℝ := fun i ω ↦ G i ω * (Y i ω) ^ 2
  have hset : ∀ i, MeasurableSet {ω | i < T ω} := fun i ↦
    measurableSet_lt measurable_const hTmeas
  have hTint : Integrable (fun ω ↦ (T ω : ℝ)) P := hT2.integrable (by norm_num)
  have hGint : ∀ i, Integrable (G i) P := fun i ↦ by
    have heq : G i = {ω | i < T ω}.indicator (fun ω ↦ (T ω : ℝ)) := by
      funext ω
      by_cases hi : i < T ω <;> simp [G, countIndicator, hi]
    rw [heq]
    exact hTint.indicator (hset i)
  have hYsqInt : ∀ i, Integrable (fun ω ↦ (Y i ω) ^ 2) P := fun i ↦
    (memLp_two_iff_integrable_sq (hY2 i).aestronglyMeasurable).mp (hY2 i)
  have hGindepSq : ∀ i, IndepFun (G i) (fun ω ↦ (Y i ω) ^ 2) P := fun i ↦ by
    change IndepFun (fun ω ↦ (T ω : ℝ) * countIndicator T i ω)
      (fun ω ↦ (Y i ω) ^ 2) P
    change IndepFun (fun ω ↦ (T ω : ℝ) * if i < T ω then 1 else 0)
      (fun ω ↦ (Y i ω) ^ 2) P
    simpa only [Function.comp_def, id_eq] using
      (hTindepSq i).comp
        (measurable_of_countable fun n : ℕ ↦ (n : ℝ) * if i < n then 1 else 0) measurable_id
  have hFint : ∀ i, Integrable (F i) P := fun i ↦ by
    change Integrable (fun ω ↦ G i ω * (Y i ω) ^ 2) P
    exact (hGindepSq i).integrable_mul (hGint i) (hYsqInt i)
  have hfactor : ∀ i, (∫ ω, ‖F i ω‖ ∂P) =
      (∫ ω, G i ω ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P := by
    intro i
    have hnonneg : ∀ ω, 0 ≤ F i ω := fun ω ↦ by
      by_cases hi : i < T ω
      · simp only [F, G, countIndicator, hi, if_true]
        positivity
      · simp [F, G, countIndicator, hi]
    have hi := (hGindepSq i).integral_fun_mul_eq_mul_integral
      (hGint i).aestronglyMeasurable (hYsqInt i).aestronglyMeasurable
    have hsqIdent : IdentDistrib (fun ω ↦ (Y i ω) ^ 2) (fun ω ↦ (Y 0 ω) ^ 2) P P := by
      simpa only [Function.comp_def, id_eq] using (hYident i).comp (measurable_id.pow_const 2)
    have hnorm : (fun ω ↦ ‖F i ω‖) = F i := by
      funext ω
      exact Real.norm_of_nonneg (hnonneg ω)
    rw [hnorm]
    change (∫ ω, G i ω * (Y i ω) ^ 2 ∂P) =
      (∫ ω, G i ω ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P
    rw [hi, hsqIdent.integral_eq]
  have hsumNorm : Summable fun i ↦ ∫ ω, ‖F i ω‖ ∂P := by
    apply ((summable_integral_count_mul_countIndicator hTmeas hT2).mul_right
      (∫ ω, (Y 0 ω) ^ 2 ∂P)).congr
    intro i
    exact (hfactor i).symm
  have hpointSum : ∀ ω, Summable fun i ↦ ‖F i ω‖ := fun ω ↦ by
    apply summable_of_ne_finset_zero (s := range (T ω))
    intro i hi
    simp only [mem_range, not_lt] at hi
    simp [F, G, countIndicator, hi]
  have hsumInt := integrable_tsum_norm_of_summable_integral_norm F hFint hpointSum hsumNorm
  apply hsumInt.congr
  filter_upwards with ω
  rw [stoppedSum_eq_tsum_countIndicator (T := T)
    (X := fun i ω ↦ (Y i ω) ^ 2) ω, ← tsum_mul_left]
  apply tsum_congr
  intro i
  have hfi : 0 ≤ F i ω := by
    by_cases hi : i < T ω
    · simp only [F, G, countIndicator, hi, if_true]
      positivity
    · simp [F, G, countIndicator, hi]
  rw [Real.norm_of_nonneg hfi]
  simp only [F, G]
  ring

private theorem integral_sq_stoppedSum_eq_mul_centered [IsProbabilityMeasure P]
    {T : Ω → ℕ} {Y : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hT2 : MemLp (fun ω ↦ (T ω : ℝ)) 2 P)
    (hY2 : ∀ i, MemLp (Y i) 2 P)
    (hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hYcenter : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hYindep : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P)
    (hTindepSq : ∀ i, IndepFun T (fun ω ↦ (Y i ω) ^ 2) P)
    (hTindepMul : ∀ i j, IndepFun T (fun ω ↦ Y i ω * Y j ω) P) :
    ∫ ω, (stoppedSum T Y ω) ^ 2 ∂P =
      (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P := by
  let U : ℕ → Ω → ℕ := fun N ω ↦ min (T ω) N
  have hUmeas : ∀ N, Measurable (U N) := fun N ↦ hTmeas.min measurable_const
  have hUbound : ∀ N, ∀ ω, U N ω ≤ N := fun N ω ↦ min_le_right _ _
  have hUle : ∀ N ω, U N ω ≤ T ω := fun N ω ↦ min_le_left _ _
  have hUindepSq : ∀ N i, IndepFun (U N) (fun ω ↦ (Y i ω) ^ 2) P := fun N i ↦ by
    change IndepFun (fun ω ↦ min (T ω) N) (fun ω ↦ (Y i ω) ^ 2) P
    simpa only [Function.comp_def, id_eq] using
      (hTindepSq i).comp (measurable_of_countable fun n : ℕ ↦ min n N) measurable_id
  have hUindepMul : ∀ N i j, IndepFun (U N) (fun ω ↦ Y i ω * Y j ω) P :=
    fun N i j ↦ by
      change IndepFun (fun ω ↦ min (T ω) N) (fun ω ↦ Y i ω * Y j ω) P
      simpa only [Function.comp_def, id_eq] using
        (hTindepMul i j).comp (measurable_of_countable fun n : ℕ ↦ min n N) measurable_id
  have hfinite : ∀ N, (∫ ω, (stoppedSum (U N) Y ω) ^ 2 ∂P) =
      (∫ ω, (U N ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P := fun N ↦
    integral_sq_stoppedSum_eq_mul_of_bounded_centered (hUmeas N) hY2 hYident hYcenter
      hYindep (hUindepSq N) (hUindepMul N)
      (Filter.Eventually.of_forall (hUbound N))
  have hYmeas : ∀ i, AEStronglyMeasurable (Y i) P := fun i ↦ (hY2 i).aestronglyMeasurable
  have hstopMeas : ∀ N, AEStronglyMeasurable (stoppedSum (U N) Y) P := fun N ↦ by
    have hcind : ∀ i, AEStronglyMeasurable (countIndicator (U N) i) P := fun i ↦ by
      have hset : MeasurableSet {ω | i < U N ω} :=
        measurableSet_lt measurable_const (hUmeas N)
      have hm : Measurable (countIndicator (U N) i) := by
        unfold countIndicator
        exact measurable_const.ite hset measurable_const
      exact hm.aestronglyMeasurable
    have hsumMeas : AEStronglyMeasurable
        (fun ω ↦ ∑ i ∈ range N, countIndicator (U N) i ω * Y i ω) P :=
      by
        have h := Finset.aestronglyMeasurable_sum (range N)
          (fun i _ ↦ (hcind i).mul (hYmeas i))
        apply h.congr
        filter_upwards with ω
        simp only [Finset.sum_apply, Pi.mul_apply]
    apply hsumMeas.congr
    filter_upwards with ω
    exact (stoppedSum_eq_sum_countIndicator (hUbound N ω)).symm
  have henvelope := integrable_count_mul_stoppedSum_sq hTmeas hT2 hY2 hYident hTindepSq
  have hleft : Filter.Tendsto
      (fun N ↦ ∫ ω, (stoppedSum (U N) Y ω) ^ 2 ∂P) Filter.atTop
      (nhds (∫ ω, (stoppedSum T Y ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω ↦ (T ω : ℝ) * stoppedSum T (fun i ω ↦ (Y i ω) ^ 2) ω)
    · intro N
      exact (hstopMeas N).pow 2
    · exact henvelope
    · intro N
      filter_upwards with ω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_stoppedSum_le_count_mul_stoppedSum_sq (hUle N ω)
    · filter_upwards with ω
      apply tendsto_atTop_of_eventually_const (i₀ := T ω)
      intro N hN
      rw [stoppedSum, stoppedSum, show U N ω = T ω by simp [U, hN]]
  have hTint : Integrable (fun ω ↦ (T ω : ℝ)) P := hT2.integrable (by norm_num)
  have hrightCore : Filter.Tendsto (fun N ↦ ∫ ω, (U N ω : ℝ) ∂P) Filter.atTop
      (nhds (∫ ω, (T ω : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω ↦ (T ω : ℝ))
    · intro N
      exact ((measurable_of_countable fun n : ℕ ↦ (n : ℝ)).comp (hUmeas N)).aestronglyMeasurable
    · exact hTint
    · intro N
      filter_upwards with ω
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hUle N ω
    · filter_upwards with ω
      apply tendsto_atTop_of_eventually_const (i₀ := T ω)
      intro N hN
      simp [U, hN]
  have hright := hrightCore.mul_const (∫ ω, (Y 0 ω) ^ 2 ∂P)
  rw [show (fun N ↦ ∫ ω, (stoppedSum (U N) Y ω) ^ 2 ∂P) =
      (fun N ↦ (∫ ω, (U N ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P) from
    funext hfinite] at hleft
  exact tendsto_nhds_unique hleft hright

private theorem integral_stoppedSum_mul_count_eq_zero_centered [IsProbabilityMeasure P]
    {T : Ω → ℕ} {Y : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hT2 : MemLp (fun ω ↦ (T ω : ℝ)) 2 P)
    (hY2 : ∀ i, MemLp (Y i) 2 P)
    (hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (hYcenter : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hTindep : ∀ i, IndepFun T (Y i) P)
    (hTindepSq : ∀ i, IndepFun T (fun ω ↦ (Y i ω) ^ 2) P) :
    ∫ ω, stoppedSum T Y ω * (T ω : ℝ) ∂P = 0 := by
  let U : ℕ → Ω → ℕ := fun N ω ↦ min (T ω) N
  let G : ℕ → ℕ → Ω → ℝ := fun N i ω ↦
    (T ω : ℝ) * countIndicator (U N) i ω
  have hUmeas : ∀ N, Measurable (U N) := fun N ↦ hTmeas.min measurable_const
  have hUbound : ∀ N ω, U N ω ≤ N := fun N ω ↦ min_le_right _ _
  have hUle : ∀ N ω, U N ω ≤ T ω := fun N ω ↦ min_le_left _ _
  have hYint : ∀ i, Integrable (Y i) P := fun i ↦ (hY2 i).integrable (by norm_num)
  have hGint : ∀ N i, Integrable (G N i) P := fun N i ↦ by
    have hTint : Integrable (fun ω ↦ (T ω : ℝ)) P := hT2.integrable (by norm_num)
    have hset : MeasurableSet {ω | i < U N ω} :=
      measurableSet_lt measurable_const (hUmeas N)
    have heq : G N i = {ω | i < U N ω}.indicator (fun ω ↦ (T ω : ℝ)) := by
      funext ω
      by_cases hi : i < U N ω <;> simp [G, countIndicator, hi]
    rw [heq]
    exact hTint.indicator hset
  have hGindep : ∀ N i, IndepFun (G N i) (Y i) P := fun N i ↦ by
    change IndepFun
      (fun ω ↦ (T ω : ℝ) * if i < min (T ω) N then 1 else 0) (Y i) P
    simpa only [Function.comp_def, id_eq] using
      (hTindep i).comp
        (measurable_of_countable fun n : ℕ ↦
          (n : ℝ) * if i < min n N then 1 else 0) measurable_id
  have htermInt : ∀ N i, Integrable (fun ω ↦ G N i ω * Y i ω) P := fun N i ↦
    (hGindep N i).integrable_mul (hGint N i) (hYint i)
  have hfiniteZero : ∀ N, (∫ ω, stoppedSum (U N) Y ω * (T ω : ℝ) ∂P) = 0 := by
    intro N
    have hrepr : (fun ω ↦ stoppedSum (U N) Y ω * (T ω : ℝ)) =
        fun ω ↦ ∑ i ∈ range N, G N i ω * Y i ω := by
      funext ω
      rw [stoppedSum_eq_sum_countIndicator (hUbound N ω), sum_mul]
      apply sum_congr rfl
      intro i hi
      simp only [G]
      ring
    rw [hrepr, integral_finsetSum _ (fun i _ ↦ htermInt N i)]
    apply sum_eq_zero
    intro i hi
    rw [(hGindep N i).integral_fun_mul_eq_mul_integral
      (hGint N i).aestronglyMeasurable (hYint i).aestronglyMeasurable, hYcenter i, mul_zero]
  have hYmeas : ∀ i, AEStronglyMeasurable (Y i) P := fun i ↦ (hY2 i).aestronglyMeasurable
  have hstopMeas : ∀ N, AEStronglyMeasurable (stoppedSum (U N) Y) P := fun N ↦ by
    have hcind : ∀ i, AEStronglyMeasurable (countIndicator (U N) i) P := fun i ↦ by
      have hset : MeasurableSet {ω | i < U N ω} :=
        measurableSet_lt measurable_const (hUmeas N)
      have hm : Measurable (countIndicator (U N) i) := by
        unfold countIndicator
        exact measurable_const.ite hset measurable_const
      exact hm.aestronglyMeasurable
    have hsumMeas := Finset.aestronglyMeasurable_sum (range N)
      (fun i _ ↦ (hcind i).mul (hYmeas i))
    have hsumMeas' : AEStronglyMeasurable
        (fun ω ↦ ∑ i ∈ range N, countIndicator (U N) i ω * Y i ω) P := by
      apply hsumMeas.congr
      filter_upwards with ω
      simp only [Finset.sum_apply, Pi.mul_apply]
    apply hsumMeas'.congr
    filter_upwards with ω
    exact (stoppedSum_eq_sum_countIndicator (hUbound N ω)).symm
  have hR := integrable_count_mul_stoppedSum_sq hTmeas hT2 hY2 hYident hTindepSq
  have hTsq : Integrable (fun ω ↦ (T ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hT2.aestronglyMeasurable).mp hT2
  have hleft : Filter.Tendsto
      (fun N ↦ ∫ ω, stoppedSum (U N) Y ω * (T ω : ℝ) ∂P) Filter.atTop
      (nhds (∫ ω, stoppedSum T Y ω * (T ω : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω ↦ (T ω : ℝ) * stoppedSum T (fun i ω ↦ (Y i ω) ^ 2) ω +
        (T ω : ℝ) ^ 2)
    · intro N
      exact (hstopMeas N).mul
        ((measurable_of_countable fun n : ℕ ↦ (n : ℝ)).comp hTmeas).aestronglyMeasurable
    · exact hR.add hTsq
    · intro N
      filter_upwards with ω
      have hsquare := sq_stoppedSum_le_count_mul_stoppedSum_sq (Y := Y) (hUle N ω)
      have hTabs : 0 ≤ (T ω : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hTabs]
      have hsqAbs : |stoppedSum (U N) Y ω| ^ 2 = (stoppedSum (U N) Y ω) ^ 2 := by
        rw [sq_abs]
      nlinarith [sq_nonneg (|stoppedSum (U N) Y ω| - (T ω : ℝ))]
    · filter_upwards with ω
      apply tendsto_atTop_of_eventually_const (i₀ := T ω)
      intro N hN
      rw [stoppedSum, stoppedSum, show U N ω = T ω by simp [U, hN]]
  rw [show (fun N ↦ ∫ ω, stoppedSum (U N) Y ω * (T ω : ℝ) ∂P) =
      (fun _N ↦ (0 : ℝ)) from funext hfiniteZero] at hleft
  exact tendsto_nhds_unique hleft tendsto_const_nhds

/-- Bounded-count Wald identity.  This is the finite core used by the integrable-count theorem;
all interchanges here are finite and therefore require no hidden convergence assumption. -/
theorem integral_stoppedSum_eq_mul_of_bounded [IsProbabilityMeasure P]
    {T : Ω → ℕ} {X : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hXint : ∀ i, Integrable (X i) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hindep : ∀ i, IndepFun T (X i) P)
    {N : ℕ} (hTbound : ∀ᵐ ω ∂P, T ω ≤ N) :
    ∫ ω, stoppedSum T X ω ∂P =
      (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, X 0 ω ∂P := by
  have hset : ∀ i, MeasurableSet {ω | i < T ω} := fun i ↦ by
    exact measurableSet_lt measurable_const hTmeas
  have hcind : ∀ i, AEStronglyMeasurable (countIndicator T i) P := fun i ↦ by
    have hm : Measurable (countIndicator T i) := by
      unfold countIndicator
      exact measurable_const.ite (hset i) measurable_const
    exact hm.aestronglyMeasurable
  have htermInt : ∀ i, Integrable (fun ω ↦ countIndicator T i ω * X i ω) P := fun i ↦ by
    have heq : (fun ω ↦ countIndicator T i ω * X i ω) =
        {ω | i < T ω}.indicator (X i) := by
      funext ω
      by_cases hi : i < T ω <;> simp [countIndicator, hi]
    rw [heq]
    exact (hXint i).indicator (hset i)
  have hrepr : stoppedSum T X =ᵐ[P]
      fun ω ↦ ∑ i ∈ range N, countIndicator T i ω * X i ω :=
    hTbound.mono fun ω hω ↦ stoppedSum_eq_sum_countIndicator hω
  rw [integral_congr_ae hrepr, integral_finsetSum _ (fun i _ ↦ htermInt i)]
  have hfactor : ∀ i, (∫ ω, countIndicator T i ω * X i ω ∂P) =
      (∫ ω, countIndicator T i ω ∂P) * ∫ ω, X 0 ω ∂P := by
    intro i
    have hiIndep : IndepFun (countIndicator T i) (X i) P := by
      change IndepFun (fun ω ↦ if i < T ω then (1 : ℝ) else 0) (X i) P
      simpa only [Function.comp_def, id_eq] using
        (hindep i).comp (measurable_of_countable fun n : ℕ ↦ if i < n then (1 : ℝ) else 0)
          measurable_id
    have hi := hiIndep.integral_fun_mul_eq_mul_integral
      (hcind i) (hXint i).aestronglyMeasurable
    rw [hi, (hident i).integral_eq]
  simp_rw [hfactor, ← sum_mul]
  congr 1
  rw [← integral_finsetSum _]
  · apply integral_congr_ae
    filter_upwards [hTbound] with ω hω
    have hreprOne := stoppedSum_eq_sum_countIndicator
      (T := T) (X := fun _ _ ↦ 1) hω
    calc
      ∑ i ∈ range N, countIndicator T i ω = ∑ i ∈ range (T ω), (1 : ℝ) := by
        simpa only [stoppedSum, mul_one] using hreprOne.symm
      _ = (T ω : ℝ) := by simp
  · intro i hi
    have heq : countIndicator T i = {ω | i < T ω}.indicator (fun _ ↦ (1 : ℝ)) := by
      funext ω
      by_cases hit : i < T ω <;> simp [countIndicator, hit]
    rw [heq]
    exact (integrable_const 1).indicator (hset i)

/-- Wald's identity for an integrable natural-valued random count independent of every summand.
The result includes the integrability conclusion for the random sum. -/
theorem integrable_stoppedSum_and_integral_eq_mul [IsProbabilityMeasure P]
    {T : Ω → ℕ} {X : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hTint : Integrable (fun ω ↦ (T ω : ℝ)) P)
    (hXint : ∀ i, Integrable (X i) P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hindep : ∀ i, IndepFun T (X i) P) :
    Integrable (stoppedSum T X) P ∧
      ∫ ω, stoppedSum T X ω ∂P =
        (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, X 0 ω ∂P := by
  let F : ℕ → Ω → ℝ := fun i ω ↦ countIndicator T i ω * X i ω
  have hset : ∀ i, MeasurableSet {ω | i < T ω} := fun i ↦
    measurableSet_lt measurable_const hTmeas
  have hcind : ∀ i, AEStronglyMeasurable (countIndicator T i) P := fun i ↦ by
    have hm : Measurable (countIndicator T i) := by
      unfold countIndicator
      exact measurable_const.ite (hset i) measurable_const
    exact hm.aestronglyMeasurable
  have hFint : ∀ i, Integrable (F i) P := fun i ↦ by
    have heq : F i = {ω | i < T ω}.indicator (X i) := by
      funext ω
      by_cases hi : i < T ω <;> simp [F, countIndicator, hi]
    rw [heq]
    exact (hXint i).indicator (hset i)
  have hfactor : ∀ i, (∫ ω, F i ω ∂P) =
      P.real {ω | i < T ω} * ∫ ω, X 0 ω ∂P := by
    intro i
    have hiIndep : IndepFun (countIndicator T i) (X i) P := by
      change IndepFun (fun ω ↦ if i < T ω then (1 : ℝ) else 0) (X i) P
      simpa only [Function.comp_def, id_eq] using
        (hindep i).comp (measurable_of_countable fun n : ℕ ↦ if i < n then (1 : ℝ) else 0)
          measurable_id
    have hi := hiIndep.integral_fun_mul_eq_mul_integral
      (hcind i) (hXint i).aestronglyMeasurable
    have hindicator : countIndicator T i =
        {ω | i < T ω}.indicator 1 := by
      funext ω
      by_cases hit : i < T ω <;> simp [countIndicator, hit]
    have hcint : (∫ ω, countIndicator T i ω ∂P) = P.real {ω | i < T ω} := by
      rw [hindicator]
      simpa using integral_indicator_one (μ := P) (hset i)
    change (∫ ω, countIndicator T i ω * X i ω ∂P) =
      P.real {ω | i < T ω} * ∫ ω, X 0 ω ∂P
    rw [hi, (hident i).integral_eq, hcint]
  have hnormFactor : ∀ i, (∫ ω, ‖F i ω‖ ∂P) =
      P.real {ω | i < T ω} * ∫ ω, ‖X 0 ω‖ ∂P := by
    intro i
    have hiIndep : IndepFun (countIndicator T i) (fun ω ↦ ‖X i ω‖) P := by
      change IndepFun (fun ω ↦ if i < T ω then (1 : ℝ) else 0)
        (fun ω ↦ ‖X i ω‖) P
      simpa only [Function.comp_def] using
        (hindep i).comp (measurable_of_countable fun n : ℕ ↦ if i < n then (1 : ℝ) else 0)
          measurable_norm
    have hi := hiIndep.integral_fun_mul_eq_mul_integral
      (hcind i) (hXint i).norm.aestronglyMeasurable
    have hnorm : (fun ω ↦ ‖F i ω‖) =
        fun ω ↦ countIndicator T i ω * ‖X i ω‖ := by
      funext ω
      by_cases hit : i < T ω <;> simp [F, countIndicator, hit]
    have hindicator : countIndicator T i =
        {ω | i < T ω}.indicator 1 := by
      funext ω
      by_cases hit : i < T ω <;> simp [countIndicator, hit]
    have hcint : (∫ ω, countIndicator T i ω ∂P) = P.real {ω | i < T ω} := by
      rw [hindicator]
      simpa using integral_indicator_one (μ := P) (hset i)
    rw [hnorm, hi, (hident i).norm.integral_eq, hcint]
  have htailSummable : Summable fun i : ℕ ↦ P.real {ω | i < T ω} :=
    ENNReal.summable_toReal (tsum_measure_count_lt_ne_top hTmeas hTint)
  have hsumNorm : Summable fun i ↦ ∫ ω, ‖F i ω‖ ∂P := by
    apply (htailSummable.mul_right (∫ ω, ‖X 0 ω‖ ∂P)).congr
    intro i
    exact (hnormFactor i).symm
  have hpointSum : ∀ ω, Summable fun i ↦ ‖F i ω‖ := fun ω ↦ by
    apply summable_of_ne_finset_zero (s := range (T ω))
    intro i hi
    simp only [mem_range, not_lt] at hi
    simp [F, countIndicator, hi]
  have hboundInt := integrable_tsum_norm_of_summable_integral_norm F hFint hpointSum hsumNorm
  have hstoppedMeas : AEStronglyMeasurable (stoppedSum T X) P := by
    have hmeasTsum : AEStronglyMeasurable (fun ω ↦ ∑' i : ℕ, F i ω) P :=
      AEStronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
        (fun i : ℕ ↦ (hFint i).aestronglyMeasurable)
    apply hmeasTsum.congr
    filter_upwards with ω
    exact (stoppedSum_eq_tsum_countIndicator (T := T) (X := X) ω).symm
  have hstoppedInt : Integrable (stoppedSum T X) P := hboundInt.mono' hstoppedMeas (by
    filter_upwards with ω
    rw [stoppedSum_eq_tsum_countIndicator (T := T) (X := X) ω]
    exact norm_tsum_le_tsum_norm (hpointSum ω))
  refine ⟨hstoppedInt, ?_⟩
  calc
    ∫ ω, stoppedSum T X ω ∂P = ∫ ω, ∑' i, F i ω ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      exact stoppedSum_eq_tsum_countIndicator (T := T) (X := X) ω
    _ = ∑' i, ∫ ω, F i ω ∂P :=
      (integral_tsum_of_summable_integral_norm hFint hsumNorm).symm
    _ = ∑' i, P.real {ω | i < T ω} * ∫ ω, X 0 ω ∂P := tsum_congr hfactor
    _ = (∑' i, P.real {ω | i < T ω}) * ∫ ω, X 0 ω ∂P := tsum_mul_right
    _ = (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, X 0 ω ∂P := by
      rw [tsum_measureReal_count_lt_eq_integral hTmeas hTint]

/-- Blackwell--Girshick's variance identity.  The count is square-integrable and independent of
the whole random sequence, while the identically distributed summands are mutually independent
and square-integrable.  The theorem also proves that the random sum belongs to `L²`. -/
theorem memLp_stoppedSum_and_variance_eq [IsProbabilityMeasure P]
    {T : Ω → ℕ} {X : ℕ → Ω → ℝ} (hTmeas : Measurable T)
    (hT2 : MemLp (fun ω ↦ (T ω : ℝ)) 2 P)
    (hX2 : ∀ i, MemLp (X i) 2 P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXindep : iIndepFun X P)
    (hTXindep : IndepFun T (fun ω i ↦ X i ω) P) :
    MemLp (stoppedSum T X) 2 P ∧
      variance (stoppedSum T X) P =
        (∫ ω, (T ω : ℝ) ∂P) * variance (X 0) P +
          variance (fun ω ↦ (T ω : ℝ)) P * (∫ ω, X 0 ω ∂P) ^ 2 := by
  let μ : ℝ := ∫ ω, X 0 ω ∂P
  let Y : ℕ → Ω → ℝ := fun i ω ↦ X i ω - μ
  have hXint : ∀ i, Integrable (X i) P := fun i ↦ (hX2 i).integrable (by norm_num)
  have hTint : Integrable (fun ω ↦ (T ω : ℝ)) P := hT2.integrable (by norm_num)
  have hY2 : ∀ i, MemLp (Y i) 2 P := fun i ↦ by
    exact (hX2 i).sub (memLp_const μ)
  have hYint : ∀ i, Integrable (Y i) P := fun i ↦ (hY2 i).integrable (by norm_num)
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i ↦ by
    simpa only [Y, Function.comp_def, id_eq] using
      (hident i).comp (measurable_id.sub_const μ)
  have hYcenter : ∀ i, ∫ ω, Y i ω ∂P = 0 := fun i ↦ by
    simp only [Y]
    rw [integral_sub (hXint i) (integrable_const μ), (hident i).integral_eq]
    simp [μ]
  have hYindep : Pairwise fun i j ↦ IndepFun (Y i) (Y j) P := by
    intro i j hij
    simpa only [Y, Function.comp_def, id_eq] using
      (hXindep.indepFun hij).comp (measurable_id.sub_const μ) (measurable_id.sub_const μ)
  have hTXi : ∀ i, IndepFun T (X i) P := fun i ↦ by
    simpa only [Function.comp_def, id_eq] using
      hTXindep.comp measurable_id (measurable_pi_apply i)
  have hTYi : ∀ i, IndepFun T (Y i) P := fun i ↦ by
    simpa only [Y, Function.comp_def, id_eq] using
      (hTXi i).comp measurable_id (measurable_id.sub_const μ)
  have hTindepSq : ∀ i, IndepFun T (fun ω ↦ (Y i ω) ^ 2) P := fun i ↦ by
    have hmi : Measurable (fun x : ℕ → ℝ ↦ x i - μ) :=
      (measurable_pi_apply i).sub measurable_const
    have hm : Measurable (fun x : ℕ → ℝ ↦ (x i - μ) ^ 2) := hmi.pow_const 2
    simpa only [Y, Function.comp_def, id_eq] using hTXindep.comp measurable_id hm
  have hTindepMul : ∀ i j, IndepFun T (fun ω ↦ Y i ω * Y j ω) P := fun i j ↦ by
    have hmi : Measurable (fun x : ℕ → ℝ ↦ x i - μ) :=
      (measurable_pi_apply i).sub measurable_const
    have hmj : Measurable (fun x : ℕ → ℝ ↦ x j - μ) :=
      (measurable_pi_apply j).sub measurable_const
    have hm : Measurable (fun x : ℕ → ℝ ↦ (x i - μ) * (x j - μ)) := hmi.mul hmj
    simpa only [Y, Function.comp_def, id_eq] using hTXindep.comp measurable_id hm
  have hYwald := integrable_stoppedSum_and_integral_eq_mul hTmeas hTint hYint hYident hTYi
  have hYsumInt : Integrable (stoppedSum T Y) P := hYwald.1
  have hYsumMean : (∫ ω, stoppedSum T Y ω ∂P) = 0 := by
    rw [hYwald.2, hYcenter 0, mul_zero]
  have hR := integrable_count_mul_stoppedSum_sq hTmeas hT2 hY2 hYident hTindepSq
  have hYsumSqInt : Integrable (fun ω ↦ (stoppedSum T Y ω) ^ 2) P := by
    apply hR.mono' (hYsumInt.aestronglyMeasurable.pow 2)
    filter_upwards with ω
    change |(stoppedSum T Y ω) ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_stoppedSum_le_count_mul_stoppedSum_sq (Y := Y) (le_refl (T ω))
  have hYsum2 : MemLp (stoppedSum T Y) 2 P :=
    (memLp_two_iff_integrable_sq hYsumInt.aestronglyMeasurable).mpr hYsumSqInt
  have hcenterSecond := integral_sq_stoppedSum_eq_mul_centered hTmeas hT2 hY2 hYident
    hYcenter hYindep hTindepSq hTindepMul
  have hcenterCross := integral_stoppedSum_mul_count_eq_zero_centered hTmeas hT2 hY2
    hYident hYcenter hTYi hTindepSq
  have hsumIdentity : stoppedSum T X =
      fun ω ↦ stoppedSum T Y ω + μ * (T ω : ℝ) := by
    funext ω
    simp only [stoppedSum, Y, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
  have hSX2 : MemLp (stoppedSum T X) 2 P := by
    have hright : MemLp (fun ω ↦ stoppedSum T Y ω + μ * (T ω : ℝ)) 2 P :=
      hYsum2.add (hT2.const_mul μ)
    rw [hsumIdentity]
    exact hright
  refine ⟨hSX2, ?_⟩
  have hTsqInt : Integrable (fun ω ↦ (T ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hT2.aestronglyMeasurable).mp hT2
  have hcrossInt : Integrable (fun ω ↦ stoppedSum T Y ω * (T ω : ℝ)) P :=
    MemLp.integrable_mul hYsum2 hT2
  have hsecondX : (∫ ω, (stoppedSum T X ω) ^ 2 ∂P) =
      (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P +
        μ ^ 2 * ∫ ω, (T ω : ℝ) ^ 2 ∂P := by
    have hexpand : (fun ω ↦ (stoppedSum T X ω) ^ 2) = fun ω ↦
        (stoppedSum T Y ω) ^ 2 + (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) +
          (μ ^ 2) * (T ω : ℝ) ^ 2 := by
      funext ω
      rw [congrFun hsumIdentity ω]
      ring
    rw [hexpand]
    have hAB := integral_add hYsumSqInt (hcrossInt.const_mul (2 * μ))
    have hABC := integral_add (hYsumSqInt.add (hcrossInt.const_mul (2 * μ)))
      (hTsqInt.const_mul (μ ^ 2))
    have hB := integral_const_mul (μ := P) (2 * μ)
      (fun ω ↦ stoppedSum T Y ω * (T ω : ℝ))
    have hC := integral_const_mul (μ := P) (μ ^ 2) (fun ω ↦ (T ω : ℝ) ^ 2)
    calc
      (∫ ω, (stoppedSum T Y ω) ^ 2 +
          (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) +
          (μ ^ 2) * (T ω : ℝ) ^ 2 ∂P) =
          (∫ ω, (stoppedSum T Y ω) ^ 2 +
            (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) ∂P) +
            ∫ ω, (μ ^ 2) * (T ω : ℝ) ^ 2 ∂P := by
              simpa only [Pi.add_apply] using hABC
      _ = ((∫ ω, (stoppedSum T Y ω) ^ 2 ∂P) +
            ∫ ω, (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) ∂P) +
            ∫ ω, (μ ^ 2) * (T ω : ℝ) ^ 2 ∂P := by
              rw [show (∫ ω, (stoppedSum T Y ω) ^ 2 +
                (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) ∂P) =
                  (∫ ω, (stoppedSum T Y ω) ^ 2 ∂P) +
                    ∫ ω, (2 * μ) * (stoppedSum T Y ω * (T ω : ℝ)) ∂P by
                    simpa only [Pi.add_apply] using hAB]
      _ = (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P +
          μ ^ 2 * ∫ ω, (T ω : ℝ) ^ 2 ∂P := by
            rw [hB, hC, hcenterSecond, hcenterCross]
            ring
  have hmeanX := (integrable_stoppedSum_and_integral_eq_mul hTmeas hTint hXint hident hTXi).2
  have hvarX : (∫ ω, (Y 0 ω) ^ 2 ∂P) = variance (X 0) P := by
    symm
    simpa only [Y, μ] using variance_eq_integral (hX2 0).aemeasurable
  have hsecondX' : (∫ ω, (stoppedSum T X ^ 2) ω ∂P) =
      (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, (Y 0 ω) ^ 2 ∂P +
        μ ^ 2 * ∫ ω, (T ω : ℝ) ^ 2 ∂P := by
    simpa only [Pi.pow_apply] using hsecondX
  have hTsqVariance : variance (fun ω ↦ (T ω : ℝ)) P =
      (∫ ω, ((fun ω ↦ (T ω : ℝ)) ^ 2) ω ∂P) -
        (∫ ω, (T ω : ℝ) ∂P) ^ 2 := variance_eq_sub hT2
  rw [variance_eq_sub hSX2, hsecondX', hmeanX, hvarX, hTsqVariance]
  simp only [Pi.pow_apply]
  simp only [μ]
  ring

end

end ProbabilityTheory
