/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.DiscreteIntegral
public import StochLean.Probability.Martingale.QuadraticVariation
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Probability.Martingale.Convergence

/-!
# Convergence on the event of finite predictable quadratic variation

This file proves the discrete bracket criterion by the standard predictable localization.
At level `r`, the next martingale increment is retained exactly when the already predictable
quantity `⟨M⟩_(n+1)` is at most `r`.  This avoids the overshoot that would occur if one stopped
only after the bracket crossed the level.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The predictable `0`/`1` strategy that keeps the next increment while the bracket after that
increment is at most `r`. -/
noncomputable def bracketCutoffStrategy (M : ℕ → Ω → ℝ)
    (𝒜 : Filtration ℕ mΩ) (μ : Measure Ω) (r : ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ if predictableQuadraticVariation M 𝒜 μ n ω ≤ r then 1 else 0

@[simp]
theorem bracketCutoffStrategy_apply (M : ℕ → Ω → ℝ)
    (𝒜 : Filtration ℕ mΩ) (μ : Measure Ω) (r : ℝ) (n : ℕ) (ω : Ω) :
    bracketCutoffStrategy M 𝒜 μ r n ω =
      if predictableQuadraticVariation M 𝒜 μ n ω ≤ r then 1 else 0 := rfl

theorem isStronglyPredictable_bracketCutoffStrategy
    (M : ℕ → Ω → ℝ) (𝒜 : Filtration ℕ mΩ) (μ : Measure Ω) (r : ℝ) :
    IsStronglyPredictable 𝒜 (bracketCutoffStrategy M 𝒜 μ r) := by
  apply IsStronglyPredictable.of_measurable_add_one
  · have hzero : bracketCutoffStrategy M 𝒜 μ r 0 =
        fun _ : Ω ↦ if (0 : ℝ) ≤ r then 1 else 0 := by
      funext ω
      simp [bracketCutoffStrategy]
    rw [hzero]
    exact stronglyMeasurable_const
  · intro n
    apply StronglyMeasurable.ite
    · exact (isStronglyPredictable_predictableQuadraticVariation M 𝒜 μ).measurable_add_one n
        |>.measurableSet_le stronglyMeasurable_const
    · exact stronglyMeasurable_const
    · exact stronglyMeasurable_const

theorem bracketCutoffStrategy_abs_le_one
    (M : ℕ → Ω → ℝ) (𝒜 : Filtration ℕ mΩ) (μ : Measure Ω) (r : ℝ) :
    ∀ n ω, ‖bracketCutoffStrategy M 𝒜 μ r n ω‖ ≤ 1 := by
  intro n ω
  simp only [bracketCutoffStrategy_apply]
  split <;> simp

theorem Martingale.bracketCutoffIntegral
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ} [IsFiniteMeasure μ]
    (hM : Martingale M 𝒜 μ) (r : ℝ) :
    Martingale (MeasureTheory.discreteStochasticIntegral
      (bracketCutoffStrategy M 𝒜 μ r) M) 𝒜 μ := by
  exact hM.discreteStochasticIntegral
    (isStronglyPredictable_bracketCutoffStrategy M 𝒜 μ r)
    (fun n ↦ ⟨1, ae_of_all μ fun ω ↦ bracketCutoffStrategy_abs_le_one M 𝒜 μ r n ω⟩)

theorem memLp_two_bracketCutoffIntegral
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ} [IsFiniteMeasure μ]
    (hM_two : ∀ n, MemLp (M n) 2 μ) (r : ℝ) (n : ℕ) :
    MemLp (MeasureTheory.discreteStochasticIntegral
      (bracketCutoffStrategy M 𝒜 μ r) M n) 2 μ := by
  rw [discreteStochasticIntegral_eq_sum]
  apply memLp_finsetSum'
  intro k hk
  let s : Set Ω := {ω | predictableQuadraticVariation M 𝒜 μ (k + 1) ω ≤ r}
  have hsℱ : MeasurableSet[𝒜 k] s :=
    ((isStronglyPredictable_predictableQuadraticVariation M 𝒜 μ).measurable_add_one k)
      |>.measurableSet_le stronglyMeasurable_const
  have hs : MeasurableSet s := 𝒜.le k s hsℱ
  have hΔ : MemLp (M (k + 1) - M k) 2 μ := (hM_two (k + 1)).sub (hM_two k)
  have hi := hΔ.indicator hs
  convert hi using 1
  funext ω
  simp only [s, Set.indicator, Set.mem_ofPred_eq, Pi.sub_apply]
  split <;> simp_all

/-- The bracket sum produced by the cutoff strategy, written solely in terms of the original
bracket. -/
noncomputable def cutoffBracketSum (B : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, if B (k + 1) ω ≤ r then B (k + 1) ω - B k ω else 0

@[simp]
theorem cutoffBracketSum_zero (B : ℕ → Ω → ℝ) (r : ℝ) :
    cutoffBracketSum B r 0 = 0 := by
  ext ω
  simp [cutoffBracketSum]

theorem cutoffBracketSum_succ (B : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) :
    cutoffBracketSum B r (n + 1) ω = cutoffBracketSum B r n ω +
      if B (n + 1) ω ≤ r then B (n + 1) ω - B n ω else 0 := by
  simp [cutoffBracketSum, Finset.sum_range_succ]

private theorem cutoffBracketSum_eq_sub_of_le
    (B : ℕ → ℝ) (r : ℝ) (hB : Monotone B) {n : ℕ} (hn : B n ≤ r) :
    (∑ k ∈ Finset.range n, if B (k + 1) ≤ r then B (k + 1) - B k else 0) =
      B n - B 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : B n ≤ r := (hB (Nat.le_succ n)).trans hn
      rw [Finset.sum_range_succ, if_pos hn, ih hn']
      ring

private theorem cutoffBracketSum_le
    (B : ℕ → ℝ) (r : ℝ) (hB : Monotone B) (hB0 : B 0 = 0) (hr : 0 ≤ r)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, if B (k + 1) ≤ r then B (k + 1) - B k else 0) ≤ r := by
  induction n with
  | zero => simpa using hr
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hn : B (n + 1) ≤ r
      · rw [if_pos hn]
        calc
          _ = B (n + 1) - B 0 := by
            simpa [Finset.sum_range_succ, hn] using
              (cutoffBracketSum_eq_sub_of_le B r hB (n := n + 1) hn)
          _ = B (n + 1) := by rw [hB0, sub_zero]
          _ ≤ r := hn
      · rw [if_neg hn, add_zero]
        exact ih

theorem Martingale.predictableQuadraticVariation_bracketCutoffIntegral_ae_eq
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (_hM : Martingale M 𝒜 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    (r : ℝ) (n : ℕ) :
    predictableQuadraticVariation
        (MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M)
        𝒜 μ n =ᵐ[μ]
      cutoffBracketSum (predictableQuadraticVariation M 𝒜 μ) r n := by
  let B : ℕ → Ω → ℝ := predictableQuadraticVariation M 𝒜 μ
  let H : ℕ → Ω → ℝ := bracketCutoffStrategy M 𝒜 μ r
  let N : ℕ → Ω → ℝ := MeasureTheory.discreteStochasticIntegral H M
  induction n with
  | zero => simp
  | succ n ih =>
      let s : Set Ω := {ω | B (n + 1) ω ≤ r}
      have hsℱ : MeasurableSet[𝒜 n] s := by
        exact ((isStronglyPredictable_predictableQuadraticVariation M 𝒜 μ).measurable_add_one n)
          |>.measurableSet_le stronglyMeasurable_const
      have hs : MeasurableSet s := 𝒜.le n s hsℱ
      have hΔint : Integrable ((M (n + 1) - M n) ^ 2) μ :=
        ((hM_two (n + 1)).sub (hM_two n)).integrable_sq
      have hcond := condExp_indicator (μ := μ) hΔint hsℱ
      have hΔN : N (n + 1) - N n = s.indicator (M (n + 1) - M n) := by
        rw [show N (n + 1) - N n = H (n + 1) • (M (n + 1) - M n) by
          simp [N, discreteStochasticIntegral_succ]]
        ext ω
        simp only [H, B, s, Set.indicator, Set.mem_ofPred_eq, smul_eq_mul, Pi.sub_apply]
        split <;> simp_all
      rw [predictableQuadraticVariation_succ]
      have hsum_succ :
          cutoffBracketSum (predictableQuadraticVariation M 𝒜 μ) r (n + 1) =
            fun ω ↦ cutoffBracketSum (predictableQuadraticVariation M 𝒜 μ) r n ω +
              if predictableQuadraticVariation M 𝒜 μ (n + 1) ω ≤ r then
                predictableQuadraticVariation M 𝒜 μ (n + 1) ω -
                  predictableQuadraticVariation M 𝒜 μ n ω
              else 0 := by
        funext ω
        exact cutoffBracketSum_succ _ _ _ _
      rw [hsum_succ]
      filter_upwards [ih, hcond] with ω hih hce
      simp only [Pi.add_apply]
      rw [hih]
      have hsquare : (N (n + 1) - N n) ^ 2 =
          s.indicator ((M (n + 1) - M n) ^ 2) := by
        rw [hΔN]
        ext x
        by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
      rw [hsquare, hce]
      have hBstep : μ[(M (n + 1) - M n) ^ 2 | 𝒜 n] ω = B (n + 1) ω - B n ω := by
        have hrec := congrFun (predictableQuadraticVariation_succ M 𝒜 μ n) ω
        change B (n + 1) ω = B n ω +
          μ[(M (n + 1) - M n) ^ 2 | 𝒜 n] ω at hrec
        linarith
      by_cases hlevel : B (n + 1) ω ≤ r
      · have hmem : ω ∈ s := hlevel
        rw [Set.indicator_of_mem hmem, hBstep]
        rw [if_pos (show predictableQuadraticVariation M 𝒜 μ (n + 1) ω ≤ r from hlevel)]
      · have hmem : ω ∉ s := hlevel
        rw [Set.indicator_of_notMem hmem]
        rw [if_neg (show ¬ predictableQuadraticVariation M 𝒜 μ (n + 1) ω ≤ r from hlevel)]

theorem Martingale.predictableQuadraticVariation_bracketCutoffIntegral_ae_le
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hM : Martingale M 𝒜 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    predictableQuadraticVariation
        (MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M)
        𝒜 μ n ≤ᵐ[μ] fun _ ↦ r := by
  filter_upwards [hM.predictableQuadraticVariation_bracketCutoffIntegral_ae_eq hM_two r n,
    monotone_predictableQuadraticVariation hM.stronglyAdapted
      (fun k ↦ ((hM_two (k + 1)).sub (hM_two k)).integrable_sq)] with ω heq hmono
  rw [heq]
  exact cutoffBracketSum_le (fun k ↦ predictableQuadraticVariation M 𝒜 μ k ω)
    r hmono (by simp) hr n

private theorem eLpNorm_two_bracketCutoffIntegral_le
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hM : Martingale M 𝒜 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    eLpNorm
        (MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M n)
        2 μ ≤ (ENNReal.ofReal r) ^ (1 / 2 : ℝ) := by
  let N : ℕ → Ω → ℝ := MeasureTheory.discreteStochasticIntegral
    (bracketCutoffStrategy M 𝒜 μ r) M
  have hN : Martingale N 𝒜 μ := hM.bracketCutoffIntegral r
  have hN_two : ∀ k, MemLp (N k) 2 μ :=
    fun k ↦ memLp_two_bracketCutoffIntegral hM_two r k
  have hN_zero : N 0 = 0 := by
    simp [N]
  have hΔN : ∀ k, Integrable ((N (k + 1) - N k) ^ 2) μ :=
    fun k ↦ ((hN_two (k + 1)).sub (hN_two k)).integrable_sq
  have hbr_int : Integrable (predictableQuadraticVariation N 𝒜 μ n) μ :=
    integrable_predictableQuadraticVariation hΔN n
  have hbr_le : ∫ ω, predictableQuadraticVariation N 𝒜 μ n ω ∂μ ≤ r := by
    calc
      _ ≤ ∫ _ : Ω, r ∂μ := integral_mono_ae hbr_int (integrable_const r)
        (hM.predictableQuadraticVariation_bracketCutoffIntegral_ae_le hM_two hr n)
      _ = r := by simp
  have hsq_int : ∫ ω, (N n ω) ^ 2 ∂μ ≤ r := by
    rw [hN.integral_sq_eq_integral_predictableQuadraticVariation hN_two hN_zero n]
    exact hbr_le
  have hsq_integrable : Integrable (fun ω ↦ (N n ω) ^ 2) μ :=
    (hN_two n).integrable_sq
  have hlin : (∫⁻ ω, ‖N n ω‖ₑ ^ (2 : ℝ) ∂μ) ≤ ENNReal.ofReal r := by
    calc
      (∫⁻ ω, ‖N n ω‖ₑ ^ (2 : ℝ) ∂μ) =
          ∫⁻ ω, ENNReal.ofReal ((N n ω) ^ 2) ∂μ := by
            apply lintegral_congr
            intro ω
            rw [ENNReal.rpow_two, ← ofReal_norm,
              ← ENNReal.ofReal_pow (norm_nonneg (N n ω))]
            simp [sq_abs]
      _ = ENNReal.ofReal (∫ ω, (N n ω) ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hsq_integrable
          (ae_of_all μ fun ω ↦ sq_nonneg (N n ω))).symm
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hsq_int
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow hlin (by norm_num)

private theorem Martingale.ae_tendsto_bracketCutoffIntegral
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hM : Martingale M 𝒜 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ,
      Tendsto (fun n ↦
        MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M n ω)
        atTop (𝓝 c) := by
  let R : NNReal := ((ENNReal.ofReal r) ^ (1 / 2 : ℝ)).toNNReal
  apply (hM.bracketCutoffIntegral r).submartingale.exists_ae_tendsto_of_bdd (R := R)
  intro n
  calc
    eLpNorm
        (MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M n)
        1 μ ≤
      eLpNorm
        (MeasureTheory.discreteStochasticIntegral (bracketCutoffStrategy M 𝒜 μ r) M n)
        2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
          (memLp_two_bracketCutoffIntegral hM_two r n).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal r) ^ (1 / 2 : ℝ) :=
      eLpNorm_two_bracketCutoffIntegral_le hM hM_two hr n
    _ = (R : ENNReal) := by
      symm
      exact ENNReal.coe_toNNReal
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)

/-- **Klenke 11.14, finite-bracket criterion.** A square-integrable discrete martingale
converges almost surely on the event where its predictable quadratic variation is bounded (and
hence, by monotonicity, has a finite limit). -/
theorem Martingale.ae_tendsto_of_predictableQuadraticVariation_bdd
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hM : Martingale M 𝒜 μ) (hM_two : ∀ n, MemLp (M n) 2 μ)
    (hfinite : ∀ᵐ ω ∂μ, ∃ C : ℝ, ∀ n,
      predictableQuadraticVariation M 𝒜 μ n ω ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n ↦ M n ω) atTop (𝓝 c) := by
  have hcut : ∀ᵐ ω ∂μ, ∀ r : ℕ, ∃ c : ℝ,
      Tendsto (fun n ↦ MeasureTheory.discreteStochasticIntegral
        (bracketCutoffStrategy M 𝒜 μ (r : ℝ)) M n ω) atTop (𝓝 c) := by
    rw [ae_all_iff]
    intro r
    exact hM.ae_tendsto_bracketCutoffIntegral hM_two (Nat.cast_nonneg r)
  filter_upwards [hfinite, hcut] with ω hbound hconv
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨r, hr⟩ := exists_nat_ge C
  obtain ⟨c, hc⟩ := hconv r
  have hstrategy : ∀ n, bracketCutoffStrategy M 𝒜 μ (r : ℝ) n ω = 1 := by
    intro n
    simp [bracketCutoffStrategy, (hC n).trans hr]
  have hintegral : ∀ n,
      MeasureTheory.discreteStochasticIntegral
          (bracketCutoffStrategy M 𝒜 μ (r : ℝ)) M n ω =
        M n ω - M 0 ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [congrFun (discreteStochasticIntegral_succ
          (bracketCutoffStrategy M 𝒜 μ (r : ℝ)) M n) ω]
        change MeasureTheory.discreteStochasticIntegral
            (bracketCutoffStrategy M 𝒜 μ (r : ℝ)) M n ω +
          bracketCutoffStrategy M 𝒜 μ (r : ℝ) (n + 1) ω *
            (M (n + 1) ω - M n ω) = M (n + 1) ω - M 0 ω
        rw [hstrategy, ih]
        ring
  refine ⟨c + M 0 ω, ?_⟩
  have hadd := hc.add_const (M 0 ω)
  convert hadd using 1
  · funext n
    rw [hintegral]
    ring

end MeasureTheory
