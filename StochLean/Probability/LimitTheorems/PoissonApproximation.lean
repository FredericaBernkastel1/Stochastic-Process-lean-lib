/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import StochLean.Probability.Convergence.Discrete
public import StochLean.Probability.GeneratingFunction.RandomSum

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Poisson approximation

Mathlib `v4.33.0` already contains the identically distributed binomial point-probability limit
theorem under the canonical name
`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`. StochLean re-exports that result
and adds the non-identically distributed triangular-array theorem.

A row is represented as a finite list of Bernoulli parameters. Its law is built by recursive
independent convolution. If the row sums converge to `rate` and either the row sums of squares or
the largest parameter converge to zero, then every point mass converges to the corresponding
Poisson mass. The proof passes through probability generating functions and an explicit logarithmic
remainder estimate.
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal Nat BigOperators

namespace PMF

noncomputable section

/-- The natural-number-valued Bernoulli law with success probability `p`. -/
def bernoulliNat (p : unitInterval) : PMF ℕ :=
  (ProbabilityTheory.bernoulliMeasure (1 : ℕ) 0 p).toPMF

lemma massReal_bernoulliNat (p : unitInterval) (n : ℕ) :
    (bernoulliNat p).massReal n =
      if n = 1 then (p : ℝ) else if n = 0 then 1 - p else 0 := by
  classical
  simp only [massReal, bernoulliNat, Measure.toPMF_apply]
  by_cases h1 : n = 1
  · subst n
    simp
  · by_cases h0 : n = 0
    · subst n
      simp
    · rw [if_neg h1, if_neg h0]
      rw [ProbabilityTheory.bernoulliMeasure_apply p (measurableSet_singleton n)]
      simp [Ne.symm h1, Ne.symm h0]

@[simp]
lemma pgf_bernoulliNat (p : unitInterval) (z : unitInterval) :
    (bernoulliNat p).pgf z = 1 - (p : ℝ) + p * z := by
  rw [pgf, ← (bernoulliNat p).summable_pgf z |>.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, massReal_bernoulliNat,
    if_true, pow_zero, mul_one, pow_one]
  simp

/-- The law of the sum of one independent Bernoulli variable for every parameter in a row. -/
def poissonBinomial : List unitInterval → PMF ℕ
  | [] => PMF.pure 0
  | p :: ps => convolution (bernoulliNat p) (poissonBinomial ps)

@[simp]
lemma pgf_poissonBinomial (ps : List unitInterval) (z : unitInterval) :
    (poissonBinomial ps).pgf z =
      (ps.map fun p ↦ (1 - (p : ℝ) + p * z)).prod := by
  induction ps with
  | nil => simp [poissonBinomial]
  | cons p ps ih => simp [poissonBinomial, pgf_convolution, ih]

/-- The canonical Poisson measure, regarded as a natural-number-valued probability mass
function. -/
def poissonNat (rate : ℝ≥0) : PMF ℕ :=
  (ProbabilityTheory.poissonMeasure rate).toPMF

lemma massReal_poissonNat (rate : ℝ≥0) (n : ℕ) :
    (poissonNat rate).massReal n = Real.exp (-rate) * (rate : ℝ) ^ n / (n)! := by
  rw [massReal, poissonNat, Measure.toPMF_apply]
  exact ProbabilityTheory.poissonMeasure_real_singleton rate n

@[simp]
lemma pgf_poissonNat (rate : ℝ≥0) (z : unitInterval) :
    (poissonNat rate).pgf z = Real.exp ((rate : ℝ) * ((z : ℝ) - 1)) := by
  rw [pgf]
  simp_rw [massReal_poissonNat]
  calc
    ∑' n : ℕ, (Real.exp (-rate) * (rate : ℝ) ^ n / (n)!) * (z : ℝ) ^ n =
        Real.exp (-rate) * ∑' n : ℕ, (((rate : ℝ) * z) ^ n / (n)!) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [mul_pow]
      ring
    _ = Real.exp (-rate) * Real.exp ((rate : ℝ) * z) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((rate : ℝ) * z)).tsum_eq]
      rw [← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((rate : ℝ) * ((z : ℝ) - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end PMF

namespace ProbabilityTheory

noncomputable section

/-- The probability generating function of the law of a natural-valued random variable is the
expectation of the corresponding random power. -/
lemma HasLaw.pgf_eq_integral_pow {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Y : Ω → ℕ} {μ : Measure ℕ} [IsProbabilityMeasure μ]
    (hY : HasLaw Y μ P) (z : unitInterval) :
    μ.pgf z = ∫ ω, (z : ℝ) ^ Y ω ∂P := by
  have hf : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) μ := by
    refine ⟨(measurable_of_countable fun n : ℕ ↦ (z : ℝ) ^ n).aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded (C := 1) <| Eventually.of_forall fun n ↦ by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg z.2.1]
      exact pow_le_one₀ z.2.1 z.2.2
  calc
    μ.pgf z = ∫ n, (z : ℝ) ^ n ∂μ.toPMF.toMeasure := by
      have hf' : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) μ.toPMF.toMeasure := by
        simpa only [Measure.toPMF_toMeasure] using hf
      rw [Measure.pgf, PMF.integral_eq_tsum μ.toPMF _ hf']
      rfl
    _ = ∫ n, (z : ℝ) ^ n ∂μ := by rw [Measure.toPMF_toMeasure]
    _ = ∫ ω, (z : ℝ) ^ Y ω ∂P := (hY.integral_comp hf.aestronglyMeasurable).symm

/-- A finite sum of independent identically distributed natural-valued Bernoulli variables has
the corresponding Poisson-binomial law. -/
theorem iIndepFun.hasLaw_fintype_sum_bernoulli {Ω ι : Type*}
    {mΩ : MeasurableSpace Ω} [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ι → Ω → ℕ} {p : unitInterval}
    (hIndep : iIndepFun Y P)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℕ) 0 p) P) :
    HasLaw (fun ω ↦ ∑ i, Y i ω)
      (PMF.poissonBinomial (List.replicate (Fintype.card ι) p)).toMeasure P := by
  let S : Ω → ℕ := fun ω ↦ ∑ i, Y i ω
  have hS : AEMeasurable S P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hLaw i).aemeasurable
  have hSelf : HasLaw S (P.map S) P := ⟨hS, rfl⟩
  let _ : IsProbabilityMeasure (P.map S) := hSelf.isProbabilityMeasure_iff.mp inferInstance
  refine ⟨hS, ?_⟩
  change P.map S = _
  rw [← PMF.toPMF_eq_iff_toMeasure_eq]
  apply PMF.ext_pgf
  funext z
  change (P.map S).pgf z = _
  rw [hSelf.pgf_eq_integral_pow]
  have hprod := hIndep.integral_fun_prod_comp
    (fun i ↦ (hLaw i).aemeasurable)
    (fun i ↦ (measurable_of_countable fun n : ℕ ↦ (z : ℝ) ^ n).aestronglyMeasurable)
  calc
    (∫ ω, (z : ℝ) ^ S ω ∂P) = ∫ ω, ∏ i, (z : ℝ) ^ Y i ω ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω ↦ by
        simpa [S] using
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ Y i ω) (z : ℝ)).symm
    _ = ∏ i, ∫ ω, (z : ℝ) ^ Y i ω ∂P := hprod
    _ = ∏ _i : ι, (PMF.bernoulliNat p).pgf z := by
      apply Finset.prod_congr rfl
      intro i _
      change (∫ ω, (z : ℝ) ^ Y i ω ∂P) =
        (bernoulliMeasure (1 : ℕ) 0 p).pgf z
      exact (hLaw i).pgf_eq_integral_pow z |>.symm
    _ = (PMF.poissonBinomial (List.replicate (Fintype.card ι) p)).pgf z := by
      rw [PMF.pgf_poissonBinomial]
      simp

/-- The sum of the Bernoulli parameters in one triangular-array row. -/
def bernoulliRowSum (ps : List unitInterval) : ℝ :=
  (ps.map fun p ↦ (p : ℝ)).sum

/-- The sum of the squared Bernoulli parameters in one triangular-array row. -/
def bernoulliRowSquareSum (ps : List unitInterval) : ℝ :=
  (ps.map fun p ↦ (p : ℝ) ^ 2).sum

/-- The largest Bernoulli parameter in one row, with value zero on the empty row. -/
def bernoulliRowMax : List unitInterval → ℝ
  | [] => 0
  | p :: ps => max (p : ℝ) (bernoulliRowMax ps)

/-- The sum of logarithms used to compare the row PGF with the limiting Poisson PGF. -/
def bernoulliRowLog (a : ℝ) (ps : List unitInterval) : ℝ :=
  (ps.map fun p ↦ Real.log (1 - a * (p : ℝ))).sum

lemma abs_add_log_one_sub_le_two_mul_sq {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x < 1 / 2) :
    |x + Real.log (1 - x)| ≤ 2 * x ^ 2 := by
  have hxabs : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hxabs 1
  norm_num [Finset.sum_range_succ] at h
  rw [abs_of_nonneg hx0] at h
  calc
    |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]

lemma abs_bernoulliRowLog_add_le (ps : List unitInterval) {a : ℝ} (ha0 : 0 ≤ a)
    (hhalf : ∀ p ∈ ps, a * (p : ℝ) < 1 / 2) :
    |bernoulliRowLog a ps + a * bernoulliRowSum ps| ≤
      2 * a ^ 2 * bernoulliRowSquareSum ps := by
  induction ps with
  | nil => simp [bernoulliRowLog, bernoulliRowSum, bernoulliRowSquareSum]
  | cons p ps ih =>
      have hp0 : 0 ≤ a * (p : ℝ) := mul_nonneg ha0 p.property.1
      have hpHalf : a * (p : ℝ) < 1 / 2 := hhalf p (by simp)
      have hp := abs_add_log_one_sub_le_two_mul_sq hp0 hpHalf
      have htail := ih (fun q hq ↦ hhalf q (by simp [hq]))
      rw [bernoulliRowLog, bernoulliRowSum, bernoulliRowSquareSum]
      calc
        |Real.log (1 - a * (p : ℝ)) + bernoulliRowLog a ps +
            a * ((p : ℝ) + bernoulliRowSum ps)| =
            |(a * (p : ℝ) + Real.log (1 - a * (p : ℝ))) +
              (bernoulliRowLog a ps + a * bernoulliRowSum ps)| := by ring_nf
        _ ≤ |a * (p : ℝ) + Real.log (1 - a * (p : ℝ))| +
            |bernoulliRowLog a ps + a * bernoulliRowSum ps| := abs_add_le _ _
        _ ≤ 2 * (a * (p : ℝ)) ^ 2 + 2 * a ^ 2 * bernoulliRowSquareSum ps :=
          add_le_add hp htail
        _ = 2 * a ^ 2 * ((p : ℝ) ^ 2 + bernoulliRowSquareSum ps) := by ring

lemma square_le_bernoulliRowSquareSum {p : unitInterval} {ps : List unitInterval}
    (hp : p ∈ ps) : (p : ℝ) ^ 2 ≤ bernoulliRowSquareSum ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      rw [bernoulliRowSquareSum]
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_add_of_nonneg_right (by
          rw [bernoulliRowSquareSum] at *
          exact List.sum_nonneg fun x hx ↦ by
            obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
            exact sq_nonneg (y : ℝ))
      · exact (ih hp).trans (le_add_of_nonneg_left (sq_nonneg (q : ℝ)))

lemma bernoulliRowSum_nonneg (ps : List unitInterval) : 0 ≤ bernoulliRowSum ps := by
  induction ps with
  | nil => simp [bernoulliRowSum]
  | cons p ps ih =>
      rw [bernoulliRowSum]
      exact add_nonneg p.property.1 ih

lemma bernoulliRowSquareSum_nonneg (ps : List unitInterval) :
    0 ≤ bernoulliRowSquareSum ps := by
  rw [bernoulliRowSquareSum]
  exact List.sum_nonneg fun x hx ↦ by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg (p : ℝ)

lemma bernoulliRowSquareSum_le_max_mul_sum (ps : List unitInterval) :
    bernoulliRowSquareSum ps ≤ bernoulliRowMax ps * bernoulliRowSum ps := by
  induction ps with
  | nil => simp [bernoulliRowSquareSum, bernoulliRowMax, bernoulliRowSum]
  | cons p ps ih =>
      have htail : bernoulliRowSquareSum ps ≤
          max (p : ℝ) (bernoulliRowMax ps) * bernoulliRowSum ps :=
        ih.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (bernoulliRowSum_nonneg ps))
      have hp : (p : ℝ) ^ 2 ≤ max (p : ℝ) (bernoulliRowMax ps) * p := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) p.property.1
      rw [bernoulliRowSquareSum, bernoulliRowMax, bernoulliRowSum]
      calc
        (p : ℝ) ^ 2 + bernoulliRowSquareSum ps ≤
            max (p : ℝ) (bernoulliRowMax ps) * p +
              max (p : ℝ) (bernoulliRowMax ps) * bernoulliRowSum ps :=
          add_le_add hp htail
        _ = max (p : ℝ) (bernoulliRowMax ps) *
            ((p : ℝ) + bernoulliRowSum ps) := by ring

lemma exp_bernoulliRowLog (ps : List unitInterval) {a : ℝ}
    (hpos : ∀ p ∈ ps, 0 < 1 - a * (p : ℝ)) :
    Real.exp (bernoulliRowLog a ps) =
      (ps.map fun p ↦ 1 - a * (p : ℝ)).prod := by
  induction ps with
  | nil => simp [bernoulliRowLog]
  | cons p ps ih =>
      change Real.exp (Real.log (1 - a * (p : ℝ)) + bernoulliRowLog a ps) =
        (1 - a * (p : ℝ)) * (ps.map fun q ↦ 1 - a * (q : ℝ)).prod
      rw [Real.exp_add, Real.exp_log (hpos p (by simp)),
        ih (fun q hq ↦ hpos q (by simp [hq]))]

/-- Under vanishing squared row sums, the logarithm of the Poisson-binomial PGF has the
expected linear limit. -/
theorem tendsto_bernoulliRowLog {rows : ℕ → List unitInterval} {a rate : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsum : Tendsto (fun n ↦ bernoulliRowSum (rows n)) atTop (nhds rate))
    (hsq : Tendsto (fun n ↦ bernoulliRowSquareSum (rows n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ bernoulliRowLog a (rows n)) atTop (nhds (-a * rate)) := by
  have hsqSmall : ∀ᶠ n in atTop, bernoulliRowSquareSum (rows n) < 1 / 4 :=
    hsq.eventually (Iio_mem_nhds (by norm_num))
  have hhalf : ∀ᶠ n in atTop, ∀ p ∈ rows n, a * (p : ℝ) < 1 / 2 := by
    filter_upwards [hsqSmall] with n hn p hp
    have hpSq := square_le_bernoulliRowSquareSum hp
    have hp0 : 0 ≤ (p : ℝ) := p.property.1
    have hap0 : 0 ≤ a * (p : ℝ) := mul_nonneg ha0 hp0
    have hap_le : a * (p : ℝ) ≤ (p : ℝ) := by
      nlinarith [p.property.2]
    nlinarith [sq_nonneg (a * (p : ℝ)), sq_nonneg ((p : ℝ) - a * (p : ℝ))]
  have herrBound : ∀ᶠ n in atTop,
      ‖bernoulliRowLog a (rows n) + a * bernoulliRowSum (rows n)‖ ≤
        2 * a ^ 2 * bernoulliRowSquareSum (rows n) := by
    filter_upwards [hhalf] with n hn
    simpa only [Real.norm_eq_abs] using abs_bernoulliRowLog_add_le (rows n) ha0 hn
  have hright : Tendsto (fun n ↦ 2 * a ^ 2 * bernoulliRowSquareSum (rows n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hsq.const_mul (2 * a ^ 2)
  have herr : Tendsto
      (fun n ↦ bernoulliRowLog a (rows n) + a * bernoulliRowSum (rows n))
      atTop (nhds 0) := squeeze_zero_norm' herrBound hright
  have hmain := herr.sub (hsum.const_mul a)
  simpa using hmain

/-- The PGFs of a Bernoulli triangular array converge pointwise to the Poisson PGF when the
row sums converge and the squared row sums vanish. -/
theorem tendsto_poissonBinomial_pgf {rows : ℕ → List unitInterval} {rate : ℝ≥0}
    (hsum : Tendsto (fun n ↦ bernoulliRowSum (rows n)) atTop (nhds (rate : ℝ)))
    (hsq : Tendsto (fun n ↦ bernoulliRowSquareSum (rows n)) atTop (nhds 0))
    (z : unitInterval) :
    Tendsto (fun n ↦ (PMF.poissonBinomial (rows n)).pgf z) atTop
      (nhds ((PMF.poissonNat rate).pgf z)) := by
  let a : ℝ := 1 - (z : ℝ)
  have ha0 : 0 ≤ a := sub_nonneg.mpr z.property.2
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [z.property.1]
  have hlog := tendsto_bernoulliRowLog ha0 ha1 hsum hsq
  have hsqSmall : ∀ᶠ n in atTop, bernoulliRowSquareSum (rows n) < 1 / 4 :=
    hsq.eventually (Iio_mem_nhds (by norm_num))
  have hpos : ∀ᶠ n in atTop, ∀ p ∈ rows n, 0 < 1 - a * (p : ℝ) := by
    filter_upwards [hsqSmall] with n hn p hp
    have hpSq := square_le_bernoulliRowSquareSum hp
    have hp0 : 0 ≤ (p : ℝ) := p.property.1
    have hap0 : 0 ≤ a * (p : ℝ) := mul_nonneg ha0 hp0
    have hap_le : a * (p : ℝ) ≤ (p : ℝ) := by
      nlinarith [p.property.2]
    nlinarith [sq_nonneg (a * (p : ℝ)), sq_nonneg ((p : ℝ) - a * (p : ℝ))]
  rw [PMF.pgf_poissonNat]
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have htarget : Real.exp (-a * (rate : ℝ)) =
      Real.exp ((rate : ℝ) * ((z : ℝ) - 1)) := by
    congr 1
    dsimp [a]
    ring
  rw [← htarget]
  apply Tendsto.congr' ?_ hexp
  filter_upwards [hpos] with n hn
  rw [Function.comp_apply, exp_bernoulliRowLog (rows n) hn, PMF.pgf_poissonBinomial]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  dsimp [a]
  ring

/-- Poisson limit theorem for a non-identically distributed Bernoulli triangular array, in the
square-smallness form. Every point probability converges to the corresponding Poisson mass. -/
theorem poissonBinomial_tendsto_poissonNat {rows : ℕ → List unitInterval} {rate : ℝ≥0}
    (hsum : Tendsto (fun n ↦ bernoulliRowSum (rows n)) atTop (nhds (rate : ℝ)))
    (hsq : Tendsto (fun n ↦ bernoulliRowSquareSum (rows n)) atTop (nhds 0)) :
    ∀ k, Tendsto (fun n ↦ (PMF.poissonBinomial (rows n)).massReal k) atTop
      (nhds ((PMF.poissonNat rate).massReal k)) :=
  PMF.tendsto_mass_of_tendsto_pgf fun z ↦ tendsto_poissonBinomial_pgf hsum hsq z

theorem tendsto_bernoulliRowSquareSum_of_max {rows : ℕ → List unitInterval}
    {rate : ℝ}
    (hsum : Tendsto (fun n ↦ bernoulliRowSum (rows n)) atTop (nhds rate))
    (hmax : Tendsto (fun n ↦ bernoulliRowMax (rows n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ bernoulliRowSquareSum (rows n)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ bernoulliRowSquareSum_nonneg (rows n)
  · exact Filter.Eventually.of_forall fun n ↦ bernoulliRowSquareSum_le_max_mul_sum (rows n)
  · simpa only [zero_mul] using hmax.mul hsum

/-- Classical maximum-smallness form of the Bernoulli triangular-array Poisson limit theorem. -/
theorem poissonBinomial_tendsto_poissonNat_of_max
    {rows : ℕ → List unitInterval} {rate : ℝ≥0}
    (hsum : Tendsto (fun n ↦ bernoulliRowSum (rows n)) atTop (nhds (rate : ℝ)))
    (hmax : Tendsto (fun n ↦ bernoulliRowMax (rows n)) atTop (nhds 0)) :
    ∀ k, Tendsto (fun n ↦ (PMF.poissonBinomial (rows n)).massReal k) atTop
      (nhds ((PMF.poissonNat rate).massReal k)) :=
  poissonBinomial_tendsto_poissonNat hsum
    (tendsto_bernoulliRowSquareSum_of_max hsum hmax)

end

end ProbabilityTheory
