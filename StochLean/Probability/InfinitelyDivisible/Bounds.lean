/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.ContinuousPowers
/-!
# Quantitative bounds for infinitely divisible characteristic functions

The normalized exponent is controlled under dyadic frequency scaling.  This yields the global
Gaussian lower bound of Klenke Corollary 16.11 and reusable decay-cost estimates.
-/

@[expose] public section


open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

theorem tendsto_nat_mul_one_sub_rexp_div (c : ℝ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (c / ((n + 1 : ℕ) : ℝ)))) atTop (nhds (-c)) := by
  have h := tendsto_nat_mul_cexp_sub_one_div (c : ℂ)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h.neg
  convert hre using 1
  · funext n
    change ((n + 1 : ℕ) : ℝ) * (1 - Real.exp (c / ((n + 1 : ℕ) : ℝ))) =
      (-(((n + 1 : ℕ) : ℂ) *
        (Complex.exp ((c : ℂ) / ((n + 1 : ℕ) : ℂ)) - 1))).re
    have harg : (c : ℂ) / ((n + 1 : ℕ) : ℂ) =
        ((c / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    have hexp : (Complex.exp ((c : ℂ) / ((n + 1 : ℕ) : ℂ))).re =
        Real.exp (c / ((n + 1 : ℕ) : ℝ)) := by
      rw [harg, Complex.exp_ofReal_re]
    simp only [Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.sub_re, Complex.one_re, zero_mul, sub_zero]
    rw [hexp]
    ring
  · simp

theorem normSq_exp_eq_rexp_two_re (z : ℂ) :
    Complex.normSq (Complex.exp z) = Real.exp (2 * z.re) := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, ← Real.exp_nat_mul]
  norm_num

/-- The real part of the characteristic exponent grows at most quadratically under frequency
doubling. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.four_mul_exponent_re_le
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    4 * (hμ.exponent t).re ≤ (hμ.exponent (2 * t)).re := by
  let left : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) *
    (1 - Complex.normSq
      (charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) (2 * t)))
  let right : ℕ → ℝ := fun n => 4 * (((n + 1 : ℕ) : ℝ) *
    (1 - Complex.normSq
      (charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t)))
  have hleft : Tendsto left atTop (nhds (-2 * (hμ.exponent (2 * t)).re)) := by
    have h := tendsto_nat_mul_one_sub_rexp_div (2 * (hμ.exponent (2 * t)).re)
    convert h using 1
    · funext n
      dsimp [left]
      rw [hμ.charFun_nthRoot, normSq_exp_eq_rexp_two_re]
      have hrediv : (hμ.exponent (2 * t) / ((n + 1 : ℕ) : ℂ)).re =
          (hμ.exponent (2 * t)).re / ((n + 1 : ℕ) : ℝ) := by
        change (hμ.exponent (2 * t) /
          (((n + 1 : ℕ) : ℝ) : ℂ)).re = _
        rw [Complex.div_ofReal_re]
      rw [hrediv]
      ring_nf
    · ring
  have hright : Tendsto right atTop (nhds (4 * (-2 * (hμ.exponent t).re))) := by
    have h := tendsto_nat_mul_one_sub_rexp_div (2 * (hμ.exponent t).re)
    apply Tendsto.const_mul 4 at h
    convert h using 1
    · funext n
      dsimp [right]
      rw [hμ.charFun_nthRoot, normSq_exp_eq_rexp_two_re]
      have hrediv : (hμ.exponent t / ((n + 1 : ℕ) : ℂ)).re =
          (hμ.exponent t).re / ((n + 1 : ℕ) : ℝ) := by
        change (hμ.exponent t /
          (((n + 1 : ℕ) : ℝ) : ℂ)).re = _
        rw [Complex.div_ofReal_re]
      rw [hrediv]
      ring_nf
    · ring
  have hineq : ∀ n, left n ≤ right n := by
    intro n
    dsimp [left, right]
    have hbase := one_sub_normSq_charFun_two_mul_le
      (hμ.nthRoot (n + 1) (Nat.succ_pos n)) t
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) *
          (4 * (1 - Complex.normSq
            (charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t))) :=
        mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)
      _ = _ := by ring
  have hlim := le_of_tendsto_of_tendsto' hleft hright hineq
  linarith

/-- The nonnegative decay cost of the characteristic function. -/
noncomputable def _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponentCost
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) : ℝ :=
  -(hμ.exponent t).re

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponentCost_zero
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) : hμ.exponentCost 0 = 0 := by
  change -(hμ.exponent 0).re = 0
  simp

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponent_re_nonpos
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    (hμ.exponent t).re ≤ 0 := by
  have hnorm := norm_charFun_le_one (μ := (μ : Measure ℝ)) t
  rw [← hμ.exp_exponent, Complex.norm_exp] at hnorm
  exact Real.exp_le_one_iff.mp hnorm

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponentCost_nonneg
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    0 ≤ hμ.exponentCost t := by
  exact neg_nonneg.mpr (hμ.exponent_re_nonpos t)

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.continuous_exponentCost
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    Continuous hμ.exponentCost := by
  exact (Complex.continuous_re.comp hμ.exponent.continuous).neg

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponentCost_two_mul_le
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    hμ.exponentCost (2 * t) ≤ 4 * hμ.exponentCost t := by
  change -(hμ.exponent (2 * t)).re ≤ 4 * (-(hμ.exponent t).re)
  linarith [hμ.four_mul_exponent_re_le t]

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponentCost_two_pow_mul_le
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (k : ℕ) (t : ℝ) :
    hμ.exponentCost ((2 : ℝ) ^ k * t) ≤
      (4 : ℝ) ^ k * hμ.exponentCost t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have htwo := hμ.exponentCost_two_mul_le ((2 : ℝ) ^ k * t)
      rw [show 2 ^ k * 2 * t = 2 * (2 ^ k * t) by ring]
      calc
        _ ≤ 4 * hμ.exponentCost ((2 : ℝ) ^ k * t) := htwo
        _ ≤ 4 * ((4 : ℝ) ^ k * hμ.exponentCost t) := by gcongr
        _ = (4 : ℝ) ^ k * 4 * hμ.exponentCost t := by ring

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exists_local_exponentCost_lt_log_two
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → hμ.exponentCost t ≤ Real.log 2 := by
  have hc : ContinuousAt hμ.exponentCost 0 := hμ.continuous_exponentCost.continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.1 hc)
      (Real.log 2) (Real.log_pos (by norm_num))
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro t ht
  have ht' : |t| < δ := ht.trans_lt (half_lt_self hδ)
  have hdist := hclose (by simpa [Real.dist_eq] using ht')
  exact (by simpa [Real.dist_eq, hμ.exponentCost_zero,
    abs_of_nonneg (hμ.exponentCost_nonneg t)] using hdist :
      hμ.exponentCost t < Real.log 2).le

theorem exists_dyadic_upper (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    ∃ k : ℕ, |t| ≤ (2 : ℝ) ^ k * δ := by
  have htend : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * δ) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hδ
  exact ((tendsto_atTop.1 htend) |t|).exists

/-- Corollary 16.11: an infinitely divisible characteristic function admits a global Gaussian
lower bound (up to the source's factor `1/2`). -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exists_gaussian_charFun_lowerBound
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ,
      (1 / 2 : ℝ) * Real.exp (-ε * t ^ 2) ≤ ‖charFun (μ : Measure ℝ) t‖ := by
  obtain ⟨δ, hδ, hlocal⟩ := hμ.exists_local_exponentCost_lt_log_two
  let ε : ℝ := 4 * Real.log 2 / δ ^ 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  intro t
  have hcost : hμ.exponentCost t ≤ Real.log 2 + ε * t ^ 2 := by
    by_cases ht : |t| ≤ δ
    · exact (hlocal t ht).trans (le_add_of_nonneg_right (mul_nonneg hε.le (sq_nonneg t)))
    · have htδ : δ < |t| := lt_of_not_ge ht
      let P : ℕ → Prop := fun k => |t| ≤ (2 : ℝ) ^ k * δ
      have hex : ∃ k, P k := exists_dyadic_upper δ hδ t
      let k : ℕ := Nat.find hex
      have hk : P k := Nat.find_spec hex
      change |t| ≤ (2 : ℝ) ^ k * δ at hk
      have hkpos : 0 < k := by
        by_contra hk0
        have : k = 0 := Nat.eq_zero_of_not_pos hk0
        rw [this] at hk
        norm_num at hk
        exact (not_le_of_gt htδ) hk
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      have hprevNot : ¬ P j := by
        apply Nat.find_min hex
        omega
      have hprev : (2 : ℝ) ^ j * δ < |t| := lt_of_not_ge hprevNot
      let s : ℝ := t / (2 : ℝ) ^ k
      have hpowpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      have hsabs : |s| ≤ δ := by
        dsimp [s]
        rw [abs_div, abs_of_pos hpowpos]
        exact (div_le_iff₀ hpowpos).2 (by nlinarith)
      have hslocal : hμ.exponentCost s ≤ Real.log 2 := by
        exact hlocal s hsabs
      have hscale := hμ.exponentCost_two_pow_mul_le k s
      have harg : (2 : ℝ) ^ k * s = t := by
        dsimp [s]
        field_simp
      rw [harg] at hscale
      have hcostPow : hμ.exponentCost t ≤ (4 : ℝ) ^ k * Real.log 2 :=
        hscale.trans (mul_le_mul_of_nonneg_left hslocal (pow_nonneg (by norm_num) k))
      have hpowidentity : (4 : ℝ) ^ k * δ ^ 2 =
          4 * (((2 : ℝ) ^ j * δ) ^ 2) := by
        have hfour : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
          calc
            (4 : ℝ) ^ j = ((2 : ℝ) * 2) ^ j := by norm_num
            _ = (2 : ℝ) ^ j * 2 ^ j := by rw [mul_pow]
            _ = ((2 : ℝ) ^ j) ^ 2 := by ring
        rw [hj, pow_succ, hfour]
        ring
      have hsq : (4 : ℝ) ^ k * δ ^ 2 ≤ 4 * t ^ 2 := by
        rw [hpowidentity]
        have hnonneg : 0 ≤ (2 : ℝ) ^ j * δ := mul_nonneg (pow_nonneg (by norm_num) j) hδ.le
        have habsnonneg : 0 ≤ |t| := abs_nonneg t
        have hsquare := (sq_lt_sq₀ hnonneg habsnonneg).2 hprev
        rw [sq_abs] at hsquare
        nlinarith
      have hpowlog : (4 : ℝ) ^ k * Real.log 2 ≤ ε * t ^ 2 := by
        dsimp [ε]
        have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hδsq).2
        calc
          (4 : ℝ) ^ k * Real.log 2 * δ ^ 2 =
              Real.log 2 * ((4 : ℝ) ^ k * δ ^ 2) := by ring
          _ ≤ Real.log 2 * (4 * t ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (Real.log_nonneg (by norm_num))
          _ = 4 * Real.log 2 * t ^ 2 := by ring
      exact hcostPow.trans <| hpowlog.trans (le_add_of_nonneg_left (Real.log_nonneg (by norm_num)))
  rw [← hμ.exp_exponent, Complex.norm_exp]
  have hrew : (hμ.exponent t).re = -hμ.exponentCost t := by
    change (hμ.exponent t).re = -(-(hμ.exponent t).re)
    ring
  rw [hrew]
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hcost)
  have hlog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    (1 / 2 : ℝ) * Real.exp (-ε * t ^ 2) =
        Real.exp (-(Real.log 2 + ε * t ^ 2)) := by
      rw [neg_add, Real.exp_add, hlog]
      congr 1
      ring
    _ ≤ Real.exp (-hμ.exponentCost t) := hexp

end ProbabilityTheory
