/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Convolution roots and continuous characteristic exponents

This module develops the root theory of real infinitely divisible laws internally.  In particular,
it proves nonvanishing of characteristic functions, constructs the uniquely normalized continuous
characteristic exponent, and proves uniqueness and the characteristic-function formula for every
positive convolution root.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

noncomputable def negMap (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  μ.map (by fun_prop : AEMeasurable (fun x : ℝ => -x) μ)

@[simp, norm_cast]
theorem coe_negMap (μ : ProbabilityMeasure ℝ) :
    ((negMap μ : ProbabilityMeasure ℝ) : Measure ℝ) =
      (μ : Measure ℝ).map (fun x => -x) := rfl

theorem charFun_negMap (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (negMap μ : Measure ℝ) t = starRingEnd ℂ (charFun (μ : Measure ℝ) t) := by
  rw [coe_negMap]
  convert charFun_map_mul (μ := (μ : Measure ℝ)) (-1) t using 1
  · simp
  · rw [show (-1 : ℝ) * t = -t by ring, charFun_neg]

noncomputable def symmetrization (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  conv μ (negMap μ)

theorem charFun_symmetrization (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (symmetrization μ : Measure ℝ) t =
      (Complex.normSq (charFun (μ : Measure ℝ) t) : ℂ) := by
  rw [symmetrization, coe_conv, charFun_conv, charFun_negMap, Complex.mul_conj]

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

theorem one_sub_charFun_re_two_mul_le (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    1 - (charFun (μ : Measure ℝ) (2 * t)).re ≤
      4 * (1 - (charFun (μ : Measure ℝ) t).re) := by
  have hcos (s : ℝ) : Integrable (fun x : ℝ => Real.cos (s * x)) (μ : Measure ℝ) :=
    Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with x
      exact Real.abs_cos_le_one (s * x))
  have hexp (s : ℝ) :
      Integrable (fun x : ℝ => Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I))
        (μ : Measure ℝ) :=
    Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with x
      rw [Complex.norm_exp]
      simp)
  have hreal (s : ℝ) :
      (charFun (μ : Measure ℝ) s).re = ∫ x, Real.cos (s * x) ∂(μ : Measure ℝ) := by
    rw [charFun_apply_real]
    have hre := integral_re (hexp s)
    change (∫ x : ℝ, (Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re ∂(μ : Measure ℝ)) =
      (∫ x : ℝ, Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) ∂(μ : Measure ℝ)).re at hre
    calc
      _ = ∫ x : ℝ, (Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re ∂(μ : Measure ℝ) :=
        hre.symm
      _ = _ := by
        congr 1
        funext x
        convert Complex.exp_ofReal_mul_I_re (s * x) using 1 <;> push_cast <;> rfl
  rw [hreal (2 * t), hreal t]
  have hone : (∫ _x : ℝ, (1 : ℝ) ∂(μ : Measure ℝ)) = 1 := by simp
  calc
    1 - ∫ x, Real.cos ((2 * t) * x) ∂(μ : Measure ℝ) =
        ∫ x, (1 - Real.cos ((2 * t) * x)) ∂(μ : Measure ℝ) := by
      rw [integral_sub (integrable_const _) (hcos (2 * t)), hone]
    _ ≤ ∫ x, 4 * (1 - Real.cos (t * x)) ∂(μ : Measure ℝ) := by
      apply integral_mono_ae
      · exact (integrable_const _).sub (hcos (2 * t))
      · exact (Integrable.const_mul ((integrable_const _).sub (hcos t)) 4)
      · filter_upwards with x
        rw [show (2 * t) * x = 2 * (t * x) by ring, Real.cos_two_mul]
        have hc := Real.neg_one_le_cos (t * x)
        have hc' := Real.cos_le_one (t * x)
        nlinarith
    _ = 4 * (1 - ∫ x, Real.cos (t * x) ∂(μ : Measure ℝ)) := by
      rw [integral_const_mul, integral_sub (integrable_const _) (hcos t), hone]

theorem one_sub_normSq_charFun_two_mul_le (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    1 - Complex.normSq (charFun (μ : Measure ℝ) (2 * t)) ≤
      4 * (1 - Complex.normSq (charFun (μ : Measure ℝ) t)) := by
  simpa only [ProbabilityMeasure.charFun_symmetrization, Complex.ofReal_re] using
    one_sub_charFun_re_two_mul_le (ProbabilityMeasure.symmetrization μ) t

theorem normSq_charFun_dyadic_le_of_eq_zero (μ : ProbabilityMeasure ℝ) (t : ℝ)
    (hzero : charFun (μ : Measure ℝ) t = 0) (k : ℕ) :
    Complex.normSq (charFun (μ : Measure ℝ) (t / (2 : ℝ) ^ k)) ≤
      1 - (1 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
      have hineq := one_sub_normSq_charFun_two_mul_le μ
        (t / (2 : ℝ) ^ (k + 1))
      have harg : 2 * (t / (2 : ℝ) ^ (k + 1)) = t / (2 : ℝ) ^ k := by
        rw [pow_succ]
        field_simp
      rw [harg] at hineq
      have hpow : (1 / 4 : ℝ) ^ (k + 1) = (1 / 4 : ℝ) ^ k / 4 := by
        rw [pow_succ]
        ring
      rw [hpow]
      nlinarith

theorem normSq_pow (z : ℂ) (n : ℕ) : Complex.normSq (z ^ n) = Complex.normSq z ^ n := by
  induction n with
  | zero => simp [Complex.normSq_apply]
  | succ n ih => rw [pow_succ, Complex.normSq_mul, ih, pow_succ]

/-- The characteristic function of a real infinitely divisible law never vanishes. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.charFun_ne_zero
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    charFun (μ : Measure ℝ) t ≠ 0 := by
  intro hzero
  have hzeroDyadic (k : ℕ) :
      Complex.normSq (charFun (μ : Measure ℝ) (t / (2 : ℝ) ^ k)) = 0 := by
    let c : ℝ := 1 - (1 / 4 : ℝ) ^ k
    have hc0 : 0 ≤ c := by
      dsimp [c]
      have hpow : (1 / 4 : ℝ) ^ k ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hc1 : c < 1 := by
      dsimp [c]
      have hpos : 0 < (1 / 4 : ℝ) ^ k := pow_pos (by norm_num) k
      linarith
    let A : ℝ := Complex.normSq (charFun (μ : Measure ℝ) (t / (2 : ℝ) ^ k))
    have hAle (n : ℕ) : A ≤ c ^ (n + 1) := by
      obtain ⟨ρ, hρ⟩ := hμ (n + 1) (Nat.succ_pos n)
      have hrootzero : charFun (ρ : Measure ℝ) t = 0 := by
        have hcf := congrArg
          (fun ξ : ProbabilityMeasure ℝ => charFun (ξ : Measure ℝ) t) hρ
        rw [ProbabilityMeasure.charFun_convPow_real] at hcf
        apply (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp
        exact hcf.trans hzero
      have hrootbound := normSq_charFun_dyadic_le_of_eq_zero ρ t hrootzero k
      have hcf := congrArg
        (fun ξ : ProbabilityMeasure ℝ => charFun (ξ : Measure ℝ)
          (t / (2 : ℝ) ^ k)) hρ
      rw [ProbabilityMeasure.charFun_convPow_real] at hcf
      dsimp [A, c]
      rw [← hcf, normSq_pow]
      gcongr
      exact Complex.normSq_nonneg _
    have htend : Tendsto (fun n : ℕ => c ^ (n + 1)) atTop (nhds 0) :=
      (tendsto_add_atTop_iff_nat 1).2
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)
    have hA0 : A ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend hAle
    exact le_antisymm hA0 (Complex.normSq_nonneg _)
  have hcont : Tendsto
      (fun k : ℕ => Complex.normSq (charFun (μ : Measure ℝ) (t / (2 : ℝ) ^ k)))
      atTop (nhds 1) := by
    have harg : Tendsto (fun k : ℕ => t / (2 : ℝ) ^ k) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
          (x := (2 : ℝ)⁻¹) (by norm_num)).const_mul t
    have hchar := (continuous_charFun (μ := (μ : Measure ℝ))).continuousAt.tendsto.comp harg
    have hnorm :=
      Complex.continuous_normSq.continuousAt.tendsto.comp hchar
    simpa [Function.comp_def] using hnorm
  have hconst :
      (fun k : ℕ => Complex.normSq (charFun (μ : Measure ℝ) (t / (2 : ℝ) ^ k))) =
        fun _ => 0 := by
    funext k
    exact hzeroDyadic k
  rw [hconst] at hcont
  have : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hcont
  norm_num at this

section ContinuousExponent

variable (μ : ProbabilityMeasure ℝ)
  (hμ : ∀ t, charFun (μ : Measure ℝ) t ≠ 0)

/-- The nonvanishing characteristic function as a continuous map into `ℂ \ {0}`. -/
noncomputable def nonzeroCharFun : C(ℝ, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨charFun (μ : Measure ℝ) t, hμ t⟩,
    (continuous_charFun (μ := (μ : Measure ℝ))).subtype_mk _⟩

theorem exp_zero_eq_nonzeroCharFun_zero :
    (⟨Complex.exp 0, Complex.exp_ne_zero 0⟩ : {z : ℂ // z ≠ 0}) =
      nonzeroCharFun μ hμ 0 := by
  apply Subtype.ext
  simp [nonzeroCharFun]

/-- The unique continuous characteristic exponent normalized to vanish at zero. -/
noncomputable def continuousExponent : C(ℝ, ℂ) :=
  Classical.choose
    (Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (nonzeroCharFun μ hμ) 0 0 (exp_zero_eq_nonzeroCharFun_zero μ hμ))

theorem continuousExponent_spec :
    continuousExponent μ hμ 0 = 0 ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘
        continuousExponent μ hμ = nonzeroCharFun μ hμ :=
  (Classical.choose_spec
    (Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (nonzeroCharFun μ hμ) 0 0 (exp_zero_eq_nonzeroCharFun_zero μ hμ))).1

@[simp]
theorem continuousExponent_zero : continuousExponent μ hμ 0 = 0 :=
  (continuousExponent_spec μ hμ).1

theorem exp_continuousExponent (t : ℝ) :
    Complex.exp (continuousExponent μ hμ t) = charFun (μ : Measure ℝ) t := by
  have h := congrFun (continuousExponent_spec μ hμ).2 t
  exact congrArg Subtype.val h

theorem continuous_continuousExponent : Continuous (continuousExponent μ hμ) :=
  (continuousExponent μ hμ).continuous

theorem continuousExponent_unique {f : ℝ → ℂ} (hf : Continuous f)
    (hf0 : f 0 = 0) (hexp : ∀ t, Complex.exp (f t) = charFun (μ : Measure ℝ) t) :
    f = continuousExponent μ hμ := by
  let F : C(ℝ, ℂ) := ⟨f, hf⟩
  have hF : F 0 = 0 ∧
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ F =
        nonzeroCharFun μ hμ := by
    refine ⟨hf0, ?_⟩
    funext t
    apply Subtype.ext
    exact hexp t
  exact congrArg DFunLike.coe
    ((Classical.choose_spec
      (Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
        (nonzeroCharFun μ hμ) 0 0 (exp_zero_eq_nonzeroCharFun_zero μ hμ))).2 F hF)

end ContinuousExponent

noncomputable def _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponent
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) : C(ℝ, ℂ) :=
  continuousExponent μ hμ.charFun_ne_zero

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exponent_zero
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) : hμ.exponent 0 = 0 :=
  continuousExponent_zero μ hμ.charFun_ne_zero

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exp_exponent
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Complex.exp (hμ.exponent t) = charFun (μ : Measure ℝ) t :=
  exp_continuousExponent μ hμ.charFun_ne_zero t

/-- A positive convolution root of an infinitely divisible law also has a nonvanishing
characteristic function. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.root_charFun_ne_zero
    {μ ρ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) {n : ℕ} (hn : 0 < n)
    (hρ : ρ.convPow n = μ) (t : ℝ) :
    charFun (ρ : Measure ℝ) t ≠ 0 := by
  intro hzero
  have hcf := congrArg (fun ν : ProbabilityMeasure ℝ => charFun (ν : Measure ℝ) t) hρ
  rw [ProbabilityMeasure.charFun_convPow_real, hzero, zero_pow hn.ne'] at hcf
  exact hμ.charFun_ne_zero t hcf.symm

/-- The normalized continuous exponent of a positive convolution root scales exactly by its
order.  This removes the otherwise possible integer multiples of `2π i`. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.root_exponent_mul
    {μ ρ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) {n : ℕ} (hn : 0 < n)
    (hρ : ρ.convPow n = μ) (t : ℝ) :
    (n : ℂ) * continuousExponent ρ (hμ.root_charFun_ne_zero hn hρ) t = hμ.exponent t := by
  let hρne : ∀ s, charFun (ρ : Measure ℝ) s ≠ 0 := hμ.root_charFun_ne_zero hn hρ
  have hfun : (fun s : ℝ => (n : ℂ) * continuousExponent ρ hρne s) = hμ.exponent := by
    apply continuousExponent_unique μ hμ.charFun_ne_zero
    · fun_prop
    · simp [hρne]
    · intro s
      rw [Complex.exp_nat_mul, exp_continuousExponent]
      rw [← ProbabilityMeasure.charFun_convPow_real, hρ]
  exact congrFun hfun t

/-- Every positive convolution root has the canonical characteristic function obtained by
dividing the continuous characteristic exponent. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.charFun_root
    {μ ρ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) {n : ℕ} (hn : 0 < n)
    (hρ : ρ.convPow n = μ) (t : ℝ) :
    charFun (ρ : Measure ℝ) t = Complex.exp (hμ.exponent t / (n : ℂ)) := by
  let hρne : ∀ s, charFun (ρ : Measure ℝ) s ≠ 0 := hμ.root_charFun_ne_zero hn hρ
  rw [← exp_continuousExponent ρ hρne]
  congr 1
  apply (eq_div_iff (by exact_mod_cast hn.ne')).2
  simpa [mul_comm] using hμ.root_exponent_mul hn hρ t

/-- Positive convolution roots of a real infinitely divisible law are unique. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.root_unique
    {μ ρ σ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) {n : ℕ} (hn : 0 < n)
    (hρ : ρ.convPow n = μ) (hσ : σ.convPow n = μ) : ρ = σ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [hμ.charFun_root hn hρ, hμ.charFun_root hn hσ]

/-- The canonical positive `n`th convolution root, selected from infinite divisibility. -/
noncomputable def _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.nthRoot
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (hn : 0 < n) :
    ProbabilityMeasure ℝ :=
  Classical.choose (hμ n hn)

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.nthRoot_convPow
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (hn : 0 < n) :
    (hμ.nthRoot n hn).convPow n = μ :=
  Classical.choose_spec (hμ n hn)

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.charFun_nthRoot
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (hn : 0 < n)
    (t : ℝ) :
    charFun (hμ.nthRoot n hn : Measure ℝ) t =
      Complex.exp (hμ.exponent t / (n : ℂ)) :=
  hμ.charFun_root hn (hμ.nthRoot_convPow n hn) t

/-- The canonical roots of an infinitely divisible law converge to the trivial
characteristic function uniformly on every compact frequency set.  This is the compact-uniform
part of Exercise 16.1.2. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendstoUniformlyOn_charFun_nthRoot_one
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n t => charFun (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t)
      (fun _ => (1 : ℂ)) atTop K := by
  obtain ⟨C, hCpos, hC⟩ :=
    (hK.image_of_continuousOn hμ.exponent.continuous.continuousOn).isBounded.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hscale : Tendsto (fun n : ℕ => C / (n + 1 : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  have heventually :
      ∀ᶠ n : ℕ in atTop, C / (n + 1 : ℝ) < min 1 (ε / 2) :=
    hscale.eventually (eventually_lt_nhds (lt_min zero_lt_one (half_pos hε)))
  filter_upwards [heventually] with n hn t ht
  rw [hμ.charFun_nthRoot]
  have hexponent : ‖hμ.exponent t‖ ≤ C := hC _ ⟨t, ht, rfl⟩
  have hdenom : ‖((n + 1 : ℕ) : ℂ)‖ = (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have hquot : ‖hμ.exponent t / ((n + 1 : ℕ) : ℂ)‖ ≤ C / (n + 1 : ℝ) := by
    rw [norm_div, hdenom]
    exact div_le_div_of_nonneg_right hexponent (by positivity)
  have hquotOne : ‖hμ.exponent t / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 :=
    hquot.trans (le_of_lt (hn.trans_le (min_le_left _ _)))
  have hexp := Complex.norm_exp_sub_one_le hquotOne
  rw [dist_comm, Complex.dist_eq]
  calc
    ‖Complex.exp (hμ.exponent t / ((n + 1 : ℕ) : ℂ)) - 1‖
        ≤ 2 * ‖hμ.exponent t / ((n + 1 : ℕ) : ℂ)‖ := hexp
    _ ≤ 2 * (C / (n + 1 : ℝ)) := by gcongr
    _ < 2 * (ε / 2) := by
      nlinarith [hn.trans_le (min_le_right _ _)]
    _ = ε := by ring

end ProbabilityTheory
