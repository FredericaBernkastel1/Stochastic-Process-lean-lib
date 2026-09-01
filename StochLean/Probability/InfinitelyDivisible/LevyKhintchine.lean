/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyMeasure
public import StochLean.Probability.InfinitelyDivisible.CompoundPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- Continuous logarithms on the connected real line are unique after fixing their value at one
point.  This is the project-local exponent-first substitute for choosing a global complex
logarithm. -/
theorem continuous_eq_of_exp_eq_of_eq_zero
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hzero : f 0 = g 0) (hexp : ∀ t, Complex.exp (f t) = Complex.exp (g t)) :
    f = g := by
  let S : Set ℝ := {t | f t = g t}
  have hclosed : IsClosed S := isClosed_eq hf hg
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hdiffx : f x - g x = 0 := sub_eq_zero.mpr hx
    have hnear : (fun y ↦ f y - g y) ⁻¹' Metric.ball 0 (2 * Real.pi) ∈ 𝓝 x := by
      apply (hf.sub hg).continuousAt
      simpa [hdiffx] using Metric.ball_mem_nhds (0 : ℂ) Real.two_pi_pos
    apply Filter.mem_of_superset hnear
    intro y hy
    have hyNorm : ‖f y - g y‖ < 2 * Real.pi := by simpa using hy
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp y)
    have hdiff : f y - g y = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hn]
      ring
    by_contra hne
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      simp at hdiff
      exact hne (sub_eq_zero.mp hdiff)
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hnabsInt : (1 : ℤ) ≤ |n| := by
        rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
        · rw [abs_of_neg hnneg]
          omega
        · rw [abs_of_pos hnpos]
          omega
      exact_mod_cast hnabsInt
    have hnorm : 2 * Real.pi ≤ ‖f y - g y‖ := by
      rw [hdiff, norm_mul]
      simp only [Complex.norm_intCast, Complex.norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one]
      norm_num [Real.pi_pos.le]
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    exact (not_le_of_gt hyNorm) hnorm
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hSuniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  funext t
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact ht

/-- Existence form of Levy's continuity theorem.  A pointwise characteristic-function limit that
is continuous at zero is itself the characteristic function of a probability law, and the whole
sequence converges weakly to that law. -/
theorem exists_probabilityMeasure_of_tendsto_charFun
    {μ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : ContinuousAt φ 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) Filter.atTop (nhds (φ t))) :
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (μ₀ : Measure ℝ) t = φ t) ∧
        Tendsto μ Filter.atTop (nhds μ₀) := by
  have htight : IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun hφ h
  have hcompact : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert htight using 1
      ext ν
      constructor
      · rintro ⟨ρ, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨μ n, ⟨n, rfl⟩, rfl⟩)
  obtain ⟨μ₀, -, σ, hσmono, hσ⟩ := hcompact.tendsto_subseq fun n ↦
    subset_closure (Set.mem_range_self n)
  have hchar (t : ℝ) : charFun (μ₀ : Measure ℝ) t = φ t := by
    have hleft := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hσ t
    have hright := (h t).comp hσmono.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  refine ⟨μ₀, hchar, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simpa [hchar t] using h t

/-- First-order exponential approximation in the exact normalization used by deterministic
compound-Poisson approximants. -/
theorem tendsto_nat_mul_cexp_sub_one_div (c : ℂ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      (Complex.exp (c / ((n + 1 : ℕ) : ℂ)) - 1)) atTop (nhds c) := by
  by_cases hc : c = 0
  · subst c
    simp
  · let z : ℕ → ℂ := fun n => c / ((n + 1 : ℕ) : ℂ)
    have hz : Tendsto z atTop (nhds 0) := by
      have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) :
            Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop)
      have hinvR : Tendsto (fun n : ℕ => (((n : ℝ) + 1))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hden
      have hinvC : Tendsto (fun n : ℕ => ((((n : ℝ) + 1))⁻¹ : ℂ)) atTop (nhds 0) :=
        by simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
          Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_zero] using
            Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR
      have hmul : Tendsto (fun n : ℕ => c * ((((n : ℝ) + 1))⁻¹ : ℂ))
          atTop (nhds (c * 0)) := tendsto_const_nhds.mul hinvC
      convert hmul using 1
      · funext n
        simp only [z, div_eq_mul_inv, Complex.ofReal_inv, Nat.cast_add, Nat.cast_one]
        push_cast
        rfl
      · simp
    have hz0 : ∀ n, z n ≠ 0 := by
      intro n
      exact div_ne_zero hc (by exact_mod_cast (Nat.succ_ne_zero n))
    have hzne : Tendsto z atTop (nhdsWithin (0 : ℂ) {0}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hz0⟩
    have hslope : Tendsto (fun n => slope Complex.exp 0 (z n)) atTop (nhds 1) :=
      by simpa only [Function.comp_def, Complex.exp_zero] using
        (Complex.hasDerivAt_exp 0).tendsto_slope.comp hzne
    have hmul : Tendsto (fun n : ℕ => c * slope Complex.exp 0 (z n)) atTop
        (nhds (c * 1)) := tendsto_const_nhds.mul hslope
    convert hmul using 1
    · funext n
      simp only [z, slope, sub_zero, Complex.exp_zero, smul_eq_mul, vsub_eq_sub]
      field_simp
    · simp

/-- Symmetric small jumps converge to the Gaussian quadratic exponent. -/
theorem tendsto_nat_mul_cos_div_sqrt_sub_one (k : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      (Real.cos (k / Real.sqrt ((n : ℝ) + 1)) - 1)) atTop
      (nhds (-(k ^ 2) / 2)) := by
  by_cases hk : k = 0
  · subst k
    simp
  · let q : ℕ → ℝ := fun n => k / (2 * Real.sqrt ((n : ℝ) + 1))
    have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      by simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) :
          Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop)
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hden
    have hq : Tendsto q atTop (nhds 0) := by
      have hi : Tendsto (fun n : ℕ => (2 * Real.sqrt ((n : ℝ) + 1))⁻¹) atTop
          (nhds 0) := by
        simpa only [Function.comp_def] using
          tendsto_inv_atTop_zero.comp (hsqrt.const_mul_atTop zero_lt_two)
      have hm : Tendsto (fun n : ℕ => k * (2 * Real.sqrt ((n : ℝ) + 1))⁻¹) atTop
          (nhds (k * 0)) := tendsto_const_nhds.mul hi
      simpa only [q, div_eq_mul_inv, mul_zero] using hm
    have hq0 : ∀ n, q n ≠ 0 := by
      intro n
      apply div_ne_zero hk
      exact mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity))
    have hqne : Tendsto q atTop (nhdsWithin (0 : ℝ) {0}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr ⟨hq, Filter.Eventually.of_forall hq0⟩
    have hslope : Tendsto (fun n => slope Real.sin 0 (q n)) atTop (nhds 1) := by
      simpa only [Function.comp_def, Real.sin_zero, Real.cos_zero] using
        (Real.hasDerivAt_sin 0).tendsto_slope.comp hqne
    have hsq : Tendsto (fun n => (slope Real.sin 0 (q n)) ^ 2) atTop (nhds (1 ^ 2)) :=
      hslope.pow 2
    have hmul : Tendsto (fun n => (-(k ^ 2) / 2) * (slope Real.sin 0 (q n)) ^ 2)
        atTop (nhds ((-(k ^ 2) / 2) * (1 ^ 2))) := tendsto_const_nhds.mul hsq
    convert hmul using 1
    · funext n
      have htrig : Real.cos (k / Real.sqrt ((n : ℝ) + 1)) - 1 =
          -2 * Real.sin (q n) ^ 2 := by
        have harg : k / Real.sqrt ((n : ℝ) + 1) = 2 * q n := by
          dsimp [q]
          field_simp
        rw [harg, Real.cos_two_mul']
        nlinarith [Real.sin_sq_add_cos_sq (q n)]
      rw [htrig]
      simp only [slope, sub_zero, Real.sin_zero, vsub_eq_sub, smul_eq_mul]
      have hqdef : q n = k / (2 * Real.sqrt ((n : ℝ) + 1)) := rfl
      rw [hqdef]
      field_simp
      have hsqrt_sq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]
      nlinarith
    · norm_num

/-- The fixed source truncation `x 1_{|x|<1}`. -/
noncomputable def levyTruncation (x : ℝ) : ℝ := if |x| < 1 then x else 0

@[simp]
theorem levyTruncation_zero : levyTruncation 0 = 0 := by
  simp [levyTruncation]

theorem levyTruncation_of_abs_lt_one {x : ℝ} (hx : |x| < 1) : levyTruncation x = x := by
  simp [levyTruncation, hx]

theorem levyTruncation_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : levyTruncation x = 0 := by
  simp [levyTruncation, not_lt.mpr hx]

theorem measurable_levyTruncation : Measurable levyTruncation := by
  unfold levyTruncation
  exact Measurable.ite (by measurability) measurable_id measurable_const

/-- The jump part of the real Lévy--Khintchine exponent, under the fixed strict truncation. -/
noncomputable def levyExponentIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
    ((t * levyTruncation x : ℝ) : ℂ) * Complex.I

/-- A simple global domination constant for the Lévy exponent integrand. -/
noncomputable def levyExponentBound (t : ℝ) : ℝ :=
  2 + (3 + |t|) * t ^ 2

theorem measurable_levyExponentIntegrand (t : ℝ) : Measurable (levyExponentIntegrand t) := by
  unfold levyExponentIntegrand
  have htrunc : Measurable levyTruncation := measurable_levyTruncation
  fun_prop

/-- The Lévy exponent integrand is globally dominated by the defining truncated second moment.
The proof uses the quadratic complex-exponential remainder for small jumps and the uniform bound
on the unit circle for large jumps. -/
theorem norm_levyExponentIntegrand_le (t x : ℝ) :
    ‖levyExponentIntegrand t x‖ ≤ levyExponentBound t * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hx]
    have htrunc : levyTruncation x = x := levyTruncation_of_abs_lt_one hx
    rw [levyExponentIntegrand, htrunc]
    by_cases hz : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ≤ 1
    · have hTaylor := Complex.norm_exp_sub_one_sub_id_le hz
      have htx : ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 * x ^ 2 := by
        simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
        rw [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs, sq_abs]
      calc
        ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
            ((t * x : ℝ) : ℂ) * Complex.I‖ ≤
            ‖(((t * x : ℝ) : ℂ) * Complex.I)‖ ^ 2 := hTaylor
        _ = t ^ 2 * x ^ 2 := htx
        _ ≤ levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
    · have hz' : 1 < |t * x| := by
        simpa [abs_mul] using lt_of_not_ge hz
      have hsq : 1 < t ^ 2 * x ^ 2 := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
          _ < |t * x| ^ 2 := (sq_lt_sq₀ zero_le_one (abs_nonneg (t * x))).mpr hz'
          _ = t ^ 2 * x ^ 2 := by rw [abs_mul, mul_pow, sq_abs, sq_abs]
      have hrough :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
              ((t * x : ℝ) : ℂ) * Complex.I‖ ≤ 2 + |t| := by
        calc
          _ ≤ ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ +
              ‖((t * x : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ (1 + 1) + |t * x| := by
            gcongr
            · calc
                ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
                    ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
                  norm_sub_le _ _
                _ = 1 + 1 := by
                  rw [Complex.norm_exp]
                  simp [Complex.mul_re]
            · simp
          _ ≤ 2 + |t| := by
            rw [abs_mul]
            nlinarith [mul_le_mul_of_nonneg_left hx.le (abs_nonneg t)]
      calc
        _ ≤ 2 + |t| := hrough
        _ ≤ (2 + |t|) * (t ^ 2 * x ^ 2) := by
          exact le_mul_of_one_le_right (by positivity) hsq.le
        _ = ((2 + |t|) * t ^ 2) * x ^ 2 := by ring
        _ ≤ levyExponentBound t * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold levyExponentBound
          nlinarith [sq_nonneg t, abs_nonneg t]
  · have hx' : 1 ≤ |x| := le_of_not_gt hx
    rw [levyIntegrand_toReal_of_one_le_abs hx']
    have htrunc : levyTruncation x = 0 := levyTruncation_of_one_le_abs hx'
    rw [levyExponentIntegrand, htrunc]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
    calc
      ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re]
        norm_num
      _ ≤ levyExponentBound t := by
        unfold levyExponentBound
        nlinarith [mul_nonneg (by positivity : 0 ≤ 3 + |t|) (sq_nonneg t)]

/-- The jump integral in the Lévy exponent is well-defined for every real frequency under exactly
the minimal Lévy-measure assumptions. -/
theorem IsLevyMeasure.integrable_levyExponentIntegrand {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) (t : ℝ) : Integrable (levyExponentIntegrand t) ν := by
  have hbase : Integrable (fun x => (levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      hν.lintegral_lt_top.ne
  have hdom : Integrable (fun x => levyExponentBound t * (levyIntegrand x).toReal) ν :=
    hbase.const_mul _
  apply hdom.mono'
  · exact (measurable_levyExponentIntegrand t).aestronglyMeasurable
  · exact ae_of_all _ fun x => norm_levyExponentIntegrand_le t x

/-- The correction forced by transporting the fixed truncation under `x ↦ a*x`. -/
noncomputable def affineDriftIntegrand (a x : ℝ) : ℝ :=
  levyTruncation (a * x) - a * levyTruncation x

theorem measurable_affineDriftIntegrand (a : ℝ) : Measurable (affineDriftIntegrand a) := by
  unfold affineDriftIntegrand
  exact (measurable_levyTruncation.comp (by fun_prop)).sub
    (measurable_const.mul measurable_levyTruncation)

/-- The affine drift correction is controlled by the same minimal Lévy integrand.  In particular,
no finiteness assumption on the whole jump measure is introduced. -/
theorem norm_affineDriftIntegrand_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖affineDriftIntegrand a x‖ ≤ max 1 (a ^ 2) * (levyIntegrand x).toReal := by
  by_cases hx : |x| < 1
  · rw [levyIntegrand_toReal_of_abs_lt_one hx]
    rw [affineDriftIntegrand, levyTruncation_of_abs_lt_one hx]
    by_cases hax : |a * x| < 1
    · rw [levyTruncation_of_abs_lt_one hax]
      simp [sq_nonneg]
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hax)]
      simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos ha]
      have hone : 1 ≤ a * |x| := by
        simpa [abs_mul, abs_of_pos ha] using le_of_not_gt hax
      have hself : a * |x| ≤ (a * |x|) ^ 2 := by nlinarith
      have hmain : a * |x| ≤ a ^ 2 * x ^ 2 := by
        calc
          a * |x| ≤ (a * |x|) ^ 2 := hself
          _ = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
      exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x))
  · rw [levyIntegrand_toReal_of_one_le_abs (le_of_not_gt hx)]
    rw [affineDriftIntegrand, levyTruncation_of_one_le_abs (le_of_not_gt hx)]
    simp only [mul_zero, sub_zero, Real.norm_eq_abs]
    by_cases hax : |a * x| < 1
    · rw [levyTruncation_of_abs_lt_one hax]
      simpa using (le_of_lt hax).trans (le_max_left (1 : ℝ) (a ^ 2))
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hax)]
      simp

theorem IsLevyMeasure.integrable_affineDriftIntegrand {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) {a : ℝ} (ha : 0 < a) : Integrable (affineDriftIntegrand a) ν := by
  have hbase : Integrable (fun x => (levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      hν.lintegral_lt_top.ne
  apply (hbase.const_mul (max 1 (a ^ 2))).mono'
  · exact (measurable_affineDriftIntegrand a).aestronglyMeasurable
  · exact ae_of_all _ (norm_affineDriftIntegrand_le ha)

/-- An admissible alternative truncation differs from the fixed strict truncation by a function
dominated by the defining Levy integrand.  This is the natural condition under which changing the
truncation changes only the drift. -/
def IsAdmissibleLevyTruncation (k : ℝ → ℝ) : Prop :=
  Measurable k ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, ‖k x - levyTruncation x‖ ≤ C * (levyIntegrand x).toReal

theorem isAdmissibleLevyTruncation_fixed :
    IsAdmissibleLevyTruncation levyTruncation := by
  refine ⟨measurable_levyTruncation, 0, le_rfl, ?_⟩
  intro x
  simp

theorem IsAdmissibleLevyTruncation.integrable_difference
    {k : ℝ → ℝ} (hk : IsAdmissibleLevyTruncation k)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Integrable (fun x ↦ k x - levyTruncation x) ν := by
  obtain ⟨hkmeas, C, hC, hbound⟩ := hk
  have hbase : Integrable (fun x ↦ (levyIntegrand x).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      hν.lintegral_lt_top.ne
  apply (hbase.const_mul C).mono'
  · exact (hkmeas.sub measurable_levyTruncation).aestronglyMeasurable
  · exact ae_of_all _ hbound

/-- Jump integrand written with an explicit admissible truncation. -/
noncomputable def levyExponentIntegrandWithTruncation (k : ℝ → ℝ) (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
    (((t * k x : ℝ) : ℂ) * Complex.I)

@[simp]
theorem levyExponentIntegrandWithTruncation_fixed (t x : ℝ) :
    levyExponentIntegrandWithTruncation levyTruncation t x = levyExponentIntegrand t x := rfl

/-- A real Lévy triplet under the fixed strict truncation convention. -/
structure LevyTriplet where
  gaussianVariance : ℝ≥0
  drift : ℝ
  jumpMeasure : Measure ℝ
  isLevyMeasure_jumpMeasure : IsLevyMeasure jumpMeasure

namespace LevyTriplet

/-- Drift expressed under an admissible alternative truncation.  The sign is fixed by requiring
the resulting exponent to be identical to the strict-truncation exponent. -/
noncomputable def driftUnderTruncation (η : LevyTriplet) (k : ℝ → ℝ) : ℝ :=
  η.drift + ∫ x, (k x - levyTruncation x) ∂η.jumpMeasure

/-- Levy exponent displayed with an explicit truncation and its corresponding drift. -/
noncomputable def exponentWithTruncation (η : LevyTriplet) (k : ℝ → ℝ) (t : ℝ) : ℂ :=
  -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    (((η.driftUnderTruncation k * t : ℝ) : ℂ) * Complex.I) +
      ∫ x, levyExponentIntegrandWithTruncation k t x ∂η.jumpMeasure

@[simp]
theorem driftUnderTruncation_fixed (η : LevyTriplet) :
    η.driftUnderTruncation levyTruncation = η.drift := by
  simp [driftUnderTruncation]

/-- The real Lévy--Khintchine exponent under the fixed strict truncation convention. -/
noncomputable def exponent (η : LevyTriplet) (t : ℝ) : ℂ :=
  -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    ((η.drift * t : ℝ) : ℂ) * Complex.I +
      ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure

@[simp]
theorem exponentWithTruncation_fixed (η : LevyTriplet) (t : ℝ) :
    η.exponentWithTruncation levyTruncation t = η.exponent t := by
  simp [exponentWithTruncation, exponent]

/-- A triplet represents a real probability law when the characteristic function is the
exponential of its fixed-truncation exponent. -/
def Represents (η : LevyTriplet) (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ t, charFun (μ : Measure ℝ) t = Complex.exp (η.exponent t)

/-- Existence and uniqueness of a representing triplet, separated from the triplet data itself. -/
def HasUniqueLevyTriplet (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃! η : LevyTriplet, η.Represents μ

theorem HasUniqueLevyTriplet.unique {μ : ProbabilityMeasure ℝ}
    (hμ : HasUniqueLevyTriplet μ) {η η' : LevyTriplet}
    (hη : η.Represents μ) (hη' : η'.Represents μ) : η = η' := by
  obtain ⟨canonical, hcanonical, hunique⟩ := hμ
  exact (hunique η hη).trans (hunique η' hη').symm

theorem Represents.charFun_ne_zero {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (h : η.Represents μ) (t : ℝ) : charFun (μ : Measure ℝ) t ≠ 0 := by
  rw [h t]
  exact Complex.exp_ne_zero _

theorem integrable_exponent_jump (η : LevyTriplet) (t : ℝ) :
    Integrable (levyExponentIntegrand t) η.jumpMeasure :=
  η.isLevyMeasure_jumpMeasure.integrable_levyExponentIntegrand t

/-- Continuity of the jump integral.  The proof uses local boundedness of a convergent frequency
sequence and the global truncated-second-moment domination estimate. -/
theorem continuous_exponentJump (η : LevyTriplet) :
    Continuous (fun t : ℝ ↦ ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  rw [continuous_iff_seqContinuous]
  intro u t hut
  let K : ℝ := |t| + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have huNear : ∀ᶠ n in Filter.atTop, dist (u n) t < 1 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hut) 1 zero_lt_one
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have huK : ∀ᶠ n in Filter.atTop, |u n| ≤ K := by
    filter_upwards [huNear] with n hn
    have hdiff : |u n - t| < 1 := by simpa [Real.dist_eq] using hn
    calc
      |u n| = |(u n - t) + t| := by ring_nf
      _ ≤ |u n - t| + |t| := abs_add_le _ _
      _ ≤ K := by dsimp [K]; linarith
  let C : ℝ := levyExponentBound K
  have hbase : Integrable (fun x ↦ (levyIntegrand x).toReal) η.jumpMeasure :=
    integrable_toReal_of_lintegral_ne_top measurable_levyIntegrand.aemeasurable
      η.isLevyMeasure_jumpMeasure.lintegral_lt_top.ne
  apply tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ C * (levyIntegrand x).toReal)
  · exact Filter.Eventually.of_forall fun n ↦
      (measurable_levyExponentIntegrand (u n)).aestronglyMeasurable
  · filter_upwards [huK] with n hn
    exact ae_of_all _ fun x ↦ by
      refine (norm_levyExponentIntegrand_le (u n) x).trans ?_
      apply mul_le_mul_of_nonneg_right _ (ENNReal.toReal_nonneg)
      dsimp [C]
      unfold levyExponentBound
      have hsquare : (u n) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hK).mpr hn
      have hcoef : 3 + |u n| ≤ 3 + K := by linarith
      simpa [abs_of_nonneg hK, add_comm] using
        add_le_add_left (mul_le_mul hcoef hsquare (sq_nonneg _) (by positivity)) 2
  · exact hbase.const_mul C
  · exact ae_of_all _ fun x ↦ by
      have hx : Continuous (fun s : ℝ ↦ levyExponentIntegrand s x) := by
        unfold levyExponentIntegrand
        fun_prop
      exact hx.continuousAt.tendsto.comp hut

theorem continuous_exponent (η : LevyTriplet) : Continuous η.exponent := by
  have hjump := η.continuous_exponentJump
  unfold exponent
  fun_prop

theorem continuous_exp_exponent (η : LevyTriplet) :
    Continuous (fun t ↦ Complex.exp (η.exponent t)) := by
  exact Complex.continuous_exp.comp η.continuous_exponent

/-- Two triplets representing the same law have the same continuous characteristic exponent.
This conclusion precedes the analytic identification of the triplet components. -/
theorem Represents.exponent_eq {η ξ : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) (hξ : ξ.Represents μ) : η.exponent = ξ.exponent := by
  apply continuous_eq_of_exp_eq_of_eq_zero η.continuous_exponent ξ.continuous_exponent
  · simp [exponent, levyExponentIntegrand]
  · intro t
    rw [← hη t, ← hξ t]

noncomputable def secondDifferenceWeight (s x : ℝ) : ℝ≥0 :=
  ‖levyExponentIntegrand s x + levyExponentIntegrand (-s) x‖₊

theorem secondDifferenceWeight_coe (s x : ℝ) :
    (secondDifferenceWeight s x : ℝ) = 2 * (1 - Real.cos (s * x)) := by
  unfold secondDifferenceWeight
  rw [show levyExponentIntegrand s x + levyExponentIntegrand (-s) x =
      ((2 * (Real.cos (s * x) - 1) : ℝ) : ℂ) by
    simp only [levyExponentIntegrand, neg_mul, neg_neg]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg]
    push_cast
    ring]
  simp only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos]
  · ring
  · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.mpr (Real.cos_le_one _))

theorem measurable_secondDifferenceWeight (s : ℝ) : Measurable (secondDifferenceWeight s) := by
  unfold secondDifferenceWeight
  exact (measurable_levyExponentIntegrand s).add
    (measurable_levyExponentIntegrand (-s)) |>.nnnorm

theorem integrable_secondDifferenceWeight (η : LevyTriplet) (s : ℝ) :
    Integrable (fun x => (secondDifferenceWeight s x : ℝ)) η.jumpMeasure := by
  have h := (η.integrable_exponent_jump s).add (η.integrable_exponent_jump (-s))
  exact h.norm

noncomputable def weightedJumpMeasure (η : LevyTriplet) (s : ℝ) : Measure ℝ :=
    η.jumpMeasure.withDensity (fun x => (secondDifferenceWeight s x : ℝ≥0∞))

instance instFiniteWeightedJumpMeasure (η : LevyTriplet) (s : ℝ) :
    IsFiniteMeasure (weightedJumpMeasure η s) := by
  apply IsFiniteMeasure.mk
  simp only [weightedJumpMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simpa [hasFiniteIntegral_iff_norm] using
    (integrable_secondDifferenceWeight η s).hasFiniteIntegral

noncomputable def secondDifferenceMeasure (η : LevyTriplet) (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((η.gaussianVariance : ℝ) * s ^ 2) • Measure.dirac 0 +
    weightedJumpMeasure η s

instance instFiniteSecondDifferenceMeasure (η : LevyTriplet) (s : ℝ) :
    IsFiniteMeasure (secondDifferenceMeasure η s) := by
  apply IsFiniteMeasure.mk
  simp only [secondDifferenceMeasure, Measure.add_apply, Measure.smul_apply,
    MeasurableSet.univ]
  rw [ENNReal.add_lt_top]
  refine ⟨?_, measure_lt_top _ _⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem weighted_probChar_eq_neg_secondDifference (s t x : ℝ) :
    (secondDifferenceWeight s x : ℝ) •
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) =
      -(levyExponentIntegrand (t + s) x + levyExponentIntegrand (t - s) x -
        2 * levyExponentIntegrand t x) := by
  rw [secondDifferenceWeight_coe]
  simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  simp only [levyExponentIntegrand]
  have hplus : ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
      (((t * x : ℝ) : ℂ) * Complex.I) + (((s * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hminus : ((((t - s) * x : ℝ) : ℂ) * Complex.I) =
      (((t * x : ℝ) : ℂ) * Complex.I) + (((-s * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hplus, hminus, Complex.exp_add, Complex.exp_add]
  push_cast
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, neg_mul]
  rw [show -((s : ℂ) * x * Complex.I) = (-((s : ℂ) * x)) * Complex.I by ring,
    Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

theorem charFun_weightedJumpMeasure (η : LevyTriplet) (s t : ℝ) :
    charFun (weightedJumpMeasure η s) t =
      -((∫ x, levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        (∫ x, levyExponentIntegrand (t - s) x ∂η.jumpMeasure) -
        2 * ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  rw [charFun_apply_real, weightedJumpMeasure,
    integral_withDensity_eq_integral_smul (measurable_secondDifferenceWeight s)]
  rw [integral_congr_ae (ae_of_all _ fun x => by
    simpa only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul] using
      weighted_probChar_eq_neg_secondDifference s t x)]
  rw [integral_neg]
  have hp := η.integrable_exponent_jump (t + s)
  have hm := η.integrable_exponent_jump (t - s)
  have ht := η.integrable_exponent_jump t
  congr 1
  have hsub := integral_sub (hp.add hm) (ht.const_mul 2)
  have hadd := integral_add hp hm
  have hadd' : integral η.jumpMeasure
      (levyExponentIntegrand (t + s) + levyExponentIntegrand (t - s)) =
      (∫ x, levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        ∫ x, levyExponentIntegrand (t - s) x ∂η.jumpMeasure := by
    rw [show levyExponentIntegrand (t + s) + levyExponentIntegrand (t - s) =
      (fun x => levyExponentIntegrand (t + s) x +
        levyExponentIntegrand (t - s) x) by rfl]
    exact hadd
  have hmul : (∫ x, 2 * levyExponentIntegrand t x ∂η.jumpMeasure) =
      2 * ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure :=
    integral_const_mul 2 (levyExponentIntegrand t)
  exact hsub.trans (by rw [hadd', hmul])

theorem secondDifference_exponent_eq (η : LevyTriplet) (s t : ℝ) :
    η.exponent (t + s) + η.exponent (t - s) - 2 * η.exponent t =
      -(((η.gaussianVariance : ℝ) * s ^ 2 : ℝ) : ℂ) +
        ((∫ x, levyExponentIntegrand (t + s) x ∂η.jumpMeasure) +
        (∫ x, levyExponentIntegrand (t - s) x ∂η.jumpMeasure) -
        2 * ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure) := by
  simp only [LevyTriplet.exponent]
  push_cast
  ring

theorem charFun_secondDifferenceMeasure (η : LevyTriplet) (s t : ℝ) :
    charFun (secondDifferenceMeasure η s) t =
      -(η.exponent (t + s) + η.exponent (t - s) - 2 * η.exponent t) := by
  have hdirac : Integrable (fun x : ℝ =>
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (Measure.dirac 0) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
      norm_num)
  have hscaled := hdirac.smul_measure
    (c := ENNReal.ofReal ((η.gaussianVariance : ℝ) * s ^ 2)) ENNReal.ofReal_ne_top
  have hweighted : Integrable
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (weightedJumpMeasure η s) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (ae_of_all _ fun x => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
      norm_num)
  rw [secondDifference_exponent_eq, charFun_apply_real,
    secondDifferenceMeasure, integral_add_measure]
  · rw [integral_smul_measure, integral_dirac]
    have hcf : (∫ x, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
        ∂weightedJumpMeasure η s) = charFun (weightedJumpMeasure η s) t := by
      rw [charFun_apply_real]
    rw [hcf, charFun_weightedJumpMeasure]
    simp only [ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)),
      zero_mul, Complex.ofReal_zero, Complex.exp_zero, Complex.real_smul, mul_one]
    push_cast
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    ring
  · exact hscaled
  · exact hweighted

theorem secondDifferenceMeasure_eq_of_exponent_eq {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) (s : ℝ) :
    secondDifferenceMeasure η s = secondDifferenceMeasure ξ s := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_secondDifferenceMeasure, charFun_secondDifferenceMeasure, h]

theorem weightedJumpMeasure_singleton_zero (η : LevyTriplet) (s : ℝ) :
    weightedJumpMeasure η s {0} = 0 := by
  exact withDensity_absolutelyContinuous η.jumpMeasure _
    η.isLevyMeasure_jumpMeasure.atom_zero

theorem secondDifferenceMeasure_singleton_zero (η : LevyTriplet) (s : ℝ) :
    secondDifferenceMeasure η s {0} =
      ENNReal.ofReal ((η.gaussianVariance : ℝ) * s ^ 2) := by
  simp only [secondDifferenceMeasure, Measure.add_apply, Measure.smul_apply,
    MeasurableSet.singleton, Measure.dirac_apply', Set.mem_singleton_iff, true_and,
    weightedJumpMeasure_singleton_zero, add_zero]
  simp

theorem gaussianVariance_eq_of_exponent_eq {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.gaussianVariance = ξ.gaussianVariance := by
  have hm := congrArg (fun m : Measure ℝ => m {0})
    (secondDifferenceMeasure_eq_of_exponent_eq h 1)
  rw [secondDifferenceMeasure_singleton_zero,
    secondDifferenceMeasure_singleton_zero] at hm
  have hm' : ENNReal.ofReal (η.gaussianVariance : ℝ) =
      ENNReal.ofReal (ξ.gaussianVariance : ℝ) := by
    simpa only [one_pow, mul_one] using hm
  apply ENNReal.coe_inj.mp
  calc
    (η.gaussianVariance : ℝ≥0∞) = ENNReal.ofReal (η.gaussianVariance : ℝ) :=
      ENNReal.coe_nnreal_eq _
    _ = ENNReal.ofReal (ξ.gaussianVariance : ℝ) := hm'
    _ = (ξ.gaussianVariance : ℝ≥0∞) := (ENNReal.coe_nnreal_eq _).symm

theorem weightedJumpMeasure_eq_of_exponent_eq {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) (s : ℝ) :
    weightedJumpMeasure η s = weightedJumpMeasure ξ s := by
  have hv := gaussianVariance_eq_of_exponent_eq h
  have hm := secondDifferenceMeasure_eq_of_exponent_eq h s
  ext A hA
  have hmA := congrArg (fun m : Measure ℝ => m A) hm
  simp only [secondDifferenceMeasure, Measure.add_apply, Measure.smul_apply, hA] at hmA
  rw [hv] at hmA
  apply (ENNReal.add_right_inj ?_).mp hmA
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem restrict_eq_of_withDensity_eq {μ ν : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) {S : Set ℝ} (hS : MeasurableSet S)
    (hf_pos : ∀ x ∈ S, f x ≠ 0) (hf_top : ∀ x, f x ≠ ∞)
    (h : μ.withDensity f = ν.withDensity f) :
    μ.restrict S = ν.restrict S := by
  have hr := congrArg (fun m : Measure ℝ => m.restrict S) h
  rw [restrict_withDensity hS, restrict_withDensity hS] at hr
  have hi := congrArg
    (fun m : Measure ℝ => m.withDensity (fun x => (f x)⁻¹)) hr
  have hμzero : ∀ᵐ x ∂μ.restrict S, f x ≠ 0 :=
    (ae_restrict_iff' hS).2 (ae_of_all _ hf_pos)
  have hνzero : ∀ᵐ x ∂ν.restrict S, f x ≠ 0 :=
    (ae_restrict_iff' hS).2 (ae_of_all _ hf_pos)
  have hμtop : ∀ᵐ x ∂μ.restrict S, f x ≠ ∞ := ae_of_all _ hf_top
  have hνtop : ∀ᵐ x ∂ν.restrict S, f x ≠ ∞ := ae_of_all _ hf_top
  rw [withDensity_inv_same hf hμzero hμtop,
    withDensity_inv_same hf hνzero hνtop] at hi
  exact hi

/-- Increasing bounded annuli that exhaust the nonzero real line. -/
def levyIdentificationSet (n : ℕ) : Set ℝ :=
  {x | 0 < |x| ∧ |x| < 2 * Real.pi * (n + 1)}

theorem measurableSet_levyIdentificationSet (n : ℕ) :
    MeasurableSet (levyIdentificationSet n) := by
  unfold levyIdentificationSet
  measurability

theorem monotone_levyIdentificationSet : Monotone levyIdentificationSet := by
  intro n m hnm x hx
  refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  gcongr

theorem iUnion_levyIdentificationSet :
    (⋃ n, levyIdentificationSet n) = {0}ᶜ := by
  ext x
  constructor
  · rintro hx
    simp only [Set.mem_iUnion, levyIdentificationSet] at hx
    obtain ⟨n, hx0, -⟩ := hx
    simpa [abs_pos] using hx0
  · intro hx
    have hx0 : x ≠ 0 := by simpa using hx
    obtain ⟨n, hn⟩ := exists_nat_gt (|x| / (2 * Real.pi))
    simp only [Set.mem_iUnion, levyIdentificationSet]
    refine ⟨n, (abs_pos.mpr hx0), ?_⟩
    have hpi : 0 < 2 * Real.pi := by positivity
    have hn' : |x| < 2 * Real.pi * n := by
      simpa [mul_comm] using (div_lt_iff₀ hpi).mp hn
    have hnm : (n : ℝ) ≤ n + 1 := by norm_num
    exact hn'.trans_le (mul_le_mul_of_nonneg_left hnm hpi.le)

theorem secondDifferenceWeight_ne_zero_on_identificationSet (n : ℕ)
    {x : ℝ} (hx : x ∈ levyIdentificationSet n) :
    secondDifferenceWeight ((n + 1 : ℝ)⁻¹) x ≠ 0 := by
  have hden : 0 < (n + 1 : ℝ) := by positivity
  have hxabs : |x / (n + 1 : ℝ)| < 2 * Real.pi := by
    rw [abs_div, abs_of_pos hden, div_lt_iff₀ hden]
    simpa only [levyIdentificationSet, Set.mem_setOf_eq, mul_assoc] using hx.2
  have hybounds := (abs_lt.mp hxabs)
  have harg : (n + 1 : ℝ)⁻¹ * x = x / (n + 1 : ℝ) := by
    field_simp
  have hcos : Real.cos ((n + 1 : ℝ)⁻¹ * x) ≠ 1 := by
    intro hc
    rw [harg] at hc
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt hybounds.1 hybounds.2).mp hc
    have : x = 0 := by
      apply (div_eq_zero_iff).mp hz |>.resolve_right
      positivity
    exact (abs_pos.mp hx.1) this
  intro hw
  have hw' := congrArg (fun r : ℝ≥0 => (r : ℝ)) hw
  rw [secondDifferenceWeight_coe] at hw'
  norm_num at hw'
  apply hcos
  nlinarith

theorem jumpMeasure_restrict_identificationSet_eq_of_exponent_eq
    {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) (n : ℕ) :
    η.jumpMeasure.restrict (levyIdentificationSet n) =
      ξ.jumpMeasure.restrict (levyIdentificationSet n) := by
  apply restrict_eq_of_withDensity_eq
    (show Measurable (fun x =>
      (secondDifferenceWeight ((n + 1 : ℝ)⁻¹) x : ℝ≥0∞)) by
        exact (measurable_secondDifferenceWeight _).coe_nnreal_ennreal)
    (measurableSet_levyIdentificationSet n)
  · intro x hx
    exact_mod_cast secondDifferenceWeight_ne_zero_on_identificationSet n hx
  · intro x
    exact ENNReal.coe_ne_top
  · exact weightedJumpMeasure_eq_of_exponent_eq h _

theorem jumpMeasure_eq_of_exponent_eq {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.jumpMeasure = ξ.jumpMeasure := by
  apply Measure.ext
  intro A hA
  let B : ℕ → Set ℝ := fun n => A ∩ levyIdentificationSet n
  have hBmono : Monotone B := by
    intro n m hnm x hx
    exact ⟨hx.1, monotone_levyIdentificationSet hnm hx.2⟩
  have hB_eq (n : ℕ) : η.jumpMeasure (B n) = ξ.jumpMeasure (B n) := by
    have hr := congrArg (fun m : Measure ℝ => m A)
      (jumpMeasure_restrict_identificationSet_eq_of_exponent_eq h n)
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA] at hr
    exact hr
  have hη := tendsto_measure_iUnion_atTop (μ := η.jumpMeasure) hBmono
  have hξ := tendsto_measure_iUnion_atTop (μ := ξ.jumpMeasure) hBmono
  have hseq : (η.jumpMeasure ∘ B) = (ξ.jumpMeasure ∘ B) := by
    funext n
    exact hB_eq n
  rw [hseq] at hη
  have hlimit := tendsto_nhds_unique hη hξ
  have hBunion : (⋃ n, B n) = A \ {0} := by
    calc
      (⋃ n, B n) = A ∩ ⋃ n, levyIdentificationSet n := by
        ext x
        simp only [B, Set.mem_iUnion, Set.mem_inter_iff]
        aesop
      _ = A ∩ {0}ᶜ := by rw [iUnion_levyIdentificationSet]
      _ = A \ {0} := rfl
  have hηzero : η.jumpMeasure ({0} : Set ℝ) = 0 :=
    η.isLevyMeasure_jumpMeasure.atom_zero
  have hξzero : ξ.jumpMeasure ({0} : Set ℝ) = 0 :=
    ξ.isLevyMeasure_jumpMeasure.atom_zero
  rw [hBunion, measure_sdiff_null (s := A) hηzero,
    measure_sdiff_null (s := A) hξzero] at hlimit
  exact hlimit

theorem drift_eq_of_exponent_eq {η ξ : LevyTriplet}
    (h : η.exponent = ξ.exponent) : η.drift = ξ.drift := by
  have hv := gaussianVariance_eq_of_exponent_eq h
  have hj := jumpMeasure_eq_of_exponent_eq h
  have ht := congrFun h 1
  simp only [LevyTriplet.exponent] at ht
  rw [hv, hj] at ht
  norm_num at ht
  exact ht

theorem eq_of_exponent_eq {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) : η = ξ := by
  rw [LevyTriplet.mk.injEq]
  exact ⟨gaussianVariance_eq_of_exponent_eq h, drift_eq_of_exponent_eq h,
    jumpMeasure_eq_of_exponent_eq h⟩

theorem Represents.unique {η ξ : LevyTriplet}
    {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ) (hξ : ξ.Represents μ) : η = ξ :=
  eq_of_exponent_eq (hη.exponent_eq hξ)

theorem Represents.hasUniqueLevyTriplet {η : LevyTriplet}
    {μ : ProbabilityMeasure ℝ} (hη : η.Represents μ) : HasUniqueLevyTriplet μ := by
  refine ⟨η, hη, ?_⟩
  intro ξ hξ
  exact (hη.unique hξ).symm

theorem integrable_truncationCorrection (η : LevyTriplet)
    {k : ℝ → ℝ} (hk : IsAdmissibleLevyTruncation k) (t : ℝ) :
    Integrable (fun x ↦ (((t * (k x - levyTruncation x) : ℝ) : ℂ) * Complex.I))
      η.jumpMeasure := by
  exact ((hk.integrable_difference η.isLevyMeasure_jumpMeasure).const_mul t).ofReal.mul_const
    Complex.I

theorem integrable_exponentWithTruncation (η : LevyTriplet)
    {k : ℝ → ℝ} (hk : IsAdmissibleLevyTruncation k) (t : ℝ) :
    Integrable (levyExponentIntegrandWithTruncation k t) η.jumpMeasure := by
  have hfun : levyExponentIntegrandWithTruncation k t = fun x ↦
      levyExponentIntegrand t x -
        (((t * (k x - levyTruncation x) : ℝ) : ℂ) * Complex.I) := by
    funext x
    simp only [levyExponentIntegrandWithTruncation, levyExponentIntegrand]
    push_cast
    ring
  rw [hfun]
  exact (η.integrable_exponent_jump t).sub (η.integrable_truncationCorrection hk t)

/-- Integral form of the truncation correction. -/
theorem integral_exponentWithTruncation (η : LevyTriplet)
    {k : ℝ → ℝ} (hk : IsAdmissibleLevyTruncation k) (t : ℝ) :
    ∫ x, levyExponentIntegrandWithTruncation k t x ∂η.jumpMeasure =
      ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure -
        (((t * (∫ x, (k x - levyTruncation x) ∂η.jumpMeasure) : ℝ) : ℂ) *
          Complex.I) := by
  have hfixed := η.integrable_exponent_jump t
  have hcorrection := η.integrable_truncationCorrection hk t
  rw [show levyExponentIntegrandWithTruncation k t = fun x ↦
      levyExponentIntegrand t x -
        (((t * (k x - levyTruncation x) : ℝ) : ℂ) * Complex.I) by
      funext x
      simp only [levyExponentIntegrandWithTruncation, levyExponentIntegrand]
      push_cast
      ring]
  rw [integral_sub hfixed hcorrection, integral_mul_const, integral_complex_ofReal,
    integral_const_mul]

/-- Changing to any admissible truncation and applying the corresponding drift correction leaves
the Levy exponent unchanged.  This is the public fixed-convention form of Remark 16.18. -/
theorem exponentWithTruncation_eq (η : LevyTriplet)
    {k : ℝ → ℝ} (hk : IsAdmissibleLevyTruncation k) (t : ℝ) :
    η.exponentWithTruncation k t = η.exponent t := by
  rw [exponentWithTruncation, exponent, driftUnderTruncation,
    η.integral_exponentWithTruncation hk t]
  push_cast
  ring

@[simp]
theorem exponent_zero (η : LevyTriplet) : η.exponent 0 = 0 := by
  simp [exponent, levyExponentIntegrand]

/-- The zero triplet. -/
noncomputable def zero : LevyTriplet where
  gaussianVariance := 0
  drift := 0
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_zeroTriplet (t : ℝ) : zero.exponent t = 0 := by
  simp [zero, exponent]

/-- The canonical triplet of a Dirac law under the fixed truncation. -/
noncomputable def pointMass (x : ℝ) : LevyTriplet where
  gaussianVariance := 0
  drift := x
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_pointMass (x t : ℝ) : (pointMass x).exponent t =
    ((x * t : ℝ) : ℂ) * Complex.I := by
  simp [pointMass, exponent]

theorem represents_pointMass (x : ℝ) :
    (pointMass x).Represents (ProbabilityMeasure.pointMass x) := by
  intro t
  rw [ProbabilityMeasure.coe_pointMass, charFun_dirac, exponent_pointMass]
  congr 1
  rw [Real.inner_apply]

/-- The canonical probability-measure wrapper around Mathlib's real Gaussian law. -/
noncomputable def gaussianLaw (m : ℝ) (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal m v, inferInstance⟩

@[simp, norm_cast]
theorem coe_gaussianLaw (m : ℝ) (v : ℝ≥0) :
    ((gaussianLaw m v : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal m v := rfl

/-- The no-jump Gaussian triplet. -/
noncomputable def gaussian (m : ℝ) (v : ℝ≥0) : LevyTriplet where
  gaussianVariance := v
  drift := m
  jumpMeasure := 0
  isLevyMeasure_jumpMeasure := by simp [IsLevyMeasure]

@[simp]
theorem exponent_gaussian (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (gaussian m v).exponent t =
      -((((v : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) + ((m * t : ℝ) : ℂ) * Complex.I := by
  simp [gaussian, exponent]

theorem gaussian_represents_gaussianLaw (m : ℝ) (v : ℝ≥0) :
    (gaussian m v).Represents (gaussianLaw m v) := by
  intro t
  rw [coe_gaussianLaw, charFun_gaussianReal, exponent_gaussian]
  congr 1
  push_cast
  ring

/-- Addition of independent Lévy triplets. -/
noncomputable def add (η ξ : LevyTriplet) : LevyTriplet where
  gaussianVariance := η.gaussianVariance + ξ.gaussianVariance
  drift := η.drift + ξ.drift
  jumpMeasure := η.jumpMeasure + ξ.jumpMeasure
  isLevyMeasure_jumpMeasure :=
    η.isLevyMeasure_jumpMeasure.add ξ.isLevyMeasure_jumpMeasure

@[simp]
theorem exponent_add (η ξ : LevyTriplet) (t : ℝ) :
    (η.add ξ).exponent t = η.exponent t + ξ.exponent t := by
  simp only [exponent, add, NNReal.coe_add]
  rw [integral_add_measure (η.integrable_exponent_jump t) (ξ.integrable_exponent_jump t)]
  push_cast
  ring

theorem Represents.add {η ξ : LevyTriplet} {μ ν : ProbabilityMeasure ℝ}
    (hη : η.Represents μ) (hξ : ξ.Represents ν) :
    (η.add ξ).Represents (ProbabilityMeasure.conv μ ν) := by
  intro t
  rw [ProbabilityMeasure.coe_conv, charFun_conv, hη t, hξ t, exponent_add,
    Complex.exp_add]

/-- Nonnegative-real scaling of all triplet components. -/
noncomputable def nnrealSMul (r : ℝ≥0) (η : LevyTriplet) : LevyTriplet where
  gaussianVariance := r * η.gaussianVariance
  drift := (r : ℝ) * η.drift
  jumpMeasure := r • η.jumpMeasure
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.smul r

@[simp]
theorem exponent_nnrealSMul (r : ℝ≥0) (η : LevyTriplet) (t : ℝ) :
    (η.nnrealSMul r).exponent t = (r : ℂ) * η.exponent t := by
  simp only [exponent, nnrealSMul, NNReal.coe_mul,
    MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [Complex.real_smul]
  push_cast
  ring

@[simp]
theorem nnrealSMul_zero (η : LevyTriplet) : η.nnrealSMul 0 = zero := by
  cases η
  simp [nnrealSMul, zero]

@[simp]
theorem nnrealSMul_one (η : LevyTriplet) : η.nnrealSMul 1 = η := by
  cases η
  simp [nnrealSMul]

theorem nnrealSMul_add (r s : ℝ≥0) (η : LevyTriplet) :
    η.nnrealSMul (r + s) = (η.nnrealSMul r).add (η.nnrealSMul s) := by
  cases η
  simp [nnrealSMul, add, add_smul, add_mul]

/-- Convolution-power scaling of triplet data. -/
noncomputable def nsmul (n : ℕ) (η : LevyTriplet) : LevyTriplet where
  gaussianVariance := n • η.gaussianVariance
  drift := n • η.drift
  jumpMeasure := (n : ℝ≥0) • η.jumpMeasure
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.smul n

@[simp]
theorem nsmul_gaussianVariance (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).gaussianVariance = n • η.gaussianVariance := rfl

@[simp]
theorem nsmul_drift (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).drift = n • η.drift := rfl

@[simp]
theorem nsmul_jumpMeasure (n : ℕ) (η : LevyTriplet) :
    (η.nsmul n).jumpMeasure = (n : ℝ≥0) • η.jumpMeasure := rfl

/-- Convolution-power scaling multiplies the full Lévy exponent by the same natural number. -/
theorem exponent_nsmul (n : ℕ) (η : LevyTriplet) (t : ℝ) :
    (η.nsmul n).exponent t = (n : ℂ) * η.exponent t := by
  simp only [exponent, nsmul_gaussianVariance, nsmul_drift, nsmul_jumpMeasure,
    MeasureTheory.integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem Represents.nsmul {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (h : η.Represents μ) (n : ℕ) :
    (η.nsmul n).Represents (ProbabilityMeasure.convPow μ n) := by
  intro t
  rw [CompoundPoisson.charFun_convPow, h t, exponent_nsmul, ← Complex.exp_nat_mul]

/-- The canonical triplet of the positive affine image `a*X+d` under the fixed strict
truncation.  The integral term is essential: omitting it changes the characteristic exponent. -/
noncomputable def affine (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) : LevyTriplet where
  gaussianVariance := (Real.toNNReal a) ^ 2 * η.gaussianVariance
  drift := a * η.drift + d + ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure
  jumpMeasure := η.jumpMeasure.map (fun x => a * x)
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.map_mul ha.ne'

@[simp]
theorem affine_gaussianVariance (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).gaussianVariance =
      (Real.toNNReal a) ^ 2 * η.gaussianVariance := rfl

@[simp]
theorem affine_drift (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).drift =
      a * η.drift + d + ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure := rfl

@[simp]
theorem affine_jumpMeasure (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).jumpMeasure = η.jumpMeasure.map (fun x => a * x) := rfl

theorem levyExponentIntegrand_mul (a t x : ℝ) :
    levyExponentIntegrand t (a * x) = levyExponentIntegrand (a * t) x -
      (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I) := by
  unfold levyExponentIntegrand affineDriftIntegrand
  have hexpArg : (((t * (a * x) : ℝ) : ℂ) * Complex.I) =
      ((((a * t) * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexpArg]
  push_cast
  ring

/-- Positive affine transport of a triplet has the expected exponent.  The proof displays the
cancellation between the transported jump truncation and `affineDriftIntegrand`. -/
theorem exponent_affine (η : LevyTriplet) (a d : ℝ) (ha : 0 < a) (t : ℝ) :
    (η.affine a d ha).exponent t =
      η.exponent (a * t) + ((d * t : ℝ) : ℂ) * Complex.I := by
  have hmap :
      (∫ x, levyExponentIntegrand t x ∂(η.jumpMeasure.map fun x => a * x)) =
        ∫ x, levyExponentIntegrand t (a * x) ∂η.jumpMeasure := by
    rw [integral_map (by fun_prop)
      (measurable_levyExponentIntegrand t).aestronglyMeasurable]
  have hcorr := η.isLevyMeasure_jumpMeasure.integrable_affineDriftIntegrand ha
  have hexp := η.isLevyMeasure_jumpMeasure.integrable_levyExponentIntegrand (a * t)
  have hcorrC : Integrable
      (fun x => (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) η.jumpMeasure :=
    ((hcorr.const_mul t).ofReal.mul_const Complex.I)
  have hcast :
      (∫ x, ((t * affineDriftIntegrand a x : ℝ) : ℂ) ∂η.jumpMeasure) =
        ((∫ x, t * affineDriftIntegrand a x ∂η.jumpMeasure : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * affineDriftIntegrand a x ∂η.jumpMeasure) =
        t * ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure :=
    integral_const_mul _ _
  simp only [LevyTriplet.exponent, LevyTriplet.affine]
  rw [hmap]
  rw [show (fun x => levyExponentIntegrand t (a * x)) =
      (fun x => levyExponentIntegrand (a * t) x -
        (((t * affineDriftIntegrand a x : ℝ) : ℂ) * Complex.I)) by
    funext x
    exact levyExponentIntegrand_mul a t x]
  rw [integral_sub hexp hcorrC]
  rw [integral_mul_const, hcast, hreal]
  simp only [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ ha.le]
  simp only [Complex.ofReal_mul]
  push_cast
  ring

end LevyTriplet

namespace CompoundPoisson

/-- The fixed-truncation triplet of a compound Poisson law whose jump law has no atom at zero.
The drift is derived from the truncation convention rather than guessed. -/
noncomputable def triplet (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) : LevyTriplet where
  gaussianVariance := 0
  drift := ∫ x, levyTruncation x ∂(r • (μ : Measure ℝ))
  jumpMeasure := r • (μ : Measure ℝ)
  isLevyMeasure_jumpMeasure := IsLevyMeasure.of_isFiniteMeasure (by
    simp [Measure.smul_apply, hzero])

theorem integrable_levyTruncation (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable levyTruncation ν := by
  apply (integrable_const (1 : ℝ)).mono measurable_levyTruncation.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    by_cases hx : |x| < 1
    · rw [levyTruncation_of_abs_lt_one hx, Real.norm_eq_abs]
      simpa using hx.le
    · rw [levyTruncation_of_one_le_abs (le_of_not_gt hx)]
      simp

/-- Fixed-truncation triplet attached directly to a finite jump-intensity measure.  This entry
point is zero-safe and does not normalize the measure. -/
noncomputable def tripletOfFiniteMeasure (ν : FiniteMeasure ℝ)
    (hzero : (ν : Measure ℝ) {0} = 0) : LevyTriplet where
  gaussianVariance := 0
  drift := ∫ x, levyTruncation x ∂(ν : Measure ℝ)
  jumpMeasure := ν
  isLevyMeasure_jumpMeasure := IsLevyMeasure.of_isFiniteMeasure hzero

theorem tripletOfFiniteMeasure_eq_zero (hzero : ((0 : FiniteMeasure ℝ) : Measure ℝ) {0} = 0) :
    tripletOfFiniteMeasure 0 hzero = LevyTriplet.zero := by
  rw [LevyTriplet.mk.injEq]
  simp [tripletOfFiniteMeasure, LevyTriplet.zero]

theorem normalize_apply_zero_eq_zero {ν : FiniteMeasure ℝ} (hν : ν ≠ 0)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    (ν.normalize : Measure ℝ) {0} = 0 := by
  rw [ν.toMeasure_normalize_eq_of_nonzero hν]
  simp [Measure.smul_apply, hzero]

theorem tripletOfFiniteMeasure_eq_triplet {ν : FiniteMeasure ℝ} (hν : ν ≠ 0)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    tripletOfFiniteMeasure ν hzero =
      triplet ν.mass ν.normalize (normalize_apply_zero_eq_zero hν hzero) := by
  have hmeasure : (ν.mass : ℝ≥0) • (ν.normalize : Measure ℝ) = (ν : Measure ℝ) := by
    have hfinite := congrArg (fun m : FiniteMeasure ℝ ↦ (m : Measure ℝ))
      ν.self_eq_mass_smul_normalize.symm
    simpa using hfinite
  rw [LevyTriplet.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · simp only [tripletOfFiniteMeasure, triplet]
    rw [hmeasure]
  · simpa only [tripletOfFiniteMeasure, triplet] using hmeasure.symm

/-- The compound Poisson triplet has exactly the Poisson characteristic exponent. -/
theorem exponent_triplet (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) (t : ℝ) :
    (triplet r μ hzero).exponent t =
      (r : ℂ) * (charFun (μ : Measure ℝ) t - 1) := by
  have htruncμ : Integrable levyTruncation (μ : Measure ℝ) :=
    integrable_levyTruncation _
  have hlevyμ : Integrable (levyExponentIntegrand t) (μ : Measure ℝ) :=
    (IsLevyMeasure.of_isFiniteMeasure hzero).integrable_levyExponentIntegrand t
  have hcorrμ : Integrable
      (fun x => (((t * levyTruncation x : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) :=
    ((htruncμ.const_mul t).ofReal.mul_const Complex.I)
  have hpoint (x : ℝ) :
      levyExponentIntegrand t x + (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) - 1 := by
    rw [Real.inner_apply]
    unfold levyExponentIntegrand
    have harg : (((t * x : ℝ) : ℂ) * Complex.I) =
        (((x * t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [harg]
    ring
  have hchar : Integrable
      (fun x => Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I)) (μ : Measure ℝ) := by
    apply ((hlevyμ.add hcorrμ).add (integrable_const 1)).congr
    exact ae_of_all _ fun x => by
      change levyExponentIntegrand t x +
          (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) + 1 = _
      rw [hpoint x]
      ring
  have hsum :
      (∫ x, levyExponentIntegrand t x ∂(μ : Measure ℝ)) +
          (∫ x, (((t * levyTruncation x : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) =
        (∫ x, Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) ∂(μ : Measure ℝ)) - 1 := by
    rw [← integral_add hlevyμ hcorrμ]
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    rw [integral_sub hchar (integrable_const 1)]
    simp
  have hcast :
      (∫ x, ((t * levyTruncation x : ℝ) : ℂ) ∂(μ : Measure ℝ)) =
        ((∫ x, t * levyTruncation x ∂(μ : Measure ℝ) : ℝ) : ℂ) :=
    integral_ofReal
  have hreal :
      (∫ x, t * levyTruncation x ∂(μ : Measure ℝ)) =
        t * ∫ x, levyTruncation x ∂(μ : Measure ℝ) :=
    integral_const_mul _ _
  simp only [LevyTriplet.exponent, triplet, NNReal.coe_zero, zero_div, zero_mul,
    Complex.ofReal_zero, neg_zero, zero_add]
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [charFun_apply]
  push_cast
  rw [← hsum]
  rw [integral_mul_const, hcast, hreal]
  push_cast
  simp only [smul_eq_mul]
  rw [Complex.ofReal_mul]
  ring

/-- The exponent associated with a finite jump-intensity measure is the zero-safe compound
Poisson integral.  This formulation avoids normalization and is the approximation interface used
in Theorem 16.5. -/
theorem exponent_tripletOfFiniteMeasure (ν : FiniteMeasure ℝ)
    (hzero : (ν : Measure ℝ) {0} = 0) (t : ℝ) :
    (tripletOfFiniteMeasure ν hzero).exponent t =
      ∫ x, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) - 1 ∂(ν : Measure ℝ) := by
  by_cases hν : ν = 0
  · subst ν
    simp [tripletOfFiniteMeasure_eq_zero, LevyTriplet.exponent_zeroTriplet]
  · rw [tripletOfFiniteMeasure_eq_triplet hν hzero, exponent_triplet]
    rw [charFun_apply, ν.toMeasure_normalize_eq_of_nonzero hν]
    rw [MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, Complex.real_smul]
    have hmass : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
    have hmassR : (ν.mass : ℝ) ≠ 0 := by exact_mod_cast hmass
    have hint : Integrable
        (fun x : ℝ => Complex.exp (((x * t : ℝ) : ℂ) * Complex.I)) (ν : Measure ℝ) := by
      apply (integrable_const (1 : ℂ)).mono (by fun_prop)
      exact ae_of_all _ fun x => by rw [Complex.norm_exp]; simp
    rw [integral_sub hint (integrable_const 1)]
    have hinter :
        (∫ x : ℝ, Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ)) =
          ∫ x : ℝ, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((x * t : ℝ) : ℂ) * Complex.I)
        rw [Real.inner_apply]
    rw [hinter]
    have huniv : ((ν : Measure ℝ) Set.univ).toReal = (ν.mass : ℝ) := by rfl
    rw [integral_const, Measure.real_def, huniv]
    have hcomm :
        (∫ x : ℝ, Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) ∂(ν : Measure ℝ)) =
          ∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂(ν : Measure ℝ) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        congr 1
        push_cast
        ring
    rw [hcomm]
    simp only [NNReal.smul_def, Complex.real_smul, mul_one]
    push_cast
    have hmassC : ((ν.mass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmassR
    field_simp [hmassC]

theorem triplet_represents_law (r : ℝ≥0) (μ : ProbabilityMeasure ℝ)
    (hzero : (μ : Measure ℝ) {0} = 0) :
    (triplet r μ hzero).Represents (law r μ) := by
  intro t
  rw [charFun_law, exponent_triplet]

/-- Every finite jump-intensity measure has its exact compound-Poisson representation, including
the zero measure. -/
theorem tripletOfFiniteMeasure_represents (ν : FiniteMeasure ℝ)
    (hzero : (ν : Measure ℝ) {0} = 0) :
    (tripletOfFiniteMeasure ν hzero).Represents (ofFiniteMeasure ν) := by
  by_cases hν : ν = 0
  · subst ν
    rw [tripletOfFiniteMeasure_eq_zero, ofFiniteMeasure_zero]
    exact LevyTriplet.represents_pointMass 0
  · rw [tripletOfFiniteMeasure_eq_triplet hν hzero,
      ofFiniteMeasure_eq_of_ne_zero hν]
    exact triplet_represents_law ν.mass ν.normalize
      (normalize_apply_zero_eq_zero hν hzero)

end CompoundPoisson

namespace LevyTriplet

/-- The probability law represented by a triplet with finite jump measure: deterministic drift,
Gaussian part, and the zero-safe finite-intensity compound-Poisson part. -/
noncomputable def finiteJumpLaw (η : LevyTriplet) [IsFiniteMeasure η.jumpMeasure] :
    ProbabilityMeasure ℝ :=
  let νf : FiniteMeasure ℝ := ⟨η.jumpMeasure, inferInstance⟩
  ProbabilityMeasure.conv
    (ProbabilityMeasure.conv
      (ProbabilityMeasure.pointMass
        (η.drift - ∫ x, levyTruncation x ∂η.jumpMeasure))
      (gaussianLaw 0 η.gaussianVariance))
    (CompoundPoisson.ofFiniteMeasure νf)

/-- Levy--Khintchine existence for the full finite-jump subclass. -/
theorem represents_finiteJumpLaw (η : LevyTriplet) [IsFiniteMeasure η.jumpMeasure] :
    η.Represents η.finiteJumpLaw := by
  let νf : FiniteMeasure ℝ := ⟨η.jumpMeasure, inferInstance⟩
  have hzero : (νf : Measure ℝ) {0} = 0 := η.isLevyMeasure_jumpMeasure.1
  have hdet := represents_pointMass
    (η.drift - ∫ x, levyTruncation x ∂η.jumpMeasure)
  have hgauss := gaussian_represents_gaussianLaw 0 η.gaussianVariance
  have hjump := CompoundPoisson.tripletOfFiniteMeasure_represents νf hzero
  have hsum := (hdet.add hgauss).add hjump
  have htriplet :
      ((pointMass (η.drift - ∫ x, levyTruncation x ∂η.jumpMeasure)).add
          (gaussian 0 η.gaussianVariance)).add
            (CompoundPoisson.tripletOfFiniteMeasure νf hzero) = η := by
    rw [LevyTriplet.mk.injEq]
    simp [LevyTriplet.add, LevyTriplet.pointMass, LevyTriplet.gaussian,
      CompoundPoisson.tripletOfFiniteMeasure, νf]
  rw [htriplet] at hsum
  change η.Represents
    (ProbabilityMeasure.conv
      (ProbabilityMeasure.conv
        (ProbabilityMeasure.pointMass
          (η.drift - ∫ x, levyTruncation x ∂η.jumpMeasure))
        (gaussianLaw 0 η.gaussianVariance))
      (CompoundPoisson.ofFiniteMeasure νf))
  exact hsum

/-- Finite-jump truncation of a general triplet along the canonical Lévy-measure exhaustion. -/
noncomputable def finiteRestriction (η : LevyTriplet) (n : ℕ) : LevyTriplet where
  gaussianVariance := η.gaussianVariance
  drift := η.drift
  jumpMeasure := η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)
  isLevyMeasure_jumpMeasure := η.isLevyMeasure_jumpMeasure.restrict _

theorem finiteRestriction_jumpMeasure_finite (η : LevyTriplet) (n : ℕ) :
    IsFiniteMeasure (η.finiteRestriction n).jumpMeasure := by
  apply IsFiniteMeasure.mk
  rw [finiteRestriction, Measure.restrict_apply_univ]
  exact η.isLevyMeasure_jumpMeasure.measure_spanningLevel_lt_top n

/-- Canonical finite-jump approximation law of a general triplet. -/
noncomputable def finiteRestrictionLaw (η : LevyTriplet) (n : ℕ) : ProbabilityMeasure ℝ := by
  letI : IsFiniteMeasure (η.finiteRestriction n).jumpMeasure :=
    η.finiteRestriction_jumpMeasure_finite n
  exact (η.finiteRestriction n).finiteJumpLaw

theorem finiteRestriction_represents_finiteRestrictionLaw (η : LevyTriplet) (n : ℕ) :
    (η.finiteRestriction n).Represents (η.finiteRestrictionLaw n) := by
  letI : IsFiniteMeasure (η.finiteRestriction n).jumpMeasure :=
    η.finiteRestriction_jumpMeasure_finite n
  exact represents_finiteJumpLaw (η.finiteRestriction n)

theorem restrict_iUnion_spanningLevel (η : LevyTriplet) :
    η.jumpMeasure.restrict (⋃ n, IsLevyMeasure.spanningLevel n) = η.jumpMeasure := by
  rw [IsLevyMeasure.iUnion_spanningLevel]
  have hsplit := η.jumpMeasure.restrict_compl_add_restrict
    (MeasurableSet.singleton (0 : ℝ))
  rw [Measure.restrict_singleton, η.isLevyMeasure_jumpMeasure.atom_zero] at hsplit
  simpa using hsplit

/-- The finite-jump exponents converge pointwise to the full Lévy exponent. -/
theorem tendsto_exponent_finiteRestriction (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n ↦ (η.finiteRestriction n).exponent t) Filter.atTop
      (nhds (η.exponent t)) := by
  have hint := tendsto_setIntegral_of_monotone
    (fun n ↦ IsLevyMeasure.measurableSet_spanningLevel n)
    IsLevyMeasure.monotone_spanningLevel
    ((η.integrable_exponent_jump t).integrableOn)
  rw [η.restrict_iUnion_spanningLevel] at hint
  let A : ℂ := -((((η.gaussianVariance : ℝ) / 2) * t ^ 2 : ℝ) : ℂ) +
    ((η.drift * t : ℝ) : ℂ) * Complex.I
  have hadd : Tendsto
      (fun n ↦ A + ∫ x in IsLevyMeasure.spanningLevel n,
        levyExponentIntegrand t x ∂η.jumpMeasure) Filter.atTop
      (nhds (A + ∫ x, levyExponentIntegrand t x ∂η.jumpMeasure)) :=
    tendsto_const_nhds.add hint
  simpa only [finiteRestriction, exponent, A] using hadd

/-- Characteristic functions of the finite-jump approximation laws converge to the exponential
of the full triplet exponent. -/
theorem tendsto_charFun_finiteRestrictionLaw (η : LevyTriplet) (t : ℝ) :
    Tendsto (fun n ↦ charFun (η.finiteRestrictionLaw n : Measure ℝ) t) Filter.atTop
      (nhds (Complex.exp (η.exponent t))) := by
  have hexp := Complex.continuous_exp.continuousAt.tendsto.comp
    (η.tendsto_exponent_finiteRestriction t)
  have heq : (fun n ↦ charFun (η.finiteRestrictionLaw n : Measure ℝ) t) =
      (fun n ↦ Complex.exp ((η.finiteRestriction n).exponent t)) := by
    funext n
    exact η.finiteRestriction_represents_finiteRestrictionLaw n t
  rw [heq]
  exact hexp

/-- Lévy--Khintchine existence for every real Lévy triplet, obtained as the weak limit of its
canonical finite-jump approximations. -/
theorem exists_represents (η : LevyTriplet) :
    ∃ μ : ProbabilityMeasure ℝ, η.Represents μ := by
  obtain ⟨μ, hchar, -⟩ := exists_probabilityMeasure_of_tendsto_charFun
    η.continuous_exp_exponent.continuousAt η.tendsto_charFun_finiteRestrictionLaw
  exact ⟨μ, hchar⟩

end LevyTriplet

end ProbabilityTheory
