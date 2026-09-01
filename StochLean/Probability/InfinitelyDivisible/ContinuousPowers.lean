/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Roots
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine
/-!
# Continuous convolution powers of infinitely divisible laws

Canonical roots are raised to rational powers and passed to a weak limit.  The resulting laws have
characteristic function exp(t psi), form a continuous convolution semigroup, and recover the
original law at time one.
-/

@[expose] public section


open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

/-- The lower rational approximation to a nonnegative time used to construct continuous
convolution powers. -/
noncomputable def rationalPowerCoefficient (r : NNReal) (n : ℕ) : ℝ :=
  (⌊(r : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ)

theorem tendsto_rationalPowerCoefficient (r : NNReal) :
    Tendsto (rationalPowerCoefficient r) atTop (nhds (r : ℝ)) := by
  have hindex : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hraw := (tendsto_nat_floor_mul_div_atTop (R := ℝ) r.2).comp hindex
  exact hraw

/-- Rational-time laws made from canonical roots and natural convolution powers. -/
noncomputable def rationalPowerApprox {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsInfinitelyDivisible) (r : NNReal) (n : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.convPow (hμ.nthRoot (n + 1) (Nat.succ_pos n))
    ⌊(r : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊

theorem charFun_rationalPowerApprox {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsInfinitelyDivisible) (r : NNReal) (n : ℕ) (t : ℝ) :
    charFun (rationalPowerApprox hμ r n : Measure ℝ) t =
      Complex.exp ((rationalPowerCoefficient r n : ℂ) * hμ.exponent t) := by
  rw [rationalPowerApprox, ProbabilityMeasure.charFun_convPow_real,
    hμ.charFun_nthRoot, ← Complex.exp_nat_mul]
  congr 1
  simp only [rationalPowerCoefficient, Nat.cast_add, Nat.cast_one]
  push_cast
  field_simp

theorem tendsto_charFun_rationalPowerApprox {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsInfinitelyDivisible) (r : NNReal) (t : ℝ) :
    Tendsto (fun n => charFun (rationalPowerApprox hμ r n : Measure ℝ) t) atTop
      (nhds (Complex.exp ((r : ℂ) * hμ.exponent t))) := by
  rw [show (fun n => charFun (rationalPowerApprox hμ r n : Measure ℝ) t) =
      fun n => Complex.exp ((rationalPowerCoefficient r n : ℂ) * hμ.exponent t) by
    funext n
    exact charFun_rationalPowerApprox hμ r n t]
  apply Complex.continuous_exp.continuousAt.tendsto.comp
  apply Tendsto.mul_const
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_rationalPowerCoefficient r)

theorem exists_positivePower {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsInfinitelyDivisible) (r : NNReal) :
    ∃ ν : ProbabilityMeasure ℝ,
      ∀ t, charFun (ν : Measure ℝ) t = Complex.exp ((r : ℂ) * hμ.exponent t) := by
  obtain ⟨ν, hν, -⟩ := exists_probabilityMeasure_of_tendsto_charFun
    (μ := rationalPowerApprox hμ r)
    (φ := fun t => Complex.exp ((r : ℂ) * hμ.exponent t))
    (by fun_prop)
    (tendsto_charFun_rationalPowerApprox hμ r)
  exact ⟨ν, hν⟩

/-- The canonical convolution power at any nonnegative real time. -/
noncomputable def _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.positivePower
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (r : NNReal) :
    ProbabilityMeasure ℝ :=
  Classical.choose (exists_positivePower hμ r)

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.charFun_positivePower
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (r : NNReal) (t : ℝ) :
    charFun (hμ.positivePower r : Measure ℝ) t =
      Complex.exp ((r : ℂ) * hμ.exponent t) :=
  Classical.choose_spec (exists_positivePower hμ r) t

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.positivePower_zero
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    hμ.positivePower 0 = ProbabilityMeasure.pointMass 0 := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [hμ.charFun_positivePower]
  simp [ProbabilityMeasure.coe_pointMass, charFun_dirac]

@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.positivePower_one
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    hμ.positivePower 1 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [hμ.charFun_positivePower]
  simpa using hμ.exp_exponent t

theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.positivePower_add
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (r s : NNReal) :
    hμ.positivePower (r + s) =
      ProbabilityMeasure.conv (hμ.positivePower r) (hμ.positivePower s) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [ProbabilityMeasure.coe_conv, charFun_conv]
  rw [hμ.charFun_positivePower, hμ.charFun_positivePower, hμ.charFun_positivePower,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Canonical positive powers form a convolution semigroup. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.isConvolutionSemigroup_positivePower
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    IsConvolutionSemigroup hμ.positivePower :=
  hμ.positivePower_add

/-- Canonical positive convolution powers vary weakly continuously in time. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.continuous_positivePower
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    Continuous hμ.positivePower := by
  rw [continuous_iff_seqContinuous]
  intro u r hur
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [Function.comp_apply]
  rw [show (fun n => charFun (hμ.positivePower (u n) : Measure ℝ) t) =
      fun n => Complex.exp (((u n : NNReal) : ℂ) * hμ.exponent t) by
    funext n
    exact hμ.charFun_positivePower (u n) t,
    hμ.charFun_positivePower]
  have hcast : Tendsto (fun n => (((u n : NNReal) : ℝ) : ℂ)) atTop
      (nhds (((r : NNReal) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp hur)
  exact Complex.continuous_exp.continuousAt.tendsto.comp (hcast.mul_const _)

/-- Corollary 16.10: every real infinitely divisible law is the time-one law of a continuous
convolution semigroup. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.isContinuousConvolutionSemigroup
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    IsContinuousConvolutionSemigroup hμ.positivePower := by
  refine ⟨hμ.isConvolutionSemigroup_positivePower, ?_⟩
  simpa [hμ.positivePower_zero] using
    hμ.continuous_positivePower.continuousAt.tendsto.mono_left
      (show nhdsWithin (0 : NNReal) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)

/-! ## Canonical roots tend to the convolution identity -/

/-- The canonical positive `n`th root agrees with the time-`1/n` member of the continuous
convolution-power semigroup. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.nthRoot_eq_positivePower
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (hn : 0 < n) :
    hμ.nthRoot n hn = hμ.positivePower ((1 : NNReal) / n) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [hμ.charFun_nthRoot, hμ.charFun_positivePower]
  congr 1
  push_cast
  ring

/-- Klenke Exercise 16.1.2, weak form: canonical convolution roots converge to `δ₀`. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_nthRoot_zero
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    Tendsto (fun n : ℕ ↦ hμ.nthRoot (n + 1) (Nat.succ_pos n)) atTop
      (𝓝 (ProbabilityMeasure.pointMass 0)) := by
  have h := hμ.isContinuousConvolutionSemigroup.roots_tendsto_zero
    (t := (1 : NNReal)) zero_lt_one
  convert h using 1
  funext n
  simpa only [Nat.cast_add, Nat.cast_one] using
    hμ.nthRoot_eq_positivePower (n + 1) (Nat.succ_pos n)

/-- Pointwise characteristic-function form of the root-to-one limit. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_charFun_nthRoot_one
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ charFun
      (hμ.nthRoot (n + 1) (Nat.succ_pos n) : Measure ℝ) t) atTop (𝓝 1) := by
  have h := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμ.tendsto_nthRoot_zero t
  simpa [ProbabilityMeasure.coe_pointMass, charFun_dirac] using h

end ProbabilityTheory
