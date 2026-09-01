/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyKhintchineConverse
public import StochLean.Probability.InfinitelyDivisible.NonnegativeLevyKhintchine
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# First-order extraction for nonnegative infinitely divisible laws

The real Lévy--Khintchine extraction uses the quadratic weight `1 - sinc x`.  For laws supported
on the nonnegative half-line the natural weight is instead `1 - exp (-x)`: its possible weak-limit
atom at zero is the deterministic part, while division away from zero yields the subordinator
jump measure.  This module develops that construction directly inside StochLean.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

/-- Laplace transform at an arbitrary nonnegative argument. -/
noncomputable def nonnegativeLaplaceAt (t : ℝ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * x)) ∂(μ : Measure ℝ)

theorem integrable_nonnegativeLaplaceAt {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => Real.exp (-(t * x))) (μ : Measure ℝ) := by
  apply (integrable_const (μ := (μ : Measure ℝ)) (1 : ℝ)).mono'
  · fun_prop
  · filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg ht hx))

theorem nonnegativeLaplaceAt_pos {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) :
    0 < nonnegativeLaplaceAt t μ := by
  exact integral_exp_pos (integrable_nonnegativeLaplaceAt hμ ht)

theorem nonnegativeLaplaceAt_le_one {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) :
    nonnegativeLaplaceAt t μ ≤ 1 := by
  rw [show (1 : ℝ) = ∫ _ : ℝ, 1 ∂(μ : Measure ℝ) by simp]
  apply integral_mono_ae (integrable_nonnegativeLaplaceAt hμ ht) (integrable_const 1)
  filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
  exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg ht hx))

@[simp]
theorem nonnegativeLaplaceAt_one (μ : ProbabilityMeasure ℝ) :
    nonnegativeLaplaceAt 1 μ = nonnegativeLaplace μ := by
  rw [nonnegativeLaplaceAt, nonnegativeLaplace]
  congr 1
  funext x
  ring_nf

@[simp]
theorem nonnegativeLaplaceAt_zero (μ : ProbabilityMeasure ℝ) :
    nonnegativeLaplaceAt 0 μ = 1 := by
  simp [nonnegativeLaplaceAt]

theorem nonnegativeLaplaceAt_conv {μ ν : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) (hν : ν.IsNonnegativeLaw)
    {t : ℝ} (ht : 0 ≤ t) :
    nonnegativeLaplaceAt t (μ.conv ν) =
      nonnegativeLaplaceAt t μ * nonnegativeLaplaceAt t ν := by
  rw [nonnegativeLaplaceAt, ProbabilityMeasure.coe_conv,
    integral_conv (integrable_nonnegativeLaplaceAt (hμ.conv hν) ht)]
  simp only [mul_add, neg_add_rev, Real.exp_add, integral_mul_const,
    integral_const_mul]
  simp only [nonnegativeLaplaceAt, mul_comm]

theorem nonnegativeLaplaceAt_convPow {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    nonnegativeLaplaceAt t (μ.convPow n) = nonnegativeLaplaceAt t μ ^ n := by
  induction n with
  | zero =>
      simp [ProbabilityMeasure.convPow, nonnegativeLaplaceAt,
        ProbabilityMeasure.coe_pointMass]
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ,
        nonnegativeLaplaceAt_conv (hμ.convPow n) hμ ht, ih, pow_succ]

/-- Every canonical convolution root of a nonnegative infinitely divisible law is nonnegative. -/
theorem canonicalRoot_isNonnegativeLaw
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) (n : ℕ) (hn : 0 < n) :
    (hID.nthRoot n hn).IsNonnegativeLaw := by
  apply ProbabilityMeasure.IsNonnegativeLaw.of_convPow hn
  rw [hID.nthRoot_convPow]
  exact hμ

/-- The nonnegative Laplace transform of a canonical root is its positive real root. -/
theorem nonnegativeLaplace_canonicalRoot
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) (n : ℕ) (hn : 0 < n) :
    nonnegativeLaplace (hID.nthRoot n hn) =
      nonnegativeLaplace μ ^ ((n : ℝ)⁻¹) := by
  let ρ := hID.nthRoot n hn
  have hρ : ρ.IsNonnegativeLaw := canonicalRoot_isNonnegativeLaw hID hμ n hn
  have hpow := congrArg nonnegativeLaplace (hID.nthRoot_convPow n hn)
  rw [nonnegativeLaplace_convPow hρ n] at hpow
  calc
    nonnegativeLaplace ρ =
        (nonnegativeLaplace ρ ^ n) ^ ((n : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast (nonnegativeLaplace_pos hρ).le hn.ne']
    _ = nonnegativeLaplace μ ^ ((n : ℝ)⁻¹) := by rw [hpow]

/-- Canonical-root formula for the whole nonnegative Laplace transform. -/
theorem nonnegativeLaplaceAt_canonicalRoot
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (hn : 0 < n) :
    nonnegativeLaplaceAt t (hID.nthRoot n hn) =
      nonnegativeLaplaceAt t μ ^ ((n : ℝ)⁻¹) := by
  let ρ := hID.nthRoot n hn
  have hρ : ρ.IsNonnegativeLaw := canonicalRoot_isNonnegativeLaw hID hμ n hn
  have hpow := congrArg (nonnegativeLaplaceAt t) (hID.nthRoot_convPow n hn)
  rw [nonnegativeLaplaceAt_convPow hρ ht n] at hpow
  calc
    nonnegativeLaplaceAt t ρ =
        (nonnegativeLaplaceAt t ρ ^ n) ^ ((n : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast (nonnegativeLaplaceAt_pos hρ ht).le hn.ne']
    _ = nonnegativeLaplaceAt t μ ^ ((n : ℝ)⁻¹) := by rw [hpow]

/-- First-order canonical-root Laplace asymptotics at any nonnegative argument. -/
theorem tendsto_firstOrderRootMassAt
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) *
      (1 - nonnegativeLaplaceAt t
        (hID.nthRoot (n + 1) (Nat.succ_pos n))))
      atTop (𝓝 (-Real.log (nonnegativeLaplaceAt t μ))) := by
  have hL : 0 < nonnegativeLaplaceAt t μ := nonnegativeLaplaceAt_pos hμ ht
  have hp : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      exact tendsto_inv_atTop_zero.comp htop
    · filter_upwards [] with n
      exact Set.mem_Ioi.mpr (by positivity)
  have hlog := (tendsto_rpow_sub_one_log hL).comp hp
  have hneg := hlog.neg
  convert hneg using 1
  funext n
  rw [nonnegativeLaplaceAt_canonicalRoot hID hμ ht (n + 1) (Nat.succ_pos n)]
  simp only [Function.comp_apply]
  rw [inv_inv]
  push_cast
  ring

/-- The total first-order root intensity converges to the log-Laplace exponent at one. -/
theorem tendsto_firstOrderRootMass
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) *
      (1 - nonnegativeLaplace (hID.nthRoot (n + 1) (Nat.succ_pos n))))
      atTop (𝓝 (-Real.log (nonnegativeLaplace μ))) := by
  have hL : 0 < nonnegativeLaplace μ := nonnegativeLaplace_pos hμ
  have hp : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop
      (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have htop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      exact tendsto_inv_atTop_zero.comp htop
    · filter_upwards [] with n
      exact Set.mem_Ioi.mpr (by positivity)
  have hlog := (tendsto_rpow_sub_one_log hL).comp hp
  have hneg := hlog.neg
  convert hneg using 1
  funext n
  rw [nonnegativeLaplace_canonicalRoot hID hμ (n + 1) (Nat.succ_pos n)]
  simp only [Function.comp_apply]
  rw [inv_inv]
  push_cast
  ring

/-! ## First-order weighted root measures -/

/-- The first-order nonnegative extraction weight, extended by zero on the negative half-line. -/
noncomputable def nonnegativeExtractionWeight (x : ℝ) : NNReal :=
  Real.toNNReal (1 - Real.exp (-x))

theorem continuous_nonnegativeExtractionWeight : Continuous nonnegativeExtractionWeight := by
  unfold nonnegativeExtractionWeight
  fun_prop

theorem measurable_nonnegativeExtractionWeight : Measurable nonnegativeExtractionWeight :=
  continuous_nonnegativeExtractionWeight.measurable

@[simp]
theorem nonnegativeExtractionWeight_zero : nonnegativeExtractionWeight 0 = 0 := by
  simp [nonnegativeExtractionWeight]

theorem coe_nonnegativeExtractionWeight_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (nonnegativeExtractionWeight x : ℝ) = 1 - Real.exp (-x) := by
  rw [nonnegativeExtractionWeight, Real.coe_toNNReal]
  exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 (neg_nonpos.mpr hx))

theorem nonnegativeExtractionWeight_le_one (x : ℝ) :
    nonnegativeExtractionWeight x ≤ 1 := by
  simpa [nonnegativeExtractionWeight] using
    Real.toNNReal_le_toNNReal (show 1 - Real.exp (-x) ≤ 1 by
      linarith [Real.exp_pos (-x)])

/-! ## Bounded continuous first-order Laplace quotients -/

noncomputable def nonnegativeLaplaceRatioNum (t x : ℝ) : ℝ :=
  1 - Real.exp (-(t * x))

noncomputable def nonnegativeLaplaceRatioDen (x : ℝ) : ℝ :=
  1 - Real.exp (-x)

private theorem hasDerivAt_nonnegativeLaplaceRatioNum (t x : ℝ) :
    HasDerivAt (nonnegativeLaplaceRatioNum t)
      (t * Real.exp (-(t * x))) x := by
  have hinner : HasDerivAt (fun y : ℝ => -(t * y)) (-t) x := by
    convert ((hasDerivAt_id x).const_mul t).neg using 1
    all_goals first | rfl | ring
  have hexp := (Real.hasDerivAt_exp (-(t * x))).comp x hinner
  unfold nonnegativeLaplaceRatioNum
  convert (hasDerivAt_const x 1).sub hexp using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_nonnegativeLaplaceRatioDen (x : ℝ) :
    HasDerivAt nonnegativeLaplaceRatioDen (Real.exp (-x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hexp := (Real.hasDerivAt_exp (-x)).comp x hinner
  unfold nonnegativeLaplaceRatioDen
  convert (hasDerivAt_const x 1).sub hexp using 1
  all_goals first | rfl | ring

private theorem tendsto_nonnegativeLaplaceQuotient (t : ℝ) :
    Tendsto (fun x => nonnegativeLaplaceRatioNum t x /
      nonnegativeLaplaceRatioDen x) (𝓝[≠] 0) (𝓝 t) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact Filter.Eventually.of_forall fun x =>
      hasDerivAt_nonnegativeLaplaceRatioNum t x
  · exact Filter.Eventually.of_forall hasDerivAt_nonnegativeLaplaceRatioDen
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos (-x)).ne'
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeLaplaceRatioNum] using
        (hasDerivAt_nonnegativeLaplaceRatioNum t 0).continuousAt.tendsto)
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeLaplaceRatioDen] using
        (hasDerivAt_nonnegativeLaplaceRatioDen 0).continuousAt.tendsto)
  · have hc : ContinuousAt
        (fun x : ℝ => t * Real.exp (-(t * x)) / Real.exp (-x)) 0 := by
      apply ContinuousAt.div₀
      · fun_prop
      · fun_prop
      · simp
    simpa using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

/-- The quotient `(1-exp(-t*x))/(1-exp(-x))`, continuously extended by `t` at zero. -/
noncomputable def nonnegativeLaplaceRatio (t x : ℝ) : ℝ :=
  if x = 0 then t
  else nonnegativeLaplaceRatioNum t x / nonnegativeLaplaceRatioDen x

theorem continuous_nonnegativeLaplaceRatio (t : ℝ) :
    Continuous (nonnegativeLaplaceRatio t) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [show nonnegativeLaplaceRatio t = Function.update
        (fun y => nonnegativeLaplaceRatioNum t y / nonnegativeLaplaceRatioDen y) 0 t by
      funext y
      simp [nonnegativeLaplaceRatio, Function.update_apply]]
    rw [continuousAt_update_same]
    exact tendsto_nonnegativeLaplaceQuotient t
  · have hden : nonnegativeLaplaceRatioDen x ≠ 0 := by
      intro h
      have he : Real.exp (-x) = 1 := by
        simpa [nonnegativeLaplaceRatioDen] using (sub_eq_zero.mp h).symm
      have hx' : -x = 0 := Real.exp_injective (by simpa using he)
      exact hx (by linarith)
    have hlocal : nonnegativeLaplaceRatio t =ᶠ[𝓝 x]
        fun y => nonnegativeLaplaceRatioNum t y / nonnegativeLaplaceRatioDen y := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [nonnegativeLaplaceRatio, hy]
    have hnumc : ContinuousAt (nonnegativeLaplaceRatioNum t) x := by
      unfold nonnegativeLaplaceRatioNum
      fun_prop
    have hdenc : ContinuousAt nonnegativeLaplaceRatioDen x := by
      unfold nonnegativeLaplaceRatioDen
      fun_prop
    apply (hnumc.div₀ hdenc hden).congr_of_eventuallyEq
    exact hlocal

theorem nonnegativeLaplaceRatio_nonneg {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    0 ≤ nonnegativeLaplaceRatio t x := by
  by_cases hx0 : x = 0
  · simp [nonnegativeLaplaceRatio, hx0, ht]
  · rw [nonnegativeLaplaceRatio, if_neg hx0]
    apply div_nonneg
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).2
        (neg_nonpos.mpr (mul_nonneg ht hx)))
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 (neg_nonpos.mpr hx))

theorem nonnegativeLaplaceRatio_le_max {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    nonnegativeLaplaceRatio t x ≤ max t 1 := by
  by_cases hx0 : x = 0
  · subst x
    simp [nonnegativeLaplaceRatio, le_max_left]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hdenpos : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hxpos))
  rw [nonnegativeLaplaceRatio, if_neg hx0]
  unfold nonnegativeLaplaceRatioNum nonnegativeLaplaceRatioDen
  by_cases htone : t ≤ 1
  · have htx : t * x ≤ x := by nlinarith
    have hnum : 1 - Real.exp (-(t * x)) ≤ 1 - Real.exp (-x) := by
      gcongr
    exact (div_le_one hdenpos).2 hnum |>.trans (le_max_right _ _)
  · have hone : 1 ≤ t := le_of_not_ge htone
    have hs : -1 ≤ Real.exp (-x) - 1 := by
      linarith [Real.exp_pos (-x)]
    have hbern := one_add_mul_self_le_rpow_one_add hs hone
    have hrpow : (1 + (Real.exp (-x) - 1)) ^ t = Real.exp (-(t * x)) := by
      rw [show 1 + (Real.exp (-x) - 1) = Real.exp (-x) by ring,
        Real.rpow_def_of_pos (Real.exp_pos (-x)), Real.log_exp]
      congr 1
      ring
    rw [hrpow] at hbern
    have hnum : 1 - Real.exp (-(t * x)) ≤ t * (1 - Real.exp (-x)) := by
      linarith
    exact ((div_le_iff₀ hdenpos).2 hnum).trans (le_max_left _ _)

/-- The nonnegative quotient clamped to `[0,∞)`, hence bounded on the whole real line. -/
noncomputable def nonnegativeLaplaceRatioClamped (t x : ℝ) : ℝ :=
  nonnegativeLaplaceRatio t (max x 0)

theorem continuous_nonnegativeLaplaceRatioClamped (t : ℝ) :
    Continuous (nonnegativeLaplaceRatioClamped t) := by
  exact (continuous_nonnegativeLaplaceRatio t).comp (continuous_id.max continuous_const)

noncomputable def nonnegativeLaplaceRatioBCF (t : ℝ) (ht : 0 ≤ t) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨nonnegativeLaplaceRatioClamped t, continuous_nonnegativeLaplaceRatioClamped t⟩
    (2 * max t 1) fun x y => by
      rw [dist_eq_norm, Real.norm_eq_abs]
      have hx := nonnegativeLaplaceRatio_nonneg ht (le_max_right x 0)
      have hy := nonnegativeLaplaceRatio_nonneg ht (le_max_right y 0)
      have hx' := nonnegativeLaplaceRatio_le_max ht (le_max_right x 0)
      have hy' := nonnegativeLaplaceRatio_le_max ht (le_max_right y 0)
      dsimp [nonnegativeLaplaceRatioClamped]
      rw [abs_sub_le_iff]
      constructor <;> linarith

/-! The corresponding complex quotient recovers the characteristic exponent. -/

private noncomputable def nonnegativeFourierRatioReNum (t x : ℝ) : ℝ :=
  Real.cos (t * x) - 1

private noncomputable def nonnegativeFourierRatioImNum (t x : ℝ) : ℝ :=
  Real.sin (t * x)

private theorem hasDerivAt_nonnegativeFourierRatioReNum (t x : ℝ) :
    HasDerivAt (nonnegativeFourierRatioReNum t)
      (-t * Real.sin (t * x)) x := by
  unfold nonnegativeFourierRatioReNum
  convert (((Real.hasDerivAt_cos (t * x)).comp x
    ((hasDerivAt_id x).const_mul t)).sub_const 1) using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_nonnegativeFourierRatioImNum (t x : ℝ) :
    HasDerivAt (nonnegativeFourierRatioImNum t)
      (t * Real.cos (t * x)) x := by
  unfold nonnegativeFourierRatioImNum
  convert (Real.hasDerivAt_sin (t * x)).comp x
    ((hasDerivAt_id x).const_mul t) using 1
  all_goals first | rfl | ring

private theorem tendsto_nonnegativeFourierRatioRe (t : ℝ) :
    Tendsto (fun x => nonnegativeFourierRatioReNum t x /
      nonnegativeLaplaceRatioDen x) (𝓝[≠] 0) (𝓝 0) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact Filter.Eventually.of_forall fun x =>
      hasDerivAt_nonnegativeFourierRatioReNum t x
  · exact Filter.Eventually.of_forall hasDerivAt_nonnegativeLaplaceRatioDen
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos (-x)).ne'
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeFourierRatioReNum] using
        (hasDerivAt_nonnegativeFourierRatioReNum t 0).continuousAt.tendsto)
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeLaplaceRatioDen] using
        (hasDerivAt_nonnegativeLaplaceRatioDen 0).continuousAt.tendsto)
  · have hc : ContinuousAt
        (fun x : ℝ => (-t * Real.sin (t * x)) / Real.exp (-x)) 0 := by
      apply ContinuousAt.div₀
      · fun_prop
      · fun_prop
      · simp
    simpa using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

private theorem tendsto_nonnegativeFourierRatioIm (t : ℝ) :
    Tendsto (fun x => nonnegativeFourierRatioImNum t x /
      nonnegativeLaplaceRatioDen x) (𝓝[≠] 0) (𝓝 t) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact Filter.Eventually.of_forall fun x =>
      hasDerivAt_nonnegativeFourierRatioImNum t x
  · exact Filter.Eventually.of_forall hasDerivAt_nonnegativeLaplaceRatioDen
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos (-x)).ne'
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeFourierRatioImNum] using
        (hasDerivAt_nonnegativeFourierRatioImNum t 0).continuousAt.tendsto)
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa [nonnegativeLaplaceRatioDen] using
        (hasDerivAt_nonnegativeLaplaceRatioDen 0).continuousAt.tendsto)
  · have hc : ContinuousAt
        (fun x : ℝ => (t * Real.cos (t * x)) / Real.exp (-x)) 0 := by
      apply ContinuousAt.div₀
      · fun_prop
      · fun_prop
      · simp
    simpa using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

private theorem nonnegativeFourierQuotient_eq_re_add_im (t : ℝ)
    {x : ℝ} (_hx : x ≠ 0) :
    LevyTriplet.poissonExponentIntegrand t x /
        nonnegativeLaplaceRatioDen x =
      ((nonnegativeFourierRatioReNum t x /
          nonnegativeLaplaceRatioDen x : ℝ) : ℂ) +
        ((nonnegativeFourierRatioImNum t x /
          nonnegativeLaplaceRatioDen x : ℝ) : ℂ) * Complex.I := by
  rw [LevyTriplet.poissonExponentIntegrand, Complex.exp_ofReal_mul_I]
  simp only [nonnegativeFourierRatioReNum, nonnegativeFourierRatioImNum,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]
  ring

noncomputable def nonnegativeFourierRatio (t x : ℝ) : ℂ :=
  if x = 0 then (t : ℂ) * Complex.I
  else LevyTriplet.poissonExponentIntegrand t x /
    nonnegativeLaplaceRatioDen x

theorem continuous_nonnegativeFourierRatio (t : ℝ) :
    Continuous (nonnegativeFourierRatio t) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [show nonnegativeFourierRatio t = Function.update
        (fun y => LevyTriplet.poissonExponentIntegrand t y /
          nonnegativeLaplaceRatioDen y) 0 ((t : ℂ) * Complex.I) by
      funext y
      simp [nonnegativeFourierRatio, Function.update_apply]]
    rw [continuousAt_update_same]
    have hlim :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_nonnegativeFourierRatioRe t)).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_nonnegativeFourierRatioIm t)).mul_const Complex.I)
    have hlim' : Tendsto
        (fun x => ((nonnegativeFourierRatioReNum t x /
            nonnegativeLaplaceRatioDen x : ℝ) : ℂ) +
          ((nonnegativeFourierRatioImNum t x /
            nonnegativeLaplaceRatioDen x : ℝ) : ℂ) * Complex.I)
        (𝓝[≠] 0) (𝓝 ((t : ℂ) * Complex.I)) := by
      simpa only [Function.comp_apply, Complex.ofReal_zero, zero_add] using hlim
    apply Tendsto.congr' _ hlim'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (nonnegativeFourierQuotient_eq_re_add_im t (by simpa using hy)).symm
  · have hden : nonnegativeLaplaceRatioDen x ≠ 0 := by
      intro h
      have he : Real.exp (-x) = 1 := by
        simpa [nonnegativeLaplaceRatioDen] using (sub_eq_zero.mp h).symm
      have hx' : -x = 0 := Real.exp_injective (by simpa using he)
      exact hx (by linarith)
    have hlocal : nonnegativeFourierRatio t =ᶠ[𝓝 x]
        fun y => LevyTriplet.poissonExponentIntegrand t y /
          nonnegativeLaplaceRatioDen y := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [nonnegativeFourierRatio, hy]
    have hn : ContinuousAt (LevyTriplet.poissonExponentIntegrand t) x := by
      unfold LevyTriplet.poissonExponentIntegrand
      fun_prop
    have hd : ContinuousAt nonnegativeLaplaceRatioDen x := by
      unfold nonnegativeLaplaceRatioDen
      fun_prop
    have hdC : ContinuousAt (fun y => (nonnegativeLaplaceRatioDen y : ℂ)) x := by
      fun_prop
    exact (hn.div₀ hdC (Complex.ofReal_ne_zero.mpr hden)).congr_of_eventuallyEq
      hlocal

/-- The complex quotient, clamped to the nonnegative half-line. -/
noncomputable def nonnegativeFourierRatioClamped (t x : ℝ) : ℂ :=
  nonnegativeFourierRatio t (max x 0)

theorem continuous_nonnegativeFourierRatioClamped (t : ℝ) :
    Continuous (nonnegativeFourierRatioClamped t) := by
  exact (continuous_nonnegativeFourierRatio t).comp
    (continuous_id.max continuous_const)

/-- A uniform bound for the Fourier quotient on `[0,∞)`. -/
theorem norm_nonnegativeFourierRatio_le {t x : ℝ} (hx : 0 ≤ x) :
    ‖nonnegativeFourierRatio t x‖ ≤ max (3 * |t|) 4 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [nonnegativeFourierRatio, if_pos, Complex.norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact (show |t| ≤ 3 * |t| by nlinarith [abs_nonneg t]).trans
      (le_max_left _ _)
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hdenpos : 0 < nonnegativeLaplaceRatioDen x := by
    unfold nonnegativeLaplaceRatioDen
    exact sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hxpos))
  rw [nonnegativeFourierRatio, if_neg hx0, norm_div]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenpos]
  by_cases hxone : x ≤ 1
  · have hnum : ‖LevyTriplet.poissonExponentIntegrand t x‖ ≤ |t * x| := by
      unfold LevyTriplet.poissonExponentIntegrand
      simpa only [mul_comm, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * x))
    have hw : x ≤ 3 * nonnegativeLaplaceRatioDen x := by
      have hprod := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x)
        (Real.exp_pos (-x)).le
      have hprod' : x * Real.exp (-x) + Real.exp (-x) ≤ 1 := by
        calc
          x * Real.exp (-x) + Real.exp (-x) =
              (x + 1) * Real.exp (-x) := by ring
          _ ≤ Real.exp x * Real.exp (-x) := hprod
          _ = 1 := by rw [← Real.exp_add]; norm_num
      have he3 : Real.exp 1 < 3 := by
        have he := Real.exp_bound' (x := (1 : ℝ)) zero_le_one le_rfl
          (n := 3) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at he
        linarith
      have hthird : (1 / 3 : ℝ) < Real.exp (-1) := by
        rw [Real.exp_neg]
        simpa only [one_div] using
          one_div_lt_one_div_of_lt (Real.exp_pos 1) he3
      have hmono : Real.exp (-1) ≤ Real.exp (-x) :=
        Real.exp_le_exp.mpr (neg_le_neg hxone)
      unfold nonnegativeLaplaceRatioDen
      nlinarith [hthird.trans_le hmono]
    have htx : |t * x| = |t| * x := by
      rw [abs_mul, abs_of_nonneg hx]
    calc
      ‖LevyTriplet.poissonExponentIntegrand t x‖ /
          nonnegativeLaplaceRatioDen x ≤ |t * x| /
          nonnegativeLaplaceRatioDen x :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ = |t| * x / nonnegativeLaplaceRatioDen x := by rw [htx]
      _ ≤ 3 * |t| := by
        rw [mul_div_assoc, show 3 * |t| = |t| * 3 by ring]
        exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hdenpos).2 hw)
          (abs_nonneg t)
      _ ≤ max (3 * |t|) 4 := le_max_left _ _
  · have hone : 1 < x := lt_of_not_ge hxone
    have hhalf : (1 / 2 : ℝ) < nonnegativeLaplaceRatioDen x := by
      have hexp : Real.exp (-x) < (1 / 2 : ℝ) := by
        calc
          Real.exp (-x) < Real.exp (-1) := Real.exp_lt_exp.mpr (neg_lt_neg hone)
          _ < (1 / 2 : ℝ) := by
            rw [Real.exp_neg]
            have htwo : (2 : ℝ) < Real.exp 1 := by
              nlinarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
            simpa only [one_div] using one_div_lt_one_div_of_lt
              (show (0 : ℝ) < 2 by norm_num) htwo
      unfold nonnegativeLaplaceRatioDen
      linarith
    have hnum : ‖LevyTriplet.poissonExponentIntegrand t x‖ ≤ 2 := by
      unfold LevyTriplet.poissonExponentIntegrand
      calc
        ‖Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) - 1‖ ≤
            ‖Complex.exp (((x * t : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
    calc
      ‖LevyTriplet.poissonExponentIntegrand t x‖ /
          nonnegativeLaplaceRatioDen x ≤
          2 / nonnegativeLaplaceRatioDen x :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ 4 := by
        rw [(div_le_iff₀ hdenpos)]
        nlinarith
      _ ≤ max (3 * |t|) 4 := le_max_right _ _

noncomputable def nonnegativeFourierRatioBCF (t : ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨nonnegativeFourierRatioClamped t,
      continuous_nonnegativeFourierRatioClamped t⟩
    (2 * max (3 * |t|) 4) fun x y => by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans <| by
        have hx := norm_nonnegativeFourierRatio_le
          (t := t) (x := max x 0) (le_max_right x 0)
        have hy := norm_nonnegativeFourierRatio_le
          (t := t) (x := max y 0) (le_max_right y 0)
        dsimp [nonnegativeFourierRatioClamped]
        linarith

/-- The finite measure `(1 - exp (-x)) (n+1) μ^(1/(n+1))(dx)`. -/
noncomputable def canonicalNonnegativeExtractionMeasure
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible) (n : ℕ) : Measure ℝ :=
  (hID.canonicalRootIntensity n : Measure ℝ).withDensity
    (fun x => (nonnegativeExtractionWeight x : ENNReal))

instance instFiniteCanonicalNonnegativeExtractionMeasure
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible) (n : ℕ) :
    IsFiniteMeasure (canonicalNonnegativeExtractionMeasure hID n) := by
  apply IsFiniteMeasure.mk
  rw [canonicalNonnegativeExtractionMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    ∫⁻ x, (nonnegativeExtractionWeight x : ENNReal)
        ∂(hID.canonicalRootIntensity n : Measure ℝ) ≤
        ∫⁻ _ : ℝ, 1 ∂(hID.canonicalRootIntensity n : Measure ℝ) := by
          apply lintegral_mono
          intro x
          change (nonnegativeExtractionWeight x : ENNReal) ≤ ((1 : NNReal) : ENNReal)
          exact ENNReal.coe_le_coe.mpr (nonnegativeExtractionWeight_le_one x)
    _ < ∞ := by simp

/-- Bundled finite-measure form of the first-order extraction. -/
noncomputable def canonicalNonnegativeExtractionFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible) (n : ℕ) :
    FiniteMeasure ℝ :=
  ⟨canonicalNonnegativeExtractionMeasure hID n,
    instFiniteCanonicalNonnegativeExtractionMeasure hID n⟩

@[simp, norm_cast]
theorem coe_canonicalNonnegativeExtractionFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible) (n : ℕ) :
    (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ) =
      canonicalNonnegativeExtractionMeasure hID n := rfl

theorem canonicalNonnegativeExtractionFiniteMeasure_supported
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) (n : ℕ) :
    ∀ᵐ x ∂(canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ), 0 ≤ x := by
  rw [coe_canonicalNonnegativeExtractionFiniteMeasure,
    canonicalNonnegativeExtractionMeasure]
  rw [ae_withDensity_iff
    measurable_nonnegativeExtractionWeight.coe_nnreal_ennreal]
  rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
    ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
  have hbase := ProbabilityMeasure.isNonnegativeLaw_iff_ae _ |>.mp
      (canonicalRoot_isNonnegativeLaw hID hμ (n + 1) (Nat.succ_pos n))
  have hscaled := Measure.ae_smul_measure hbase ((n + 1 : ℕ) : NNReal)
  filter_upwards [hscaled] with x hx
  exact fun _ => hx

theorem nonnegativeExtractionWeight_smul_fourierRatioClamped
    {t x : ℝ} (hx : 0 ≤ x) :
    (nonnegativeExtractionWeight x : ℝ) •
        nonnegativeFourierRatioClamped t x =
      LevyTriplet.poissonExponentIntegrand t x := by
  by_cases hx0 : x = 0
  · subst x
    simp [nonnegativeExtractionWeight, nonnegativeFourierRatioClamped,
      nonnegativeFourierRatio, LevyTriplet.poissonExponentIntegrand]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hden : (nonnegativeLaplaceRatioDen x : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold nonnegativeLaplaceRatioDen
    exact (sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hxpos))).ne'
  rw [coe_nonnegativeExtractionWeight_of_nonneg hx]
  simp only [nonnegativeFourierRatioClamped, max_eq_left hx,
    nonnegativeFourierRatio, if_neg hx0, nonnegativeLaplaceRatioDen,
    NNReal.smul_def, Complex.real_smul]
  rw [← mul_div_assoc]
  apply mul_div_cancel_left₀
  simpa [nonnegativeLaplaceRatioDen] using hden

/-- The complex quotient exactly recovers the canonical first-order characteristic exponent. -/
theorem integral_nonnegativeFourierRatio_canonical
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) (n : ℕ) (t : ℝ) :
    ∫ x, nonnegativeFourierRatioClamped t x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ) =
      canonicalRootLinearization hID n t := by
  rw [coe_canonicalNonnegativeExtractionFiniteMeasure,
    canonicalNonnegativeExtractionMeasure,
    integral_withDensity_eq_integral_smul measurable_nonnegativeExtractionWeight]
  rw [← ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity
    hID n t]
  apply integral_congr_ae
  rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
    ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
  have hroot := ProbabilityMeasure.isNonnegativeLaw_iff_ae _ |>.mp
    (canonicalRoot_isNonnegativeLaw hID hmu (n + 1) (Nat.succ_pos n))
  have hscaled := Measure.ae_smul_measure hroot ((n + 1 : ℕ) : NNReal)
  filter_upwards [hscaled] with x hx
  exact nonnegativeExtractionWeight_smul_fourierRatioClamped hx

theorem tendsto_integral_nonnegativeFourierRatio_canonical
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) (t : ℝ) :
    Tendsto (fun n => ∫ x, nonnegativeFourierRatioClamped t x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)) atTop
      (nhds (hID.exponent t)) := by
  simpa only [integral_nonnegativeFourierRatio_canonical hID hmu] using
    (ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization hID t)

theorem nonnegativeExtractionWeight_mul_ratioClamped
    {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    (nonnegativeExtractionWeight x : ℝ) *
        nonnegativeLaplaceRatioClamped t x = 1 - Real.exp (-(t * x)) := by
  by_cases hx0 : x = 0
  · subst x
    simp [nonnegativeLaplaceRatioClamped, nonnegativeLaplaceRatio]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hden : 1 - Real.exp (-x) ≠ 0 :=
    (sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hxpos))).ne'
  rw [coe_nonnegativeExtractionWeight_of_nonneg hx]
  simp only [nonnegativeLaplaceRatioClamped, max_eq_left hx,
    nonnegativeLaplaceRatio, if_neg hx0, nonnegativeLaplaceRatioNum,
    nonnegativeLaplaceRatioDen]
  field_simp

/-- The subordinator moment integrand is controlled by the extraction weight. -/
theorem min_one_le_three_mul_nonnegativeExtractionWeight {x : ℝ} (hx : 0 ≤ x) :
    min 1 x ≤ 3 * (nonnegativeExtractionWeight x : ℝ) := by
  rw [coe_nonnegativeExtractionWeight_of_nonneg hx]
  by_cases hxone : x ≤ 1
  · rw [min_eq_right hxone]
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hprod := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x)
      (Real.exp_pos (-x)).le
    have hprod' : x * Real.exp (-x) + Real.exp (-x) ≤ 1 := by
      calc
        x * Real.exp (-x) + Real.exp (-x) =
            (x + 1) * Real.exp (-x) := by ring
        _ ≤ Real.exp x * Real.exp (-x) := hprod
        _ = 1 := by rw [← Real.exp_add]; norm_num
    have he3 : Real.exp 1 < 3 := by
      have he := Real.exp_bound' (x := (1 : ℝ)) zero_le_one le_rfl
        (n := 3) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at he
      linarith
    have hthird : (1 / 3 : ℝ) < Real.exp (-1) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        one_div_lt_one_div_of_lt (Real.exp_pos 1) he3
    have hmono : Real.exp (-1) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (neg_le_neg hxone)
    nlinarith [hthird.trans_le hmono]
  · rw [min_eq_left (le_of_not_ge hxone)]
    have hone : 1 < x := lt_of_not_ge hxone
    have hhalf : Real.exp (-1) < (1 / 2 : ℝ) := by
      rw [Real.exp_neg]
      have htwo : (2 : ℝ) < Real.exp 1 := by
        nlinarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
      simpa only [one_div] using one_div_lt_one_div_of_lt
        (show (0 : ℝ) < 2 by norm_num) htwo
    have hmono : Real.exp (-x) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (neg_le_neg hone.le)
    nlinarith [hmono.trans_lt hhalf]

/-- Reciprocal extraction weight away from zero, internal to the nonnegative LK construction. -/
noncomputable def nonnegativeExtractionJumpDensity (x : ℝ) : NNReal :=
  if 0 < x then (nonnegativeExtractionWeight x)⁻¹ else 0

theorem measurable_nonnegativeExtractionJumpDensity :
    Measurable nonnegativeExtractionJumpDensity := by
  unfold nonnegativeExtractionJumpDensity
  exact Measurable.ite measurableSet_Ioi
    measurable_nonnegativeExtractionWeight.inv measurable_const

noncomputable def nonnegativeExtractionJumpMeasure (kappa : FiniteMeasure ℝ) :
    Measure ℝ :=
  (kappa : Measure ℝ).withDensity
    (fun x => (nonnegativeExtractionJumpDensity x : ENNReal))

theorem nonnegativeExtractionJumpMeasure_supportedPositive
    (kappa : FiniteMeasure ℝ) :
    ∀ᵐ x ∂nonnegativeExtractionJumpMeasure kappa, 0 < x := by
  rw [nonnegativeExtractionJumpMeasure, ae_withDensity_iff
    measurable_nonnegativeExtractionJumpDensity.coe_nnreal_ennreal]
  filter_upwards [] with x
  intro hdensity
  by_contra hx
  have hx' : ¬ 0 < x := hx
  simp [nonnegativeExtractionJumpDensity, hx'] at hdensity

theorem integrable_min_one_nonnegativeExtractionJumpMeasure
    (kappa : FiniteMeasure ℝ)
    (hsupport : ∀ᵐ x ∂(kappa : Measure ℝ), 0 ≤ x) :
    Integrable (fun x : ℝ => min 1 x)
      (nonnegativeExtractionJumpMeasure kappa) := by
  rw [nonnegativeExtractionJumpMeasure,
    integrable_withDensity_iff_integrable_smul
      measurable_nonnegativeExtractionJumpDensity]
  apply (integrable_const (μ := (kappa : Measure ℝ)) (3 : ℝ)).mono'
  · exact (measurable_nonnegativeExtractionJumpDensity.smul
      (measurable_const.min measurable_id)).aestronglyMeasurable
  · filter_upwards [hsupport] with x hx
    by_cases hx0 : x = 0
    · subst x
      simp [nonnegativeExtractionJumpDensity]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hwpos : 0 < (nonnegativeExtractionWeight x : ℝ) := by
      rw [coe_nonnegativeExtractionWeight_of_nonneg hx]
      exact sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hxpos))
    simp only [nonnegativeExtractionJumpDensity, if_pos hxpos, NNReal.coe_inv]
    change ‖((nonnegativeExtractionWeight x : ℝ))⁻¹ * min 1 x‖ ≤ 3
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr hwpos.le) (le_min zero_le_one hx))]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hwpos).2
      (min_one_le_three_mul_nonnegativeExtractionWeight hx)

noncomputable def nonnegativeExtractionDeterministicPart
    (kappa : FiniteMeasure ℝ) : NNReal :=
  ⟨(kappa : Measure ℝ).real {0}, measureReal_nonneg⟩

/-- Reconstruction of the subordinator parameters from a finite first-order limit. -/
noncomputable def nonnegativeLevyPairOfExtraction
    (kappa : FiniteMeasure ℝ)
    (hsupport : ∀ᵐ x ∂(kappa : Measure ℝ), 0 ≤ x) :
    NonnegativeLevyPair where
  deterministicPart := nonnegativeExtractionDeterministicPart kappa
  jumpMeasure := nonnegativeExtractionJumpMeasure kappa
  supportedPositive := nonnegativeExtractionJumpMeasure_supportedPositive kappa
  integrable_min_one :=
    integrable_min_one_nonnegativeExtractionJumpMeasure kappa hsupport

theorem nonnegativeExtractionJumpDensity_smul_uncompensated
    {t x : ℝ} (hx : 0 < x) :
    (nonnegativeExtractionJumpDensity x : ℝ) •
        NonnegativeLevyPair.uncompensatedJumpIntegrand t x =
      nonnegativeFourierRatioClamped t x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hxnonneg : 0 ≤ x := hx.le
  have hwpos : 0 < (nonnegativeExtractionWeight x : ℝ) := by
    rw [coe_nonnegativeExtractionWeight_of_nonneg hxnonneg]
    exact sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hx))
  have hw : ((nonnegativeExtractionWeight x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hwpos.ne'
  simp only [nonnegativeExtractionJumpDensity, if_pos hx,
    nonnegativeFourierRatioClamped, max_eq_left hxnonneg,
    nonnegativeFourierRatio, if_neg hx0, NNReal.smul_def,
    Complex.real_smul, NNReal.coe_inv]
  rw [show NonnegativeLevyPair.uncompensatedJumpIntegrand t x =
      LevyTriplet.poissonExponentIntegrand t x by
    unfold NonnegativeLevyPair.uncompensatedJumpIntegrand
      LevyTriplet.poissonExponentIntegrand
    congr 3
    push_cast
    ring]
  rw [coe_nonnegativeExtractionWeight_of_nonneg hxnonneg,
    nonnegativeLaplaceRatioDen]
  simp only [one_div, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

/-- Decomposition of a nonnegative extraction limit into its atom at zero and positive jumps. -/
theorem exponent_nonnegativeLevyPairOfExtraction
    (kappa : FiniteMeasure ℝ)
    (hsupport : ∀ᵐ x ∂(kappa : Measure ℝ), 0 ≤ x) (t : ℝ) :
    (nonnegativeLevyPairOfExtraction kappa hsupport).toLevyTriplet.exponent t =
      ∫ x, nonnegativeFourierRatioClamped t x ∂(kappa : Measure ℝ) := by
  let eta := nonnegativeLevyPairOfExtraction kappa hsupport
  have hweighted :
      ∫ x, NonnegativeLevyPair.uncompensatedJumpIntegrand t x ∂eta.jumpMeasure =
        ∫ x in ({0} : Set ℝ)ᶜ, nonnegativeFourierRatioClamped t x
          ∂(kappa : Measure ℝ) := by
    rw [show eta.jumpMeasure = nonnegativeExtractionJumpMeasure kappa by rfl,
      nonnegativeExtractionJumpMeasure,
      integral_withDensity_eq_integral_smul
        measurable_nonnegativeExtractionJumpDensity,
      ← integral_indicator (MeasurableSet.singleton 0).compl]
    apply integral_congr_ae
    filter_upwards [hsupport] with x hx
    by_cases hx0 : x = 0
    · subst x
      simp [nonnegativeExtractionJumpDensity]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [Set.indicator_of_mem]
      · exact nonnegativeExtractionJumpDensity_smul_uncompensated hxpos
      · simpa using hx0
  have hint : Integrable (nonnegativeFourierRatioClamped t)
      (kappa : Measure ℝ) :=
    (nonnegativeFourierRatioBCF t).integrable (kappa : Measure ℝ)
  have hsplit := integral_add_compl (MeasurableSet.singleton 0) hint
  have hzero :
      ∫ x in ({0} : Set ℝ), nonnegativeFourierRatioClamped t x
          ∂(kappa : Measure ℝ) =
        (((kappa : Measure ℝ).real {0} * t : ℝ) : ℂ) * Complex.I := by
    rw [integral_singleton]
    simp [nonnegativeFourierRatioClamped, nonnegativeFourierRatio]
    ring
  rw [NonnegativeLevyPair.exponent_toLevyTriplet, hweighted]
  change ((((kappa : Measure ℝ).real {0} : ℝ) * t : ℝ) : ℂ) * Complex.I +
      ∫ x in ({0} : Set ℝ)ᶜ, nonnegativeFourierRatioClamped t x
        ∂(kappa : Measure ℝ) = _
  rw [← hzero]
  exact hsplit

/-- The bounded quotient cancels the extraction weight and recovers the first-order
log-Laplace increment of the canonical root. -/
theorem integral_nonnegativeLaplaceRatio_canonical
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫ x, nonnegativeLaplaceRatioClamped t x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ) =
      (n + 1 : ℝ) *
        (1 - nonnegativeLaplaceAt t
          (hID.nthRoot (n + 1) (Nat.succ_pos n))) := by
  let rho := hID.nthRoot (n + 1) (Nat.succ_pos n)
  have hrho : rho.IsNonnegativeLaw :=
    canonicalRoot_isNonnegativeLaw hID hmu (n + 1) (Nat.succ_pos n)
  rw [coe_canonicalNonnegativeExtractionFiniteMeasure,
    canonicalNonnegativeExtractionMeasure,
    integral_withDensity_eq_integral_smul measurable_nonnegativeExtractionWeight]
  rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
    ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
  rw [FiniteMeasure.toMeasure_smul]
  change (∫ x, (nonnegativeExtractionWeight x : ℝ) *
      nonnegativeLaplaceRatioClamped t x
      ∂((((n + 1 : ℕ) : NNReal) : ENNReal) • (rho : Measure ℝ))) = _
  rw [integral_smul_measure]
  simp only [smul_eq_mul]
  rw [ENNReal.coe_toReal]
  push_cast
  rw [show (∫ x, (nonnegativeExtractionWeight x : ℝ) *
      nonnegativeLaplaceRatioClamped t x ∂(rho : Measure ℝ)) =
      ∫ x, 1 - Real.exp (-(t * x)) ∂(rho : Measure ℝ) by
    apply integral_congr_ae
    filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae rho |>.mp hrho] with x hx
    exact nonnegativeExtractionWeight_mul_ratioClamped ht hx]
  rw [integral_sub (integrable_const 1)
    (integrable_nonnegativeLaplaceAt hrho ht)]
  simp [nonnegativeLaplaceAt, rho]

theorem tendsto_integral_nonnegativeLaplaceRatio_canonical
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ x, nonnegativeLaplaceRatioClamped t x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)) atTop
      (𝓝 (-Real.log (nonnegativeLaplaceAt t mu))) := by
  simpa only [integral_nonnegativeLaplaceRatio_canonical hID hmu ht] using
    tendsto_firstOrderRootMassAt hID hmu ht

theorem canonicalNonnegativeExtractionFiniteMeasure_mass_coe
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) (n : ℕ) :
    ((canonicalNonnegativeExtractionFiniteMeasure hID n).mass : ℝ) =
      (n + 1 : ℝ) *
        (1 - nonnegativeLaplace
          (hID.nthRoot (n + 1) (Nat.succ_pos n))) := by
  let ρ := hID.nthRoot (n + 1) (Nat.succ_pos n)
  have hρ : ρ.IsNonnegativeLaw :=
    canonicalRoot_isNonnegativeLaw hID hμ (n + 1) (Nat.succ_pos n)
  change (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ).real Set.univ = _
  change ENNReal.toReal
      ((canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ) Set.univ) = _
  calc
    _ = _ := by
      rw [coe_canonicalNonnegativeExtractionFiniteMeasure,
        canonicalNonnegativeExtractionMeasure,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
        ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
      change ENNReal.toReal
          (∫⁻ x, (nonnegativeExtractionWeight x : ENNReal)
            ∂((n + 1 : ℕ) : NNReal) • (ρ : Measure ℝ)) = _
      rw [lintegral_smul_measure]
      rw [ENNReal.toReal_smul]
      · simp only [NNReal.smul_def, smul_eq_mul]
        push_cast
        rw [show ENNReal.toReal
            (∫⁻ x, (nonnegativeExtractionWeight x : ENNReal) ∂(ρ : Measure ℝ)) =
            ∫ x, (nonnegativeExtractionWeight x : ℝ) ∂(ρ : Measure ℝ) by
          rw [integral_eq_lintegral_of_nonneg_ae]
          · simp only [ENNReal.ofReal_coe_nnreal]
          · exact Eventually.of_forall fun _ => NNReal.coe_nonneg _
          · exact
              continuous_nonnegativeExtractionWeight.measurable.coe_nnreal_real
                |>.aestronglyMeasurable]
        rw [show (∫ x, (nonnegativeExtractionWeight x : ℝ) ∂(ρ : Measure ℝ)) =
            1 - nonnegativeLaplace ρ by
          rw [integral_congr_ae]
          · rw [integral_sub (integrable_const 1)
              (integrable_exp_neg_of_isNonnegativeLaw hρ)]
            simp [nonnegativeLaplace]
          · filter_upwards
              [ProbabilityMeasure.isNonnegativeLaw_iff_ae ρ |>.mp hρ] with x hx
            exact coe_nonnegativeExtractionWeight_of_nonneg hx]

theorem tendsto_canonicalNonnegativeExtraction_mass
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) :
    Tendsto (fun n => ((canonicalNonnegativeExtractionFiniteMeasure hID n).mass : ℝ))
      atTop (𝓝 (-Real.log (nonnegativeLaplace μ))) := by
  simpa only [canonicalNonnegativeExtractionFiniteMeasure_mass_coe hID hμ] using
    tendsto_firstOrderRootMass hID hμ

/-! ## Laplace probes and tightness data -/

/-- A bounded tail probe on the nonnegative half-line. -/
noncomputable def nonnegativeExtractionProbe (s x : ℝ) : ℝ :=
  1 - Real.exp (-(s * x))

theorem continuous_nonnegativeExtractionProbe (s : ℝ) :
    Continuous (nonnegativeExtractionProbe s) := by
  unfold nonnegativeExtractionProbe
  fun_prop

theorem nonnegativeExtractionProbe_nonneg {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    0 ≤ nonnegativeExtractionProbe s x := by
  exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg hs hx)))

theorem nonnegativeExtractionProbe_le_one {s x : ℝ} :
    nonnegativeExtractionProbe s x ≤ 1 := by
  unfold nonnegativeExtractionProbe
  linarith [Real.exp_pos (-(s * x))]

theorem integrable_nonnegativeExtractionProbe
    (kappa : FiniteMeasure ℝ) (hsupport : ∀ᵐ x ∂(kappa : Measure ℝ), 0 ≤ x)
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (nonnegativeExtractionProbe s) (kappa : Measure ℝ) := by
  apply (integrable_const (μ := (kappa : Measure ℝ)) (1 : ℝ)).mono'
  · exact (continuous_nonnegativeExtractionProbe s).aestronglyMeasurable
  · filter_upwards [hsupport] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (nonnegativeExtractionProbe_nonneg hs hx)]
    exact nonnegativeExtractionProbe_le_one

/-- The Laplace probe of the first-order root measure is the mixed second difference of the
root Laplace transform. -/
theorem integral_nonnegativeExtractionProbe_canonical
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ∫ x, nonnegativeExtractionProbe s x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ) =
      (n + 1 : ℝ) *
        ((1 - nonnegativeLaplaceAt 1
            (hID.nthRoot (n + 1) (Nat.succ_pos n))) +
          (1 - nonnegativeLaplaceAt s
            (hID.nthRoot (n + 1) (Nat.succ_pos n))) -
          (1 - nonnegativeLaplaceAt (s + 1)
            (hID.nthRoot (n + 1) (Nat.succ_pos n)))) := by
  let rho := hID.nthRoot (n + 1) (Nat.succ_pos n)
  have hrho : rho.IsNonnegativeLaw :=
    canonicalRoot_isNonnegativeLaw hID hμ (n + 1) (Nat.succ_pos n)
  rw [coe_canonicalNonnegativeExtractionFiniteMeasure,
    canonicalNonnegativeExtractionMeasure,
    integral_withDensity_eq_integral_smul measurable_nonnegativeExtractionWeight]
  rw [ProbabilityMeasure.IsInfinitelyDivisible.canonicalRootIntensity,
    ProbabilityMeasure.IsInfinitelyDivisible.compoundPoissonRootIntensity]
  rw [FiniteMeasure.toMeasure_smul]
  change (∫ x, (nonnegativeExtractionWeight x : ℝ) *
      nonnegativeExtractionProbe s x
      ∂((((n + 1 : ℕ) : NNReal) : ENNReal) • (rho : Measure ℝ))) = _
  rw [integral_smul_measure]
  simp only [smul_eq_mul]
  rw [ENNReal.coe_toReal]
  push_cast
  rw [show (∫ x, (nonnegativeExtractionWeight x : ℝ) *
      nonnegativeExtractionProbe s x ∂(rho : Measure ℝ)) =
      ∫ x, ((1 - Real.exp (-x)) * (1 - Real.exp (-(s * x))))
        ∂(rho : Measure ℝ) by
    apply integral_congr_ae
    filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae rho |>.mp hrho] with x hx
    rw [coe_nonnegativeExtractionWeight_of_nonneg hx]
    rfl]
  have h1 := integrable_nonnegativeLaplaceAt hrho (show 0 ≤ (1 : ℝ) by norm_num)
  have h1' : Integrable (fun x : ℝ => Real.exp (-x)) (rho : Measure ℝ) := by
    simpa using h1
  have hs1 := integrable_nonnegativeLaplaceAt hrho (add_nonneg hs zero_le_one)
  have hs' := integrable_nonnegativeLaplaceAt hrho hs
  have hc : Integrable (fun _x : ℝ => (1 : ℝ)) (rho : Measure ℝ) := integrable_const 1
  have hsub1 :
      (∫ x, 1 - Real.exp (-x) ∂(rho : Measure ℝ)) =
        (∫ _x, (1 : ℝ) ∂(rho : Measure ℝ)) -
          ∫ x, Real.exp (-x) ∂(rho : Measure ℝ) := by
    simpa only [Pi.sub_apply] using integral_sub hc h1'
  have hsub2 :
      (∫ x, 1 - Real.exp (-x) - Real.exp (-(s * x)) ∂(rho : Measure ℝ)) =
        ((∫ _x, (1 : ℝ) ∂(rho : Measure ℝ)) -
          ∫ x, Real.exp (-x) ∂(rho : Measure ℝ)) -
          ∫ x, Real.exp (-(s * x)) ∂(rho : Measure ℝ) := by
    calc
      _ = (∫ x, 1 - Real.exp (-x) ∂(rho : Measure ℝ)) -
          ∫ x, Real.exp (-(s * x)) ∂(rho : Measure ℝ) := by
        simpa only [Pi.sub_apply] using integral_sub (hc.sub h1') hs'
      _ = _ := by rw [hsub1]
  rw [show (fun x : ℝ => (1 - Real.exp (-x)) * (1 - Real.exp (-(s * x)))) =
      fun x => 1 - Real.exp (-x) - Real.exp (-(s * x)) +
        Real.exp (-((s + 1) * x)) by
    funext x
    rw [show -((s + 1) * x) = -x + -(s * x) by ring, Real.exp_add]
    ring]
  have hsplit :
      (∫ x, 1 - Real.exp (-x) - Real.exp (-(s * x)) +
          Real.exp (-((s + 1) * x)) ∂(rho : Measure ℝ)) =
        ((∫ _x, (1 : ℝ) ∂(rho : Measure ℝ)) -
          ∫ x, Real.exp (-x) ∂(rho : Measure ℝ)) -
          (∫ x, Real.exp (-(s * x)) ∂(rho : Measure ℝ)) +
          ∫ x, Real.exp (-((s + 1) * x)) ∂(rho : Measure ℝ) := by
    change
      (∫ x, ((((fun _x : ℝ => (1 : ℝ)) - fun x => Real.exp (-x)) -
          fun x => Real.exp (-(s * x))) +
          fun x => Real.exp (-((s + 1) * x))) x ∂(rho : Measure ℝ)) = _
    calc
      _ = (∫ x, (1 - Real.exp (-x) - Real.exp (-(s * x))) ∂(rho : Measure ℝ)) +
          ∫ x, Real.exp (-((s + 1) * x)) ∂(rho : Measure ℝ) :=
        integral_add ((hc.sub h1').sub hs') hs1
      _ = _ := by rw [hsub2]
  rw [hsplit]
  simp only [nonnegativeLaplaceAt]
  rw [show (∫ _x : ℝ, (1 : ℝ) ∂(rho : Measure ℝ)) = 1 by simp]
  dsimp [rho]
  ring

/-- Pointwise limit of all bounded Laplace probes of the extraction measures. -/
theorem tendsto_integral_nonnegativeExtractionProbe_canonical
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => ∫ x, nonnegativeExtractionProbe s x ∂
        (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)) atTop
      (𝓝 (-Real.log (nonnegativeLaplaceAt 1 μ) -
        Real.log (nonnegativeLaplaceAt s μ) +
        Real.log (nonnegativeLaplaceAt (s + 1) μ))) := by
  rw [show (fun n => ∫ x, nonnegativeExtractionProbe s x ∂
      (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)) =
      fun n : ℕ =>
        ((n + 1 : ℝ) * (1 - nonnegativeLaplaceAt 1
          (hID.nthRoot (n + 1) (Nat.succ_pos n)))) +
        ((n + 1 : ℝ) * (1 - nonnegativeLaplaceAt s
          (hID.nthRoot (n + 1) (Nat.succ_pos n)))) -
        ((n + 1 : ℝ) * (1 - nonnegativeLaplaceAt (s + 1)
          (hID.nthRoot (n + 1) (Nat.succ_pos n)))) by
    funext n
    rw [integral_nonnegativeExtractionProbe_canonical hID hμ hs]
    ring]
  convert ((tendsto_firstOrderRootMassAt hID hμ (show 0 ≤ (1 : ℝ) by norm_num)).add
    (tendsto_firstOrderRootMassAt hID hμ hs)).sub
      (tendsto_firstOrderRootMassAt hID hμ (add_nonneg hs zero_le_one)) using 1 <;> ring

/-! ## Tightness of the weighted roots -/

/-- The Laplace transform tends to one along the positive sequence `1 / (n+1)`. -/
theorem tendsto_nonnegativeLaplaceAt_inv_succ
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw) :
    Tendsto (fun n : ℕ => nonnegativeLaplaceAt ((n + 1 : ℝ)⁻¹) μ)
      atTop (𝓝 1) := by
  have hdct : Tendsto
      (fun n : ℕ => ∫ x, Real.exp (-(((n + 1 : ℝ)⁻¹) * x)) ∂(μ : Measure ℝ))
      atTop (𝓝 (∫ _x, (1 : ℝ) ∂(μ : Measure ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _x => (1 : ℝ))
    · intro n
      exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg (by positivity) hx))
    · filter_upwards [] with x
      have hs : Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
        simpa only [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : Tendsto (fun n : ℕ => -(((n + 1 : ℝ)⁻¹) * x))
          atTop (𝓝 0) := by
        simpa only [zero_mul, neg_zero] using (hs.mul_const x).neg
      change Tendsto (Real.exp ∘ fun n : ℕ => -(((n + 1 : ℝ)⁻¹) * x))
        atTop (𝓝 1)
      simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hz
  simpa [nonnegativeLaplaceAt] using hdct

/-- The shifted Laplace transform tends to its value at one along `1 / (n+1)`. -/
theorem tendsto_nonnegativeLaplaceAt_one_add_inv_succ
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw) :
    Tendsto (fun n : ℕ => nonnegativeLaplaceAt (((n + 1 : ℝ)⁻¹) + 1) μ)
      atTop (𝓝 (nonnegativeLaplaceAt 1 μ)) := by
  unfold nonnegativeLaplaceAt
  apply tendsto_integral_of_dominated_convergence (fun _x => (1 : ℝ))
  · intro n
    exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact (Real.exp_le_one_iff).2
      (neg_nonpos.mpr (mul_nonneg (by positivity) hx))
  · filter_upwards [] with x
    have hs : Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : Tendsto (fun n : ℕ => -((((n + 1 : ℝ)⁻¹) + 1) * x))
        atTop (𝓝 (-x)) := by
      simpa only [zero_add, one_mul] using (((hs.add_const 1).mul_const x).neg)
    rw [show (fun n : ℕ => Real.exp (-((((n + 1 : ℝ)⁻¹) + 1) * x))) =
      Real.exp ∘ fun n : ℕ => -((((n + 1 : ℝ)⁻¹) + 1) * x) by rfl]
    simpa only [one_mul] using (Real.continuous_exp.tendsto (-x)).comp hz

/-- The limiting Laplace-tail bound vanishes as the probe parameter decreases to zero. -/
theorem tendsto_nonnegativeExtractionProbeLimit_inv_succ
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw) :
    Tendsto (fun n : ℕ =>
        -Real.log (nonnegativeLaplaceAt 1 μ) -
          Real.log (nonnegativeLaplaceAt ((n + 1 : ℝ)⁻¹) μ) +
          Real.log (nonnegativeLaplaceAt (((n + 1 : ℝ)⁻¹) + 1) μ))
      atTop (𝓝 0) := by
  have hlog0 : Tendsto
      (fun n : ℕ => Real.log (nonnegativeLaplaceAt ((n + 1 : ℝ)⁻¹) μ))
      atTop (𝓝 0) := by
    change Tendsto
      (Real.log ∘ fun n : ℕ => nonnegativeLaplaceAt ((n + 1 : ℝ)⁻¹) μ)
      atTop (𝓝 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        (tendsto_nonnegativeLaplaceAt_inv_succ hμ)
  have hL1 : 0 < nonnegativeLaplaceAt 1 μ :=
    nonnegativeLaplaceAt_pos hμ (by norm_num)
  have hlog1 : Tendsto
      (fun n : ℕ => Real.log
        (nonnegativeLaplaceAt (((n + 1 : ℝ)⁻¹) + 1) μ))
      atTop (𝓝 (Real.log (nonnegativeLaplaceAt 1 μ))) :=
    (Real.continuousAt_log hL1.ne').tendsto.comp
      (tendsto_nonnegativeLaplaceAt_one_add_inv_succ hμ)
  convert (tendsto_const_nhds.sub hlog0).add hlog1 using 1 <;> ring

/-- A Laplace probe controls the positive tail of any finite measure supported on `[0,∞)`. -/
theorem measureReal_abs_gt_le_two_integral_nonnegativeExtractionProbe
    (κ : FiniteMeasure ℝ) (hsupport : ∀ᵐ x ∂(κ : Measure ℝ), 0 ≤ x)
    {s r : ℝ} (hs : 0 < s) (hr : Real.log 2 / s ≤ r) :
    (κ : Measure ℝ).real {x | r < |x|} ≤
      2 * ∫ x, nonnegativeExtractionProbe s x ∂(κ : Measure ℝ) := by
  have hint := integrable_nonnegativeExtractionProbe κ hsupport hs.le
  have hscaled : Integrable (fun x => 2 * nonnegativeExtractionProbe s x)
      (κ : Measure ℝ) := hint.const_mul 2
  have hnonneg : 0 ≤ᵐ[(κ : Measure ℝ)]
      (fun x => 2 * nonnegativeExtractionProbe s x) := by
    filter_upwards [hsupport] with x hx
    exact mul_nonneg (by norm_num) (nonnegativeExtractionProbe_nonneg hs.le hx)
  have hpoint : ∀ x ∈ {x : ℝ | r < |x| ∧ 0 ≤ x},
      1 ≤ 2 * nonnegativeExtractionProbe s x := by
    intro x hx
    have hxr : r < x := by simpa [abs_of_nonneg hx.2] using hx.1
    have hsx : Real.log 2 ≤ s * x := by
      have hsr : Real.log 2 ≤ r * s := (div_le_iff₀ hs).mp hr
      nlinarith
    have hexp : Real.exp (-(s * x)) ≤ (2 : ℝ)⁻¹ := by
      calc
        Real.exp (-(s * x)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (neg_le_neg hsx)
        _ = (2 : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    unfold nonnegativeExtractionProbe
    linarith
  have hmeasure := hscaled.measure_le_integral hnonneg hpoint
  have heq : (κ : Measure ℝ) {x | r < |x|} =
      (κ : Measure ℝ) {x | r < |x| ∧ 0 ≤ x} := by
    rw [show {x : ℝ | r < |x| ∧ 0 ≤ x} = Set.Ici 0 ∩ {x | r < |x|} by
      ext x
      simp [and_comm]]
    apply measure_congr
    filter_upwards [hsupport] with x hx
    apply propext
    constructor
    · intro h
      exact ⟨hx, h⟩
    · intro h
      exact h.2
  have hmeasureReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hintegral0 : 0 ≤ ∫ x, 2 * nonnegativeExtractionProbe s x ∂(κ : Measure ℝ) := by
    have hzero : Integrable (fun _x : ℝ => (0 : ℝ)) (κ : Measure ℝ) :=
      integrable_zero ℝ ℝ (κ : Measure ℝ)
    simpa only [integral_zero] using integral_mono_ae hzero hscaled hnonneg
  rw [ENNReal.toReal_ofReal hintegral0] at hmeasureReal
  rw [measureReal_def, heq]
  simpa [integral_const_mul] using hmeasureReal

/-- The first-order nonnegative extraction measures form a tight family. -/
theorem isTightMeasureSet_canonicalNonnegativeExtraction
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) :
    IsTightMeasureSet (Set.range fun n =>
      (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)) := by
  let κ : ℕ → Measure ℝ := fun n =>
    (canonicalNonnegativeExtractionFiniteMeasure hID n : Measure ℝ)
  have hmass : ∃ C : ℝ≥0, ∀ᶠ n in atTop, κ n Set.univ ≤ (C : ℝ≥0∞) := by
    have hLpos : 0 < nonnegativeLaplace μ := nonnegativeLaplace_pos hμ
    have hLle : nonnegativeLaplace μ ≤ 1 := nonnegativeLaplace_le_one hμ
    have hm0 : 0 ≤ -Real.log (nonnegativeLaplace μ) :=
      neg_nonneg.mpr (Real.log_nonpos hLpos.le hLle)
    let C : ℝ≥0 := Real.toNNReal (-Real.log (nonnegativeLaplace μ) + 1)
    have hCcoe : (C : ℝ) = -Real.log (nonnegativeLaplace μ) + 1 := by
      dsimp [C]
      rw [max_eq_left]
      linarith
    have hmassReal := tendsto_canonicalNonnegativeExtraction_mass hID hμ
    have hbounded : ∀ᶠ n in atTop,
        ((canonicalNonnegativeExtractionFiniteMeasure hID n).mass : ℝ) ≤ (C : ℝ) := by
      apply ((tendsto_order.1 hmassReal).2 _ (lt_add_one _)).mono
      intro n hn
      rw [hCcoe]
      exact hn.le
    refine ⟨C, ?_⟩
    filter_upwards [hbounded] with n hn
    have hnn : (canonicalNonnegativeExtractionFiniteMeasure hID n).mass ≤ C := by
      exact_mod_cast hn
    dsimp [κ]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.coe_ne_top).mp
    change ((canonicalNonnegativeExtractionFiniteMeasure hID n).mass : ℝ) ≤ (C : ℝ)
    exact hn
  obtain ⟨C, hC⟩ := hmass
  refine MeasureTheory.isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one ℝ
    (fun y hy => ?_) C hC
  have hy' : y = 1 ∨ y = -1 := by
    rw [Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hy
    exact hy
  have hset (r : ℝ) : {x : ℝ | r < ‖inner ℝ y x‖} = {x | r < |x|} := by
    rcases hy' with rfl | rfl <;> ext x <;> simp [Real.norm_eq_abs]
  simp_rw [hset]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB := tendsto_nonnegativeExtractionProbeLimit_inv_succ hμ
  obtain ⟨k, hk⟩ : ∃ k : ℕ,
      2 * (-Real.log (nonnegativeLaplaceAt 1 μ) -
          Real.log (nonnegativeLaplaceAt ((k + 1 : ℝ)⁻¹) μ) +
          Real.log (nonnegativeLaplaceAt (((k + 1 : ℝ)⁻¹) + 1) μ)) < ε := by
    have hev := (tendsto_order.1 (hB.const_mul 2)).2 ε (by simpa using hε)
    exact hev.exists
  let s : ℝ := ((k + 1 : ℝ)⁻¹)
  refine ⟨Real.log 2 / s, fun r hr => ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg]
  · have htail n : (κ n).real {x | r < |x|} ≤
        2 * ∫ x, nonnegativeExtractionProbe s x ∂(κ n) := by
      exact measureReal_abs_gt_le_two_integral_nonnegativeExtractionProbe
        (canonicalNonnegativeExtractionFiniteMeasure hID n)
        (canonicalNonnegativeExtractionFiniteMeasure_supported hID hμ n)
        (by positivity) hr
    calc
      limsup (fun n => (κ n).real {x | r < |x|}) atTop ≤
          limsup (fun n => 2 * ∫ x, nonnegativeExtractionProbe s x ∂(κ n)) atTop := by
        refine limsup_le_limsup (.of_forall htail) ?_ ?_
        · exact IsCoboundedUnder.of_frequently_ge (.of_forall fun _ => measureReal_nonneg)
        · exact ((tendsto_integral_nonnegativeExtractionProbe_canonical hID hμ
            (by positivity)).const_mul 2).isBoundedUnder_le
      _ = 2 * (-Real.log (nonnegativeLaplaceAt 1 μ) -
          Real.log (nonnegativeLaplaceAt s μ) +
          Real.log (nonnegativeLaplaceAt (s + 1) μ)) := by
        apply Tendsto.limsup_eq
        exact (tendsto_integral_nonnegativeExtractionProbe_canonical hID hμ
          (by positivity)).const_mul 2
      _ < ε := by simpa [s] using hk
  · have htailBound : IsBoundedUnder (· ≤ ·) atTop
        (fun n => (κ n).real {x | r < |x|}) := by
      apply isBoundedUnder_of_eventually_le (a := (C : ℝ))
      filter_upwards [hC] with n hn
      have hle : κ n {x | r < |x|} ≤ (C : ℝ≥0∞) :=
        (measure_mono (Set.subset_univ _)).trans hn
      simpa only [measureReal_def] using ENNReal.toReal_le_coe_of_le_coe hle
    exact le_limsup_of_le htailBound fun b hb =>
      le_trans measureReal_nonneg (hb.exists.choose_spec)

/-- Prokhorov extraction for the first-order nonnegative root measures. -/
theorem exists_tendsto_subseq_canonicalNonnegativeExtraction
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    (hμ : μ.IsNonnegativeLaw) :
    ∃ κ : FiniteMeasure ℝ, ∃ φ : ℕ → ℕ,
      (∀ᵐ x ∂(κ : Measure ℝ), 0 ≤ x) ∧ StrictMono φ ∧
      Tendsto (fun n => canonicalNonnegativeExtractionFiniteMeasure hID (φ n))
        atTop (𝓝 κ) := by
  let κn : ℕ → FiniteMeasure ℝ := fun n =>
    canonicalNonnegativeExtractionFiniteMeasure hID n
  let m : ℝ≥0 := Real.toNNReal (-Real.log (nonnegativeLaplace μ))
  have hmcoe : (m : ℝ) = -Real.log (nonnegativeLaplace μ) := by
    dsimp [m]
    rw [max_eq_left]
    exact neg_nonneg.mpr (Real.log_nonpos
      (nonnegativeLaplace_pos hμ).le (nonnegativeLaplace_le_one hμ))
  have hmass : Tendsto (fun n => (κn n).mass) atTop (𝓝 m) := by
    rw [← NNReal.tendsto_coe]
    simpa [κn, hmcoe] using tendsto_canonicalNonnegativeExtraction_mass hID hμ
  by_cases hmzero : m = 0
  · have hmass0 : Tendsto (fun n => (κn n).mass) atTop (𝓝 0) := by
      simpa only [hmzero] using hmass
    have hzero : Tendsto κn atTop (𝓝 0) :=
      FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass0
    exact ⟨0, id, by simp, strictMono_id, by simpa [κn] using hzero⟩
  · have hmpos : 0 < m := pos_iff_ne_zero.mpr hmzero
    let c : ℝ≥0 := m / 2
    have hcpos : 0 < c := by positivity
    have hcm : c < m := by
      dsimp [c]
      exact div_lt_self hmpos (by norm_num)
    have hevent : ∀ᶠ n in atTop, c ≤ (κn n).mass :=
      ((tendsto_order.1 hmass).1 c hcm).mono fun _ h => h.le
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    let ρ : ℕ → ProbabilityMeasure ℝ := fun n => (κn (N + n)).normalize
    have htightκ : IsTightMeasureSet (Set.range fun n => (κn n : Measure ℝ)) := by
      simpa [κn] using isTightMeasureSet_canonicalNonnegativeExtraction hID hμ
    have htightρ : IsTightMeasureSet (Set.range fun n => (ρ n : Measure ℝ)) := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      have hεc : 0 < ε * (c : ℝ≥0∞) :=
        ENNReal.mul_pos hε.ne' (by exact_mod_cast hcpos.ne')
      rcases isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htightκ
          (ε * (c : ℝ≥0∞)) hεc with ⟨K, hKcompact, hKtail⟩
      refine ⟨K, hKcompact, ?_⟩
      intro ν hν
      rcases hν with ⟨n, rfl⟩
      have hmassLower : c ≤ (κn (N + n)).mass := hN _ (Nat.le_add_right N n)
      have hκne : κn (N + n) ≠ 0 := by
        exact (FiniteMeasure.mass_nonzero_iff _).mp
          (ne_of_gt (hcpos.trans_le hmassLower))
      have hmassne : (κn (N + n)).mass ≠ 0 :=
        (FiniteMeasure.mass_nonzero_iff _).mpr hκne
      dsimp [ρ]
      rw [(κn (N + n)).toMeasure_normalize_eq_of_nonzero hκne,
        Measure.smul_apply]
      rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hmassne]
      calc
        ((↑(κn (N + n)).mass : ℝ≥0∞))⁻¹ *
            (κn (N + n) : Measure ℝ) Kᶜ ≤
            ((c : ℝ≥0∞))⁻¹ * (ε * (c : ℝ≥0∞)) := by
          have hmassLower' : (c : ℝ≥0∞) ≤ ↑(κn (N + n)).mass := by
            exact_mod_cast hmassLower
          exact mul_le_mul' (ENNReal.inv_le_inv.mpr hmassLower')
            (hKtail _ ⟨N + n, rfl⟩)
        _ = ε := by
          rw [mul_comm ε (c : ℝ≥0∞), ← mul_assoc,
            ENNReal.inv_mul_cancel (by exact_mod_cast hcpos.ne') ENNReal.coe_ne_top, one_mul]
    let S : Set (ProbabilityMeasure ℝ) := Set.range ρ
    have htightS : IsTightMeasureSet
        {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ S} := by
      convert htightρ using 1
      ext ν
      constructor
      · rintro ⟨η, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨ρ n, ⟨n, rfl⟩, rfl⟩
    have hcompact : IsCompact (closure S) :=
      isCompact_closure_of_isTightMeasureSet htightS
    have hρmem (n : ℕ) : ρ n ∈ closure S := subset_closure ⟨n, rfl⟩
    rcases hcompact.tendsto_subseq hρmem with ⟨η, _hη, ψ, hψ, hρlim⟩
    have hρnonnegative (n : ℕ) : (ρ n).IsNonnegativeLaw := by
      have hmassLower : c ≤ (κn (N + n)).mass := hN _ (Nat.le_add_right N n)
      have hκne : κn (N + n) ≠ 0 := by
        exact (FiniteMeasure.mass_nonzero_iff _).mp
          (ne_of_gt (hcpos.trans_le hmassLower))
      rw [ProbabilityMeasure.isNonnegativeLaw_iff_ae]
      dsimp [ρ]
      rw [(κn (N + n)).toMeasure_normalize_eq_of_nonzero hκne]
      exact Measure.ae_smul_measure
        (canonicalNonnegativeExtractionFiniteMeasure_supported hID hμ (N + n)) _
    have hηnonnegative : η.IsNonnegativeLaw :=
      ProbabilityMeasure.IsNonnegativeLaw.tendsto hρlim
        (fun n => hρnonnegative (ψ n))
    let φ : ℕ → ℕ := fun n => N + ψ n
    have hφ : StrictMono φ := fun _ _ hab => Nat.add_lt_add_left (hψ hab) N
    let κ : FiniteMeasure ℝ := m • η.toFiniteMeasure
    have hκmass : κ.mass = m := by
      change (m • η.toFiniteMeasure) Set.univ = m
      rw [FiniteMeasure.smul_apply]
      simp
    have hκne : κ ≠ 0 := by
      intro h
      have := congrArg FiniteMeasure.mass h
      simp [hκmass, hmzero] at this
    have hκnormalize : κ.normalize = η := by
      apply ProbabilityMeasure.eq_of_forall_apply_eq
      intro A hA
      rw [κ.normalize_eq_of_nonzero hκne A]
      rw [hκmass]
      change m⁻¹ * (m • η.toFiniteMeasure) A = η A
      rw [FiniteMeasure.smul_apply]
      simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hmzero, one_mul]
      rfl
    have hmassSub : Tendsto (fun n => (κn (φ n)).mass) atTop (𝓝 κ.mass) := by
      rw [hκmass]
      exact hmass.comp (hφ.tendsto_atTop)
    have hnormSub : Tendsto (fun n => (κn (φ n)).normalize)
        atTop (𝓝 κ.normalize) := by
      rw [hκnormalize]
      simpa [Function.comp_def, ρ, φ] using hρlim
    have hlim : Tendsto (fun n => κn (φ n)) atTop (𝓝 κ) :=
      FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
        hnormSub hmassSub
    have hκsupport : ∀ᵐ x ∂(κ : Measure ℝ), 0 ≤ x := by
      dsimp [κ]
      exact Measure.ae_smul_measure
        (ProbabilityMeasure.isNonnegativeLaw_iff_ae η |>.mp hηnonnegative) _
    exact ⟨κ, φ, hκsupport, hφ, by simpa [κn] using hlim⟩

/-- A finite first-order extraction limit carries both the complete log-Laplace exponent and the
full characteristic exponent. -/
theorem exists_nonnegativeExtractionLimit
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) :
    ∃ kappa : FiniteMeasure ℝ,
      (∀ᵐ x ∂(kappa : Measure ℝ), 0 ≤ x) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∫ x, nonnegativeLaplaceRatioClamped t x ∂(kappa : Measure ℝ) =
          -Real.log (nonnegativeLaplaceAt t mu)) ∧
      ∀ t : ℝ,
        ∫ x, nonnegativeFourierRatioClamped t x ∂(kappa : Measure ℝ) =
          hID.exponent t := by
  rcases exists_tendsto_subseq_canonicalNonnegativeExtraction hID hmu with
    ⟨kappa, phi, hsupport, hphi, hlim⟩
  refine ⟨kappa, hsupport, ?_, ?_⟩
  · intro t ht
    have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
      (nonnegativeLaplaceRatioBCF t ht)
    have hweak' : Tendsto
        (fun n => ∫ x, nonnegativeLaplaceRatioClamped t x ∂
          (canonicalNonnegativeExtractionFiniteMeasure hID (phi n) : Measure ℝ))
        atTop (nhds (∫ x, nonnegativeLaplaceRatioClamped t x ∂
          (kappa : Measure ℝ))) := by
      simpa [nonnegativeLaplaceRatioBCF] using hweak
    have hsource := (tendsto_integral_nonnegativeLaplaceRatio_canonical hID hmu ht).comp
      hphi.tendsto_atTop
    exact tendsto_nhds_unique hweak' hsource
  · intro t
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim
        (nonnegativeFourierRatioBCF t)
    have hweak' : Tendsto
        (fun n => ∫ x, nonnegativeFourierRatioClamped t x ∂
          (canonicalNonnegativeExtractionFiniteMeasure hID (phi n) : Measure ℝ))
        atTop (nhds (∫ x, nonnegativeFourierRatioClamped t x ∂
          (kappa : Measure ℝ))) := by
      simpa [nonnegativeFourierRatioBCF] using hweak
    have hsource :=
      (tendsto_integral_nonnegativeFourierRatio_canonical hID hmu t).comp
        hphi.tendsto_atTop
    exact tendsto_nhds_unique hweak' hsource

/-- The nonnegative Lévy--Khintchine converse: every infinitely divisible law supported on
`[0,∞)` has a unique deterministic-drift/positive-jump representation. -/
theorem existsUnique_nonnegativeLevyPair
    {mu : ProbabilityMeasure ℝ} (hID : mu.IsInfinitelyDivisible)
    (hmu : mu.IsNonnegativeLaw) :
    ∃! eta : NonnegativeLevyPair, eta.toLevyTriplet.Represents mu := by
  rcases exists_nonnegativeExtractionLimit hID hmu with
    ⟨kappa, hsupport, _hLaplace, hFourier⟩
  let eta := nonnegativeLevyPairOfExtraction kappa hsupport
  have heta : eta.toLevyTriplet.Represents mu := by
    intro t
    rw [← hID.exp_exponent t]
    congr 1
    exact ((exponent_nonnegativeLevyPairOfExtraction kappa hsupport t).trans
      (hFourier t)).symm
  refine ⟨eta, heta, ?_⟩
  intro xi hxi
  exact NonnegativeLevyPair.eq_of_represents hxi heta

/-- Source-facing form of Klenke Theorem 16.14 in the StochLean fixed-truncation convention. -/
theorem nonnegativeLevyKhintchine_iff
    {mu : ProbabilityMeasure ℝ} :
    mu.IsInfinitelyDivisible ∧ mu.IsNonnegativeLaw ↔
      ∃! eta : NonnegativeLevyPair, eta.toLevyTriplet.Represents mu := by
  constructor
  · rintro ⟨hID, hmu⟩
    exact existsUnique_nonnegativeLevyPair hID hmu
  · rintro ⟨eta, heta, _hunique⟩
    refine ⟨heta.isInfinitelyDivisible, ?_⟩
    have heqMeasure : (mu : Measure ℝ) =
        (eta.law : Measure ℝ) := by
      apply Measure.ext_of_charFun
      funext t
      rw [heta t, eta.represents_law t]
    have heq : mu = eta.law := by
      apply ProbabilityMeasure.toMeasure_injective
      exact heqMeasure
    rw [heq]
    exact eta.isNonnegativeLaw_law

end ProbabilityTheory
