/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.RootLimits
public import StochLean.Probability.InfinitelyDivisible.Bounds

/-!
# Limits of convolution powers

This module develops the difficult nonvanishing step in the reverse direction of the
characteristic-function root-limit criterion.  If characteristic functions raised to increasing
convolution powers converge to a limit continuous at zero, the limit is itself a characteristic
function and is nowhere zero.  The proof follows the internal dyadic estimate, with all scalar
logarithmic asymptotics proved inside StochLean.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ProbabilityTheory

namespace ProbabilityTheory

def HasConvolutionPowerLimit (ρ : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  ContinuousAt φ 0 ∧ ∀ t : ℝ,
    Tendsto (fun n => charFun (ρ n : Measure ℝ) t ^ (n + 1)) atTop (𝓝 (φ t))

theorem HasConvolutionPowerLimit.zero {ρ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (h : HasConvolutionPowerLimit ρ φ) : φ 0 = 1 := by
  have hz := h.2 0
  have hone : (fun n : ℕ => charFun (ρ n : Measure ℝ) 0 ^ (n + 1)) =
      fun _ => (1 : ℂ) := by
    funext n
    simp
  rw [hone] at hz
  exact tendsto_nhds_unique hz tendsto_const_nhds

/-- The pointwise limit is realized by a probability law, and the convolution powers converge
weakly to that law. -/
theorem HasConvolutionPowerLimit.exists_limitLaw
    {ρ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (h : HasConvolutionPowerLimit ρ φ) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ t, charFun (μ : Measure ℝ) t = φ t) ∧
        Tendsto (fun n => (ρ n).convPow (n + 1)) atTop (𝓝 μ) := by
  apply exists_probabilityMeasure_of_tendsto_charFun h.1
  intro t
  rw [show (fun n => charFun ((ρ n).convPow (n + 1) : Measure ℝ) t) =
      fun n => charFun (ρ n : Measure ℝ) t ^ (n + 1) by
    funext n
    exact ProbabilityMeasure.charFun_convPow_real (ρ n) (n + 1) t]
  exact h.2 t

theorem tendsto_nat_mul_sub_one_of_pow_tendsto
    {a : ℕ → ℝ} {A : ℝ} (ha : ∀ n, 0 ≤ a n)
    (hA : 0 < A)
    (hpow : Tendsto (fun n => a n ^ (n + 1)) atTop (𝓝 A)) :
    Tendsto (fun n => ((n + 1 : ℕ) : ℝ) * (a n - 1)) atTop (𝓝 (Real.log A)) := by
  let m : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let L : ℕ → ℝ := fun n => m n * Real.log (a n)
  have hL : Tendsto L atTop (𝓝 (Real.log A)) := by
    have hlog := hpow.log hA.ne'
    convert hlog using 1
    funext n
    exact (Real.log_pow (a n) (n + 1)).symm
  have hmTop : Tendsto m atTop atTop := by
    change Tendsto (Nat.cast ∘ fun n : ℕ => n + 1) atTop atTop
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hx : Tendsto (fun n => L n / m n) atTop (𝓝 0) := hL.div_atTop hmTop
  have hloga (n : ℕ) : Real.log (a n) = L n / m n := by
    dsimp [L, m]
    field_simp
  have hapos : ∀ᶠ n in atTop, 0 < a n := by
    have hp : ∀ᶠ n in atTop, 0 < a n ^ (n + 1) :=
      hpow.eventually (Ioi_mem_nhds hA)
    refine hp.mono ?_
    intro n hn
    rcases (ha n).eq_or_lt with hzero | hpos
    · rw [← hzero, zero_pow (Nat.succ_ne_zero n)] at hn
      exact (lt_irrefl 0 hn).elim
    · exact hpos
  have hrem : Tendsto
      (fun n => m n * (Real.exp (L n / m n) - 1 - L n / m n))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let C : ℝ := |Real.log A| + 1
    apply squeeze_zero' (g := fun n => C ^ 2 / m n)
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · have hC0 : 0 ≤ C := by dsimp [C]; positivity
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hL) 1 zero_lt_one
      have hC : ∀ᶠ n in atTop, |L n| ≤ C := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hdist := hN n hn
        rw [Real.dist_eq] at hdist
        dsimp [C]
        calc
          |L n| ≤ |L n - Real.log A| + |Real.log A| := by
            nth_rewrite 1 [show L n = (L n - Real.log A) + Real.log A by ring]
            exact abs_add_le _ _
          _ ≤ |Real.log A| + 1 := by linarith
      filter_upwards [hC, (show ∀ᶠ n in atTop, |L n / m n| ≤ 1 from
        (show Tendsto (fun n => |L n / m n|) atTop (𝓝 0) by
          simpa using hx.abs).eventually
          (eventually_le_nhds zero_lt_one))] with n hnL hsmall
      rw [Real.norm_eq_abs, abs_mul]
      have hmpos : 0 < m n := by dsimp [m]; positivity
      rw [abs_of_pos hmpos]
      calc
        m n * |Real.exp (L n / m n) - 1 - L n / m n| ≤
            m n * (L n / m n) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Real.abs_exp_sub_one_sub_id_le hsmall) hmpos.le
        _ = L n ^ 2 / m n := by field_simp
        _ ≤ C ^ 2 / m n := by
          apply (div_le_div_iff_of_pos_right hmpos).2
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) hC0).2 hnL
    · exact hmTop.const_div_atTop (C ^ 2)
  have hsum := hrem.add hL
  have heq : ∀ᶠ n in atTop,
      m n * (a n - 1) =
        m n * (Real.exp (L n / m n) - 1 - L n / m n) + L n := by
    filter_upwards [hapos] with n hn
    rw [← hloga n, Real.exp_log hn]
    dsimp [L, m]
    field_simp
    ring
  simpa [m] using hsum.congr' (Filter.EventuallyEq.symm heq)

theorem tendsto_one_add_pow_succ_real_of_tendsto {g : ℕ → ℝ} {z : ℝ}
    (h : Tendsto (fun n => ((n + 1 : ℕ) : ℝ) * g n) atTop (𝓝 z)) :
    Tendsto (fun n => (1 + g n) ^ (n + 1)) atTop (𝓝 (Real.exp z)) := by
  let g' : ℕ → ℝ
    | 0 => 0
    | n + 1 => g n
  have hshift : Tendsto (fun n => ((n + 1 : ℕ) : ℝ) * g' (n + 1))
      atTop (𝓝 z) := by
    simpa [g'] using h
  have hg' : Tendsto (fun n : ℕ => (n : ℝ) * g' n) atTop (𝓝 z) := by
    apply (Filter.tendsto_add_atTop_iff_nat
      (f := fun n : ℕ => (n : ℝ) * g' n) 1).mp
    simpa only [Nat.add_comm] using hshift
  have hp := Real.tendsto_one_add_pow_exp_of_tendsto hg'
  have hpShift : Tendsto (fun n => (1 + g' (n + 1)) ^ (n + 1))
      atTop (𝓝 (Real.exp z)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hp
  simpa [g'] using hpShift

theorem HasConvolutionPowerLimit.normSq_four_le_two
    {ρ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (h : HasConvolutionPowerLimit ρ φ) (t : ℝ) (htne : φ t ≠ 0) :
    Complex.normSq (φ t) ^ 4 ≤ Complex.normSq (φ (2 * t)) := by
  have htRaw := (Complex.continuous_normSq.continuousAt.tendsto.comp (h.2 t))
  have h2tRaw := (Complex.continuous_normSq.continuousAt.tendsto.comp (h.2 (2 * t)))
  have ht : Tendsto
      (fun n => Complex.normSq (charFun (ρ n : Measure ℝ) t) ^ (n + 1))
      atTop (𝓝 (Complex.normSq (φ t))) := by
    convert htRaw using 1
    funext n
    simp only [Function.comp_apply]
    exact (normSq_pow _ _).symm
  have h2t : Tendsto
      (fun n => Complex.normSq (charFun (ρ n : Measure ℝ) (2 * t)) ^ (n + 1))
      atTop (𝓝 (Complex.normSq (φ (2 * t)))) := by
    convert h2tRaw using 1
    funext n
    simp only [Function.comp_apply]
    exact (normSq_pow _ _).symm
  let a : ℕ → ℝ := fun n => Complex.normSq (charFun (ρ n : Measure ℝ) t)
  let b : ℕ → ℝ := fun n => Complex.normSq (charFun (ρ n : Measure ℝ) (2 * t))
  have hApos : 0 < Complex.normSq (φ t) := Complex.normSq_pos.mpr htne
  have hlinear := tendsto_nat_mul_sub_one_of_pow_tendsto
    (a := a) (A := Complex.normSq (φ t))
    (fun n => Complex.normSq_nonneg _) hApos (by simpa [a] using ht)
  have hscaled : Tendsto
      (fun n => ((n + 1 : ℕ) : ℝ) * (4 * (a n - 1))) atTop
      (𝓝 (4 * Real.log (Complex.normSq (φ t)))) := by
    convert hlinear.const_mul 4 using 1 <;> ring
  have hlower : Tendsto (fun n => (1 + 4 * (a n - 1)) ^ (n + 1)) atTop
      (𝓝 (Complex.normSq (φ t) ^ 4)) := by
    have hexp := tendsto_one_add_pow_succ_real_of_tendsto hscaled
    convert hexp using 1
    rw [show 4 * Real.log (Complex.normSq (φ t)) =
      Real.log (Complex.normSq (φ t) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hApos 4)]
  have hcomp : ∀ᶠ n in atTop,
      (1 + 4 * (a n - 1)) ^ (n + 1) ≤ b n ^ (n + 1) := by
    have haOne : Tendsto a atTop (𝓝 1) := by
      have hpowPos : Tendsto (fun n => a n ^ (n + 1)) atTop
          (𝓝 (Complex.normSq (φ t))) := by simpa [a] using ht
      have hlogLinear := tendsto_nat_mul_sub_one_of_pow_tendsto
        (a := a) (A := Complex.normSq (φ t))
        (fun n => Complex.normSq_nonneg _) hApos hpowPos
      have hmTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
        change Tendsto (Nat.cast ∘ fun n : ℕ => n + 1) atTop atTop
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      have := hlogLinear.div_atTop hmTop
      have hsub : Tendsto (fun n => a n - 1) atTop (𝓝 0) := by
        convert this using 1
        funext n
        have hmne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      simpa using hsub.add_const 1
    have hbaseNonneg : ∀ᶠ n in atTop, 0 ≤ 1 + 4 * (a n - 1) :=
      (haOne.eventually (eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1))).mono
        (fun _ hn => by linarith)
    filter_upwards [hbaseNonneg] with n hn
    have hab := one_sub_normSq_charFun_two_mul_le (ρ n) t
    have hab' : 1 + 4 * (a n - 1) ≤ b n := by
      dsimp [a, b]
      linarith
    exact pow_le_pow_left₀ hn hab' (n + 1)
  exact le_of_tendsto_of_tendsto hlower (by simpa [b] using h2t) hcomp

theorem HasConvolutionPowerLimit.nonvanishing
    {ρ : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (h : HasConvolutionPowerLimit ρ φ) (t : ℝ) : φ t ≠ 0 := by
  have hzero : φ 0 = 1 := h.zero
  have hneN : {s : ℝ | φ s ≠ 0} ∈ 𝓝 0 := by
    show ∀ᶠ s : ℝ in 𝓝 0, φ s ≠ 0
    have hev : ∀ᶠ z : ℂ in 𝓝 (φ 0), z ≠ 0 :=
      eventually_ne_nhds (by simp [hzero])
    exact h.1.eventually hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hneN
  obtain ⟨k, hk⟩ := exists_dyadic_upper (ε / 2) (half_pos hε) t
  let s : ℝ := t / (2 : ℝ) ^ k
  have hpowpos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hs : dist s 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpowpos]
    apply (div_lt_iff₀ hpowpos).2
    exact hk.trans_lt (by nlinarith [hpowpos])
  have hsne : φ s ≠ 0 := hball hs
  have hdyadic (j : ℕ) (u : ℝ) (hu : φ u ≠ 0) :
      φ ((2 : ℝ) ^ j * u) ≠ 0 := by
    induction j with
    | zero => simpa using hu
    | succ j ih =>
        have hprev := ih
        have hscale := h.normSq_four_le_two ((2 : ℝ) ^ j * u) hprev
        have hpos : 0 < Complex.normSq (φ ((2 : ℝ) ^ j * u)) ^ 4 :=
          pow_pos (Complex.normSq_pos.mpr hprev) 4
        have hnext : Complex.normSq (φ (2 * ((2 : ℝ) ^ j * u))) ≠ 0 := by
          exact ne_of_gt (hpos.trans_le hscale)
        have harg : (2 : ℝ) ^ (j + 1) * u = 2 * ((2 : ℝ) ^ j * u) := by
          rw [pow_succ]
          ring
        rw [harg]
        intro hφ
        apply hnext
        rw [hφ]
        simp
  have htarget := hdyadic k s hsne
  have harg : (2 : ℝ) ^ k * s = t := by
    dsimp [s]
    field_simp
  rwa [harg] at htarget

/-! ## Compatibility with linearized root limits -/

/-- A linearized root limit automatically supplies the convolution-power limit appearing on the
other side of Klenke's root-array criterion. -/
theorem HasLinearizedRootLimit.hasConvolutionPowerLimit
    {ρ : ℕ → ProbabilityMeasure ℝ} {ψ : ℝ → ℂ}
    (h : HasLinearizedRootLimit ρ ψ) :
    HasConvolutionPowerLimit ρ (fun t => Complex.exp (ψ t)) := by
  refine ⟨Complex.continuous_exp.continuousAt.comp h.1, ?_⟩
  exact h.tendsto_charFun_pow

/-- If a power limit and a linearized limit are both available for the same root array, the
probability law selected by the power limit is exactly the infinitely divisible unit-time law
selected by the linearized limit. -/
theorem HasConvolutionPowerLimit.limitLaw_eq_linearizedPowerLaw
    {ρ : ℕ → ProbabilityMeasure ℝ} {φ ψ : ℝ → ℂ}
    (hpow : HasConvolutionPowerLimit ρ φ)
    (hlin : HasLinearizedRootLimit ρ ψ)
    {μ : ProbabilityMeasure ℝ} (hμ : ∀ t, charFun (μ : Measure ℝ) t = φ t) :
    μ = hlin.powerLaw 1 := by
  have hφ : φ = fun t => Complex.exp (ψ t) :=
    hlin.powerLimit_eq_exp hpow.2
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [hμ t, hφ, hlin.charFun_powerLaw]
  simp

theorem HasConvolutionPowerLimit.isInfinitelyDivisible_limitLaw_of_linearized
    {ρ : ℕ → ProbabilityMeasure ℝ} {φ ψ : ℝ → ℂ}
    (hpow : HasConvolutionPowerLimit ρ φ)
    (hlin : HasLinearizedRootLimit ρ ψ)
    {μ : ProbabilityMeasure ℝ} (hμ : ∀ t, charFun (μ : Measure ℝ) t = φ t) :
    μ.IsInfinitelyDivisible := by
  rw [hpow.limitLaw_eq_linearizedPowerLaw hlin hμ]
  exact hlin.isInfinitelyDivisible_powerLaw_one

end ProbabilityTheory
