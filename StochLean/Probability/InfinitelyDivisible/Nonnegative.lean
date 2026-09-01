/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Basic
public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Nonnegative convolution semigroups

Support propagation and rational-time approximation for real convolution semigroups.  These
results implement the nonnegative closure part of Klenke Exercises 14.4.3--14.4.4.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

noncomputable def rationalFloorApprox (u t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ≥0) * (u / ((n : ℝ≥0) + 1))

theorem IsConvolutionSemigroup.isNonnegativeLaw_rationalFloorApprox
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsConvolutionSemigroup ν)
    {u : ℝ≥0} (hu : 0 < u) (huLaw : ProbabilityMeasure.IsNonnegativeLaw (ν u))
    (t : ℝ≥0) (n : ℕ) :
    ProbabilityMeasure.IsNonnegativeLaw (ν (rationalFloorApprox u t n)) := by
  have hrootPow := hν.convPow_root u n
  have hroot : ProbabilityMeasure.IsNonnegativeLaw (ν (u / (n + 1 : ℕ))) :=
    MeasureTheory.ProbabilityMeasure.IsNonnegativeLaw.of_convPow
      (μ := ν (u / (n + 1 : ℕ))) (n := n + 1) (Nat.succ_pos n) (by
      simpa only [Nat.cast_add, Nat.cast_one] using hrootPow ▸ huLaw)
  by_cases hk : ⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ = 0
  · have htime : rationalFloorApprox u t n = 0 := by
      rw [rationalFloorApprox, hk]
      simp
    rw [htime]
    rw [hν.zero_eq_pointMass_real]
    exact (ProbabilityMeasure.isNonnegativeLaw_pointMass_iff 0).2 le_rfl
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hpow := hroot.convPow (j + 1)
    rw [hν.convPow_succ] at hpow
    rw [rationalFloorApprox, hj]
    simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hpow

theorem tendsto_rationalFloorApprox (u t : ℝ≥0) (hu : 0 < u) :
    Tendsto (rationalFloorApprox u t) atTop (nhds t) := by
  rw [← NNReal.tendsto_coe]
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    by simpa [Function.comp_def] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hb : Tendsto (fun n : ℕ => (u : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hl : Tendsto (fun n : ℕ => (t : ℝ) - (u : ℝ) / ((n : ℝ) + 1))
      atTop (nhds (t : ℝ)) := by
    convert tendsto_const_nhds.sub hb using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [] with n
    have hxlt : ((n : ℝ≥0) + 1) * (t / u) <
        (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ≥0) + 1 :=
      Nat.lt_floor_add_one _
    have hnpos : 0 < ((n : ℝ) + 1) := by positivity
    have hueq : (u : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hu.ne'
    change (t : ℝ) - (u : ℝ) / ((n : ℝ) + 1) ≤
      (rationalFloorApprox u t n : ℝ)
    rw [rationalFloorApprox]
    push_cast
    have hxltR : ((n : ℝ) + 1) * ((t : ℝ) / (u : ℝ)) <
        (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) + 1 := by exact_mod_cast hxlt
    apply (sub_le_iff_le_add).2
    calc
      (t : ℝ) ≤ ((⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) + 1) *
          ((u : ℝ) / ((n : ℝ) + 1)) := by
        apply (le_of_lt ?_)
        calc
          (t : ℝ) = (((n : ℝ) + 1) * ((t : ℝ) / (u : ℝ))) *
              ((u : ℝ) / ((n : ℝ) + 1)) := by field_simp
          _ < ((⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) + 1) *
              ((u : ℝ) / ((n : ℝ) + 1)) := by
            gcongr
      _ = (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) *
          ((u : ℝ) / ((n : ℝ) + 1)) +
          (u : ℝ) / ((n : ℝ) + 1) := by ring
  · filter_upwards [] with n
    have hfloor : (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ≥0) ≤
        ((n : ℝ≥0) + 1) * (t / u) := Nat.floor_le (by positivity)
    have hnpos : 0 < ((n : ℝ) + 1) := by positivity
    have hueq : (u : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hu.ne'
    change (rationalFloorApprox u t n : ℝ) ≤ (t : ℝ)
    rw [rationalFloorApprox]
    push_cast
    have hfloorR : (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) ≤
        ((n : ℝ) + 1) * ((t : ℝ) / (u : ℝ)) := by
      exact_mod_cast hfloor
    calc
      (⌊((n : ℝ≥0) + 1) * (t / u)⌋₊ : ℝ) *
          ((u : ℝ) / ((n : ℝ) + 1)) ≤
          (((n : ℝ) + 1) * ((t : ℝ) / (u : ℝ))) *
            ((u : ℝ) / ((n : ℝ) + 1)) := by gcongr
      _ = (t : ℝ) := by field_simp

theorem IsContinuousConvolutionSemigroup.isNonnegativeLaw_of_one
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsContinuousConvolutionSemigroup ν)
    {u : ℝ≥0} (hu : 0 < u) (huLaw : ProbabilityMeasure.IsNonnegativeLaw (ν u))
    (t : ℝ≥0) : ProbabilityMeasure.IsNonnegativeLaw (ν t) := by
  apply ProbabilityMeasure.IsNonnegativeLaw.tendsto
    (hν.continuous_real.continuousAt.tendsto.comp (tendsto_rationalFloorApprox u t hu))
  exact fun n => hν.isConvolutionSemigroup.isNonnegativeLaw_rationalFloorApprox hu huLaw t n

/-! ## Automatic continuity of nonnegative semigroups -/

/-- The Laplace transform at one.  This single value detects concentration at zero for laws
supported by the nonnegative half-line. -/
noncomputable def nonnegativeLaplace (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, Real.exp (-x) ∂(μ : Measure ℝ)

theorem integrable_exp_neg_of_isNonnegativeLaw {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) : Integrable (fun x : ℝ => Real.exp (-x)) (μ : Measure ℝ) := by
  apply (integrable_const (μ := (μ : Measure ℝ)) (1 : ℝ)).mono'
  · fun_prop
  · filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr hx)

theorem nonnegativeLaplace_pos {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw) :
    0 < nonnegativeLaplace μ := by
  exact integral_exp_pos (integrable_exp_neg_of_isNonnegativeLaw hμ)

theorem nonnegativeLaplace_le_one {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw) :
    nonnegativeLaplace μ ≤ 1 := by
  rw [show (1 : ℝ) = ∫ _ : ℝ, 1 ∂(μ : Measure ℝ) by simp]
  apply integral_mono_ae (integrable_exp_neg_of_isNonnegativeLaw hμ) (integrable_const 1)
  filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
  exact (Real.exp_le_one_iff).2 (neg_nonpos.mpr hx)

theorem nonnegativeLaplace_conv {μ ν : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) (hν : ν.IsNonnegativeLaw) :
    nonnegativeLaplace (μ.conv ν) = nonnegativeLaplace μ * nonnegativeLaplace ν := by
  rw [nonnegativeLaplace, ProbabilityMeasure.coe_conv,
    integral_conv (integrable_exp_neg_of_isNonnegativeLaw (hμ.conv hν))]
  simp only [neg_add_rev, Real.exp_add, integral_mul_const, integral_const_mul]
  simp only [nonnegativeLaplace, mul_comm]

/-- The Laplace transform of a nonnegative convolution power is the corresponding ordinary
power.  This public law-level form is used by the nonnegative Lévy--Khintchine extraction. -/
theorem nonnegativeLaplace_convPow {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) (n : ℕ) :
    nonnegativeLaplace (μ.convPow n) = nonnegativeLaplace μ ^ n := by
  induction n with
  | zero =>
      simp [ProbabilityMeasure.convPow, nonnegativeLaplace,
        ProbabilityMeasure.coe_pointMass]
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ,
        nonnegativeLaplace_conv (hμ.convPow n) hμ, ih, pow_succ]

theorem IsNonnegativeConvolutionSemigroup.nonnegativeLaplace_add
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν)
    (s t : ℝ≥0) :
    nonnegativeLaplace (ν (s + t)) =
      nonnegativeLaplace (ν s) * nonnegativeLaplace (ν t) := by
  rw [hν.isConvolutionSemigroup.add]
  exact nonnegativeLaplace_conv (hν.isNonnegativeLaw s) (hν.isNonnegativeLaw t)

theorem IsNonnegativeConvolutionSemigroup.antitone_nonnegativeLaplace
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν) :
    Antitone (fun t => nonnegativeLaplace (ν t)) := by
  intro s t hst
  change nonnegativeLaplace (ν t) ≤ nonnegativeLaplace (ν s)
  rw [show t = s + (t - s) by exact (add_tsub_cancel_of_le hst).symm]
  rw [hν.nonnegativeLaplace_add]
  have hp := nonnegativeLaplace_pos (hν.isNonnegativeLaw s)
  exact mul_le_of_le_one_right hp.le
    (nonnegativeLaplace_le_one (hν.isNonnegativeLaw (t - s)))

theorem IsNonnegativeConvolutionSemigroup.nonnegativeLaplace_root_pow
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν)
    (u : ℝ≥0) (n : ℕ) :
    nonnegativeLaplace (ν (u / (n + 1 : ℕ))) ^ (n + 1) = nonnegativeLaplace (ν u) := by
  have hp := hν.isConvolutionSemigroup.convPow_root u n
  have hLap := congrArg nonnegativeLaplace hp
  rw [nonnegativeLaplace_convPow
    (hν.isNonnegativeLaw (u / ((n : ℝ≥0) + 1))) (n + 1)] at hLap
  simpa only [Nat.cast_add, Nat.cast_one] using hLap

theorem IsNonnegativeConvolutionSemigroup.tendsto_nonnegativeLaplace_roots_one
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν)
    (u : ℝ≥0) :
    Tendsto (fun n : ℕ => nonnegativeLaplace (ν (u / (n + 1 : ℕ)))) atTop (𝓝 1) := by
  have hformula (n : ℕ) :
      nonnegativeLaplace (ν (u / (n + 1 : ℕ))) =
        nonnegativeLaplace (ν u) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    have hp := hν.nonnegativeLaplace_root_pow u n
    have hroot := Real.pow_rpow_inv_natCast
      (nonnegativeLaplace_pos (hν.isNonnegativeLaw (u / (n + 1 : ℕ)))).le
      (Nat.succ_ne_zero n)
    calc
      nonnegativeLaplace (ν (u / (n + 1 : ℕ))) =
          (nonnegativeLaplace (ν (u / (n + 1 : ℕ))) ^ (n + 1)) ^
            (((n + 1 : ℕ) : ℝ)⁻¹) := hroot.symm
      _ = nonnegativeLaplace (ν u) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by rw [hp]
  simp_rw [hformula]
  have hden : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  convert (Real.continuousAt_const_rpow
    (nonnegativeLaplace_pos (hν.isNonnegativeLaw u)).ne').tendsto.comp hinv using 1
  · rfl
  · simp only [Real.rpow_zero]

theorem IsNonnegativeConvolutionSemigroup.tendsto_nonnegativeLaplace_zero
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν) :
    Tendsto (fun t => nonnegativeLaplace (ν t))
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hroots := hν.tendsto_nonnegativeLaplace_roots_one 1
    have hev : ∀ᶠ n : ℕ in atTop,
        a < nonnegativeLaplace (ν (1 / (n + 1 : ℕ))) :=
      (tendsto_order.1 hroots).1 a ha
    obtain ⟨n, hn⟩ := hev.exists
    have hδ : 0 < (1 / (n + 1 : ℕ) : ℝ≥0) := by positivity
    have hnear : Set.Iio (1 / (n + 1 : ℕ) : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0) :=
      Iio_mem_nhds hδ
    have hevent : ∀ᶠ t : ℝ≥0 in nhdsWithin (0 : ℝ≥0) (Set.Ioi 0),
        t ∈ Set.Iio (1 / (n + 1 : ℕ) : ℝ≥0) :=
      Filter.Eventually.filter_mono inf_le_left hnear
    filter_upwards [hevent] with t ht
    exact hn.trans_le (hν.antitone_nonnegativeLaplace ht.le)
  · intro b hb
    filter_upwards [] with t
    exact (nonnegativeLaplace_le_one (hν.isNonnegativeLaw t)).trans_lt hb

noncomputable def nonnegativeLaplaceDefect (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, 1 - Real.exp (-x) ∂(μ : Measure ℝ)

theorem nonnegativeLaplaceDefect_eq {μ : ProbabilityMeasure ℝ}
    (hμ : μ.IsNonnegativeLaw) :
    nonnegativeLaplaceDefect μ = 1 - nonnegativeLaplace μ := by
  rw [nonnegativeLaplaceDefect, nonnegativeLaplace, integral_sub
    (integrable_const 1) (integrable_exp_neg_of_isNonnegativeLaw hμ)]
  simp

theorem mul_measureReal_Ici_le_nonnegativeLaplaceDefect
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonnegativeLaw)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (1 - Real.exp (-ε)) * (μ : Measure ℝ).real (Set.Ici ε) ≤
      nonnegativeLaplaceDefect μ := by
  let c := 1 - Real.exp (-ε)
  let f : ℝ → ℝ := (Set.Ici ε).indicator (fun _ => c)
  have hfint : Integrable f (μ : Measure ℝ) := by
    exact (integrable_const (μ := (μ : Measure ℝ)) c).indicator measurableSet_Ici
  have hgint : Integrable (fun x : ℝ => 1 - Real.exp (-x)) (μ : Measure ℝ) :=
    (integrable_const 1).sub (integrable_exp_neg_of_isNonnegativeLaw hμ)
  have hle : f ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => 1 - Real.exp (-x)) := by
    filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae μ |>.mp hμ] with x hx
    simp only [f, Set.indicator_apply]
    split_ifs with hxe
    · exact sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hxe)) 1
    · exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 (neg_nonpos.mpr hx))
  have hi := integral_mono_ae hfint hgint hle
  rw [show ∫ x, f x ∂(μ : Measure ℝ) =
      (μ : Measure ℝ).real (Set.Ici ε) * c by
    dsimp [f]
    rw [integral_indicator measurableSet_Ici, setIntegral_const]
    simp [smul_eq_mul]] at hi
  simpa only [c, nonnegativeLaplaceDefect, mul_comm] using hi

theorem IsNonnegativeConvolutionSemigroup.tendsto_measureReal_Ici_zero
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t => (ν t : Measure ℝ).real (Set.Ici ε))
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 0) := by
  let c := 1 - Real.exp (-ε)
  have hc : 0 < c := sub_pos.mpr ((Real.exp_lt_one_iff).2 (neg_neg_of_pos hε))
  have hdefect : Tendsto (fun t => nonnegativeLaplaceDefect (ν t))
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 0) := by
    have hL := hν.tendsto_nonnegativeLaplace_zero
    have heq : (fun t => nonnegativeLaplaceDefect (ν t)) =
        (fun t => 1 - nonnegativeLaplace (ν t)) := by
      funext t
      exact nonnegativeLaplaceDefect_eq (hν.isNonnegativeLaw t)
    rw [heq]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hL
  apply squeeze_zero (f := fun t => (ν t : Measure ℝ).real (Set.Ici ε))
    (g := fun t => nonnegativeLaplaceDefect (ν t) / c)
  · exact fun _ => measureReal_nonneg
  · intro t
    apply (le_div_iff₀ hc).2
    simpa only [c, mul_comm] using
      (mul_measureReal_Ici_le_nonnegativeLaplaceDefect (hν.isNonnegativeLaw t) hε.le)
  · simpa [div_eq_mul_inv, mul_comm] using hdefect.const_mul c⁻¹

theorem IsNonnegativeConvolutionSemigroup.tendsto_measure_Ici_zero
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun t => (ν t : Measure ℝ) (Set.Ici ε))
      (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun t => measure_ne_top _ _)).mp
  simpa only [Measure.real] using hν.tendsto_measureReal_Ici_zero hε

/-- Every nonnegative convolution semigroup is automatically weakly continuous at zero. -/
theorem IsNonnegativeConvolutionSemigroup.tendsto_zero
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν) :
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0))
      (𝓝 (ProbabilityMeasure.pointMass (0 : ℝ))) := by
  let L := nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)
  letI : NeBot L := nhdsWithin_Ioi_neBot le_rfl
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  by_cases h0F : 0 ∈ F
  · have hle : ∀ᶠ t : ℝ≥0 in L, (ν t : Measure ℝ) F ≤ (1 : ℝ≥0∞) :=
      .of_forall fun t => by
        calc
          (ν t : Measure ℝ) F ≤ (ν t : Measure ℝ) Set.univ := measure_mono (Set.subset_univ F)
          _ = 1 := measure_univ
    have hlim : limsup (fun t => (ν t : Measure ℝ) F) L ≤ 1 :=
      limsup_le_of_le (by isBoundedDefault) hle
    simpa [ProbabilityMeasure.coe_pointMass, Measure.dirac_apply' 0 hF.measurableSet,
      h0F] using hlim
  · have hopen : IsOpen Fᶜ := hF.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.1 hopen) 0 h0F
    have htail := hν.tendsto_measure_Ici_zero hε
    have hmeasure_le (t : ℝ≥0) :
        (ν t : Measure ℝ) F ≤ (ν t : Measure ℝ) (Set.Ici ε) := by
      apply measure_mono_ae
      filter_upwards [ProbabilityMeasure.isNonnegativeLaw_iff_ae (ν t) |>.mp
        (hν.isNonnegativeLaw t)] with x hx
      intro hxF
      by_contra hxε
      have hxlt : x < ε := lt_of_not_ge hxε
      have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hx]
        exact hxlt
      exact (hball hxball) hxF
    have hFzero : Tendsto (fun t => (ν t : Measure ℝ) F) L (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
      · exact .of_forall fun _ => bot_le
      · exact .of_forall hmeasure_le
    have hlim : limsup (fun t => (ν t : Measure ℝ) F) L = 0 := hFzero.limsup_eq
    simpa [hlim, ProbabilityMeasure.coe_pointMass,
      Measure.dirac_apply' 0 hF.measurableSet, h0F]

/-- Automatic continuity: no continuity assumption is hidden in the basic nonnegative semigroup
predicate. -/
theorem IsNonnegativeConvolutionSemigroup.isContinuous
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsNonnegativeConvolutionSemigroup ν) :
    IsContinuousConvolutionSemigroup ν :=
  ⟨hν.isConvolutionSemigroup, hν.tendsto_zero⟩

end ProbabilityTheory
