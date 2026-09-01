/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.CanonicalRootAsymptotics
public import StochLean.Probability.InfinitelyDivisible.LevyExtractionWeight
public import Mathlib.MeasureTheory.Measure.IntegralCharFun

/-!
# Finite-measure extraction for the converse Lévy--Khintchine theorem

This module divides finite weighted limits by the project-local extraction weight.  The result is
a genuine Lévy measure under the minimal StochLean predicate; sigma-finiteness remains derived.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology ProbabilityTheory Interval

namespace ProbabilityTheory
namespace LevyTriplet

/-- Remove the possible Gaussian atom at zero and divide by `1 - sinc x`. -/
noncomputable def extractedJumpMeasure (kappa : FiniteMeasure ℝ) : Measure ℝ :=
  ((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ).withDensity
    (fun x => ((extractionWeight x : ℝ≥0∞))⁻¹)

theorem extractedJumpMeasure_atom_zero (kappa : FiniteMeasure ℝ) :
    extractedJumpMeasure kappa {0} = 0 := by
  apply (withDensity_absolutelyContinuous _ _)
  rw [Measure.restrict_apply (MeasurableSet.singleton 0)]
  simp

/-- Dividing a finite measure away from zero by the extraction weight always yields a Lévy
measure. -/
theorem isLevyMeasure_extractedJumpMeasure (kappa : FiniteMeasure ℝ) :
    IsLevyMeasure (extractedJumpMeasure kappa) := by
  refine ⟨extractedJumpMeasure_atom_zero kappa, ?_⟩
  rw [extractedJumpMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      ((measurable_extractionWeight.coe_nnreal_ennreal).fun_inv)
      measurable_levyIntegrand]
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi ^ 2)
  have hCtop : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hpoint : ∀ x ≠ (0 : ℝ),
      ((extractionWeight x : ℝ≥0∞))⁻¹ * levyIntegrand x ≤ C := by
    intro x hx
    have hw0 : (extractionWeight x : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (extractionWeight_pos hx).ne'
    have hwtop : (extractionWeight x : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    have hlevtop : levyIntegrand x ≠ ∞ := by
      have hle : levyIntegrand x ≤ 1 := by
        exact min_le_left _ _
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hlev : levyIntegrand x ≤ C * (extractionWeight x : ℝ≥0∞) := by
      apply (ENNReal.toReal_le_toReal hlevtop (ENNReal.mul_ne_top hCtop hwtop)).mp
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
      exact levyIntegrand_toReal_le_extractionWeight x
    calc
      ((extractionWeight x : ℝ≥0∞))⁻¹ * levyIntegrand x ≤
          ((extractionWeight x : ℝ≥0∞))⁻¹ *
            (C * (extractionWeight x : ℝ≥0∞)) := by gcongr
      _ = C * (((extractionWeight x : ℝ≥0∞))⁻¹ *
            (extractionWeight x : ℝ≥0∞)) := by ac_rfl
      _ = C := by rw [ENNReal.inv_mul_cancel hw0 hwtop, mul_one]
  have hae : ∀ᵐ x ∂((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ),
      ((extractionWeight x : ℝ≥0∞))⁻¹ * levyIntegrand x ≤ C := by
    rw [ae_restrict_iff' (MeasurableSet.singleton 0).compl]
    filter_upwards [] with x hx
    exact hpoint x (by simpa using hx)
  refine lt_of_le_of_lt (lintegral_mono_ae hae) ?_
  calc
    (∫⁻ _x, C ∂((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ))
        = C * ((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ) Set.univ := by simp
    _ < ∞ := ENNReal.mul_lt_top hCtop.lt_top (measure_lt_top _ _)

/-- Reweighting the extracted jump measure recovers the finite measure away from zero. -/
theorem extractedJumpMeasure_withDensity_extractionWeight (kappa : FiniteMeasure ℝ) :
    (extractedJumpMeasure kappa).withDensity
        (fun x => (extractionWeight x : ℝ≥0∞)) =
      (kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ := by
  rw [extractedJumpMeasure]
  let mu := (kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ
  have hw : Measurable (fun x => (extractionWeight x : ℝ≥0∞)) :=
    measurable_extractionWeight.coe_nnreal_ennreal
  have hinv := hw.fun_inv
  rw [← withDensity_mul mu hinv hw]
  change mu.withDensity _ = mu
  have hone : mu.withDensity (1 : ℝ → ℝ≥0∞) = mu := withDensity_one
  apply Eq.trans (withDensity_congr_ae ?_) hone
  change ∀ᵐ x ∂((kappa : Measure ℝ).restrict ({0} : Set ℝ)ᶜ),
    (extractionWeight x : ℝ≥0∞)⁻¹ * (extractionWeight x : ℝ≥0∞) = 1
  rw [ae_restrict_iff' (MeasurableSet.singleton 0).compl]
  filter_upwards [] with x hx
  have hw0 : (extractionWeight x : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (extractionWeight_pos (by simpa using hx)).ne'
  exact ENNReal.inv_mul_cancel hw0 ENNReal.coe_ne_top

/-- A finite measure weighted by `1 - sinc x`.  This is the compact finite object used in the
converse Lévy--Khintchine extraction. -/
noncomputable def extractionMeasure (nu : FiniteMeasure ℝ) : Measure ℝ :=
  (nu : Measure ℝ).withDensity (fun x => (extractionWeight x : ℝ≥0∞))

instance instFiniteExtractionMeasure (nu : FiniteMeasure ℝ) :
    IsFiniteMeasure (extractionMeasure nu) := by
  apply IsFiniteMeasure.mk
  rw [extractionMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    ∫⁻ x, (extractionWeight x : ℝ≥0∞) ∂(nu : Measure ℝ) ≤
        ∫⁻ _ : ℝ, 2 ∂(nu : Measure ℝ) := by
      exact lintegral_mono fun x =>
        ENNReal.coe_le_coe.mpr (extractionWeight_le_two x)
    _ < ∞ := lintegral_const_lt_top (by norm_num)

/-- Bundled finite-measure version of `extractionMeasure`. -/
noncomputable def extractionFiniteMeasure (nu : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨extractionMeasure nu, instFiniteExtractionMeasure nu⟩

@[simp, norm_cast]
theorem coe_extractionFiniteMeasure (nu : FiniteMeasure ℝ) :
    (extractionFiniteMeasure nu : Measure ℝ) = extractionMeasure nu := rfl

private theorem intervalIntegral_exp_add_mul_I (t x : ℝ) :
    ∫ s in (-1 : ℝ)..1, Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
      2 * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * Real.sinc x := by
  have hsplit (s : ℝ) :
      Complex.ofReal ((t + s) * x) * Complex.I =
        Complex.ofReal (t * x) * Complex.I +
          Complex.ofReal (s * x) * Complex.I := by
    push_cast
    ring
  simp_rw [hsplit, Complex.exp_add]
  rw [intervalIntegral.integral_const_mul]
  rw [show 2 * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * Real.sinc x =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        (2 * Real.sinc x) by ring]
  congr 1
  by_cases hx : x = 0
  · subst x
    norm_num
  · have h := intervalIntegral.integral_deriv_smul_comp (E := ℂ)
        (a := (-1 : ℝ)) (b := 1) (f := fun s => x * s) (f' := fun _ => x)
        (g := fun u => Complex.exp (u * Complex.I)) ?_ (by fun_prop) (by fun_prop)
    swap
    · intro s hs
      simp_rw [mul_comm x]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, Complex.ofReal_mul, Complex.real_smul,
      intervalIntegral.integral_const_mul, mul_neg, one_mul] at h
    rw [integral_exp_mul_I_eq_sinc] at h
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    apply (mul_left_cancel₀ hxC)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Fourier transform of the extraction-weighted finite measure.  The `sinc` averaging identity
is proved internally by Fubini and interval integration. -/
theorem charFun_extractionMeasure (nu : FiniteMeasure ℝ) (t : ℝ) :
    charFun (extractionMeasure nu) t =
      charFun (nu : Measure ℝ) t -
        (2 : ℂ)⁻¹ * ∫ s in (-1 : ℝ)..1, charFun (nu : Measure ℝ) (t + s) := by
  have h_int : Integrable
      (Function.uncurry fun (s x : ℝ) =>
        Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod (nu : Measure ℝ)) := by
    simp only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← integrable_norm_iff (by fun_prop)]
    suffices (fun a => ‖Function.uncurry (fun (s x : ℝ) =>
        Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I)) a‖) = fun _ => 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    simp only [Function.uncurry_apply_pair, Complex.norm_exp_ofReal_mul_I]
  have havg :
      ∫ s in (-1 : ℝ)..1, charFun (nu : Measure ℝ) (t + s) =
        ∫ x, 2 * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * Real.sinc x
          ∂(nu : Measure ℝ) := by
    calc
      ∫ s in (-1 : ℝ)..1, charFun (nu : Measure ℝ) (t + s) =
          ∫ s in (-1 : ℝ)..1, ∫ x,
            Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) ∂(nu : Measure ℝ) := by
              simp_rw [charFun_apply_real]
              congr 1
              funext s
              apply integral_congr_ae
              filter_upwards [] with x
              congr 1
              push_cast
              ring
      _ = ∫ x, ∫ s in (-1 : ℝ)..1,
            Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I)
          ∂volume ∂(nu : Measure ℝ) := by
              rw [intervalIntegral_integral_swap h_int]
      _ = ∫ x, 2 * Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * Real.sinc x
          ∂(nu : Measure ℝ) := by
              congr with x
              exact intervalIntegral_exp_add_mul_I t x
  rw [charFun_apply_real, extractionMeasure,
    integral_withDensity_eq_integral_smul
      measurable_extractionWeight]
  rw [havg, charFun_apply_real]
  simp only [Complex.ofReal_mul]
  have hexp : Integrable (fun x : ℝ =>
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) (nu : Measure ℝ) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) <| ae_of_all _ fun x => by
      rw [show (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) by
        push_cast
        rfl]
      rw [Complex.norm_exp_ofReal_mul_I]
      norm_num
  have hsinc : Integrable (fun x : ℝ =>
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * Real.sinc x)
      (nu : Measure ℝ) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) <| ae_of_all _ fun x => by
      rw [norm_mul,
        show (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) by
          push_cast
          rfl,
        Complex.norm_exp_ofReal_mul_I]
      simpa using Real.abs_sinc_le_one x
  rw [show (fun x : ℝ => (extractionWeight x : ℝ≥0) •
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
      fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) -
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * Real.sinc x by
    funext x
    simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul,
      extractionWeight_coe]
    push_cast
    ring]
  rw [integral_sub hexp hsinc]
  rw [show (fun x : ℝ =>
      2 * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * Real.sinc x) =
      fun x : ℝ => 2 *
        (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) * Real.sinc x) by
          funext x
          ring]
  rw [integral_const_mul]
  ring

private theorem charFun_eq_integral_poissonExponentIntegrand_add_mass
    (nu : FiniteMeasure ℝ) (t : ℝ) :
    charFun (nu : Measure ℝ) t =
      ∫ x, poissonExponentIntegrand t x ∂(nu : Measure ℝ) + (nu.mass : ℂ) := by
  have hexp : Integrable (fun x : ℝ =>
      Complex.exp (((x * t : ℝ) : ℂ) * Complex.I)) (nu : Measure ℝ) := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) <| ae_of_all _ fun x => by
      rw [Complex.norm_exp_ofReal_mul_I]
      norm_num
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) (nu : Measure ℝ) :=
    integrable_const 1
  unfold poissonExponentIntegrand
  rw [integral_sub hexp hone, charFun_apply_real]
  have hmass : (∫ _ : ℝ, (1 : ℂ) ∂(nu : Measure ℝ)) = (nu.mass : ℂ) := by
    rw [integral_const]
    simp only [one_smul, Measure.real_def]
    rw [← @FiniteMeasure.ennreal_mass ℝ _ nu]
    rw [ENNReal.coe_toReal]
    simp
  rw [hmass]
  ring_nf
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  push_cast
  ring

/-- The extraction measure of the scaled canonical convolution root. -/
noncomputable def canonicalRootExtractionFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) :
    FiniteMeasure ℝ :=
  extractionFiniteMeasure (hμ.canonicalRootIntensity n)

/-- The Fourier transform of the canonical extraction measure is the sinc-average subtraction
of the root linearization. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.charFun_canonicalRootExtractionFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) (t : ℝ) :
    charFun (canonicalRootExtractionFiniteMeasure hμ n : Measure ℝ) t =
      canonicalRootLinearization hμ n t -
        (2 : ℂ)⁻¹ * ∫ s in (-1 : ℝ)..1,
          canonicalRootLinearization hμ n (t + s) := by
  rw [canonicalRootExtractionFiniteMeasure, coe_extractionFiniteMeasure,
    charFun_extractionMeasure]
  rw [charFun_eq_integral_poissonExponentIntegrand_add_mass,
    ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity
      hμ]
  simp_rw [charFun_eq_integral_poissonExponentIntegrand_add_mass,
    ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.integral_poissonExponentIntegrand_canonicalRootIntensity
      hμ]
  have hlin : IntervalIntegrable
      (fun s : ℝ => canonicalRootLinearization hμ n (t + s)) volume (-1) 1 := by
    have hc : Continuous
        (fun s : ℝ => canonicalRootLinearization hμ n (t + s)) := by
      unfold canonicalRootLinearization
      fun_prop
    exact hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hlin intervalIntegrable_const]
  simp
  ring

/-- The limiting Fourier transform of the extraction measures. -/
noncomputable def canonicalRootExtractionLimitChar
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) : ℂ :=
  hμ.exponent t - (2 : ℂ)⁻¹ *
    ∫ s in (-1 : ℝ)..1, hμ.exponent (t + s)

private theorem continuous_canonicalRootLinearization
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (n : ℕ) :
    Continuous (canonicalRootLinearization hμ n) := by
  unfold canonicalRootLinearization
  fun_prop

/-- Canonical-root linearizations converge under integration on the fixed averaging interval. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_intervalIntegral_canonicalRootLinearization
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto
      (fun n => ∫ s in (-1 : ℝ)..1, canonicalRootLinearization hμ n (t + s))
      atTop (nhds (∫ s in (-1 : ℝ)..1, hμ.exponent (t + s))) := by
  have hcont : Continuous (fun s : ℝ => hμ.exponent (t + s)) := by fun_prop
  rcases isCompact_uIcc.bddAbove_image hcont.norm.continuousOn with ⟨B, hB⟩
  let C : ℝ := max B 1
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hpsi (s : ℝ) (hs : s ∈ Set.uIcc (-1 : ℝ) 1) :
      ‖hμ.exponent (t + s)‖ ≤ C := by
    exact (hB ⟨s, hs, rfl⟩).trans (le_max_left B 1)
  obtain ⟨N, hN⟩ := exists_nat_ge C
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 2 * C)
  case hF_meas =>
    exact Filter.Eventually.of_forall fun n =>
      ((continuous_canonicalRootLinearization hμ n).comp
        (continuous_const.add continuous_id)).aestronglyMeasurable
  case h_bound =>
    filter_upwards [eventually_ge_atTop N] with n hn
    apply ae_of_all
    intro s hs
    have hs' : s ∈ Set.uIcc (-1 : ℝ) 1 := Set.uIoc_subset_uIcc hs
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hCn : C ≤ (n + 1 : ℝ) := by
      exact hN.trans (hNn.trans (by norm_num))
    have hden : 0 < (n + 1 : ℝ) := by positivity
    have hsmall :
        ‖hμ.exponent (t + s) / ((n + 1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (div_le_one hden).2 ((hpsi s hs').trans hCn)
    rw [canonicalRootLinearization, hμ.charFun_nthRoot, norm_mul]
    have hexp := Complex.norm_exp_sub_one_le hsmall
    calc
      ‖((n + 1 : ℕ) : ℂ)‖ *
          ‖Complex.exp (hμ.exponent (t + s) / ((n + 1 : ℕ) : ℂ)) - 1‖ ≤
          ‖((n + 1 : ℕ) : ℂ)‖ *
            (2 * ‖hμ.exponent (t + s) / ((n + 1 : ℕ) : ℂ)‖) := by
              gcongr
      _ = 2 * ‖hμ.exponent (t + s)‖ := by
            rw [norm_div, Complex.norm_natCast]
            field_simp
      _ ≤ 2 * C := by gcongr; exact hpsi s hs'
  case bound_integrable =>
    exact intervalIntegrable_const
  case h_lim =>
    exact ae_of_all _ fun s hs =>
      ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
        hμ (t + s)

theorem continuous_canonicalRootExtractionLimitChar
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    Continuous (canonicalRootExtractionLimitChar hμ) := by
  unfold canonicalRootExtractionLimitChar
  apply hμ.exponent.continuous.sub
  apply continuous_const.mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t s : ℝ => hμ.exponent (t + s)) (by fun_prop) (-1) 1

/-- Fourier convergence of the finite extraction measures. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_charFun_canonicalRootExtractionFiniteMeasure
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) (t : ℝ) :
    Tendsto
      (fun n => charFun (canonicalRootExtractionFiniteMeasure hμ n : Measure ℝ) t)
      atTop (nhds (canonicalRootExtractionLimitChar hμ t)) := by
  rw [show (fun n =>
      charFun (canonicalRootExtractionFiniteMeasure hμ n : Measure ℝ) t) =
      fun n => canonicalRootLinearization hμ n t -
        (2 : ℂ)⁻¹ * ∫ s in (-1 : ℝ)..1,
          canonicalRootLinearization hμ n (t + s) by
    funext n
    exact hμ.charFun_canonicalRootExtractionFiniteMeasure n t]
  exact (ProbabilityTheory.ProbabilityMeasure.IsInfinitelyDivisible.tendsto_canonicalRootLinearization
      hμ t).sub
    (tendsto_const_nhds.mul (hμ.tendsto_intervalIntegral_canonicalRootLinearization t))

/-- The actual finite measure extracted from every infinitely divisible law. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.exists_canonicalRootExtractionLimit
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsInfinitelyDivisible) :
    ∃ kappa : FiniteMeasure ℝ,
      (∀ t, charFun (kappa : Measure ℝ) t = canonicalRootExtractionLimitChar hμ t) ∧
      Tendsto (canonicalRootExtractionFiniteMeasure hμ) atTop (nhds kappa) := by
  apply exists_finiteMeasure_of_tendsto_charFun'
    (continuous_canonicalRootExtractionLimitChar hμ).continuousAt
  exact hμ.tendsto_charFun_canonicalRootExtractionFiniteMeasure

end LevyTriplet
end ProbabilityTheory
