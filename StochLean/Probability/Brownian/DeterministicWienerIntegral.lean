/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Internal.Brownian.Wiener.Indicator

/-!
# Deterministic Wiener integral

This module owns the basis-independent first Gaussian-chaos integral associated with a
pre-Brownian process.  Its domain is the genuine `L²` quotient for Lebesgue measure restricted to
`(0, T]`; its codomain is `L²(Ω, P)`.  The construction first integrates finite linear
combinations of interval indicators and then extends the resulting isometry by density.

This is a deterministic Wiener integral, not the Itô integral for random predictable integrands.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

/-- The basis-independent deterministic Wiener integral as a linear isometry. -/
protected noncomputable def IsPreBrownianReal.deterministicWienerIntegral
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  exact
    { (DeterministicWiener.integral B hB T).toLinearMap with
      norm_map' := DeterministicWiener.norm_integral hB T }

@[simp]
theorem IsPreBrownianReal.deterministicWienerIntegral_apply
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    hB.deterministicWienerIntegral T f =
      DeterministicWiener.integral B hB T f := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  rfl

/-- The deterministic Wiener integral has the exact `L²` norm of its integrand. -/
theorem IsPreBrownianReal.norm_deterministicWienerIntegral
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ‖hB.deterministicWienerIntegral T f‖ = ‖f‖ :=
  (hB.deterministicWienerIntegral T).norm_map f

/-- Integral form of the deterministic Wiener isometry. -/
theorem IsPreBrownianReal.integral_sq_deterministicWienerIntegral
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∫ ω, (hB.deterministicWienerIntegral T f ω) ^ 2 ∂P =
      ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  simpa only [hB.deterministicWienerIntegral_apply] using
    DeterministicWiener.integral_sq hB T f

/-- A deterministic Wiener integral is centered Gaussian, with variance equal to the squared
`L²` norm of the integrand. -/
theorem IsPreBrownianReal.hasLaw_deterministicWienerIntegral
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    HasLaw (fun ω ↦ hB.deterministicWienerIntegral T f ω)
      (gaussianReal 0
        (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume).toNNReal) P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  simpa only [hB.deterministicWienerIntegral_apply] using
    DeterministicWiener.integral_hasLaw_gaussian hB T f

/-- Polarized deterministic Wiener isometry.  The covariance of two first-chaos integrals is the
`L²` inner product of their deterministic integrands. -/
theorem IsPreBrownianReal.covariance_deterministicWienerIntegral
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    cov[(fun ω ↦ hB.deterministicWienerIntegral T f ω),
        (fun ω ↦ hB.deterministicWienerIntegral T g ω); P] =
      ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), f s * g s ∂volume := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hfmean : P[fun ω ↦ hB.deterministicWienerIntegral T f ω] = 0 := by
    rw [(hB.hasLaw_deterministicWienerIntegral T f).integral_eq,
      integral_id_gaussianReal]
  have hgmean : P[fun ω ↦ hB.deterministicWienerIntegral T g ω] = 0 := by
    rw [(hB.hasLaw_deterministicWienerIntegral T g).integral_eq,
      integral_id_gaussianReal]
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hfmean, hgmean]
  have hinner := (hB.deterministicWienerIntegral T).inner_map_map f g
  rw [L2.inner_def, L2.inner_def] at hinner
  simpa only [Pi.mul_apply, RCLike.inner_apply, conj_trivial, one_mul, mul_zero, sub_zero,
    mul_comm]
    using hinner

/-- The integral of an interval indicator is the corresponding Brownian increment in `L²(P)`.
This pins the extension to its defining step-function semantics. -/
theorem IsPreBrownianReal.deterministicWienerIntegral_stepIndicator
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (i : DeterministicWiener.StepIndex T) :
    hB.deterministicWienerIntegral T (DeterministicWiener.stepIndicatorLp T i) =
      DeterministicWiener.incrementLp B hB i := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  simpa only [hB.deterministicWienerIntegral_apply] using
    DeterministicWiener.integral_stepIndicator hB T i

/-- Expansion in an arbitrary Hilbert basis converges in `L²(P)` to the deterministic Wiener
integral.  This is the generic ONB regime; it does not assert almost-sure uniform convergence of
Brownian path approximants, which is special to the Haar--Schauder construction. -/
theorem IsPreBrownianReal.hasSum_deterministicWienerIntegral_hilbertBasis
    {ι : Type*} (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (e : HilbertBasis ι ℝ (Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    HasSum (fun i ↦ e.repr f i • hB.deterministicWienerIntegral T (e i))
      (hB.deterministicWienerIntegral T f) := by
  convert (e.hasSum_repr f).map (hB.deterministicWienerIntegral T)
    (hB.deterministicWienerIntegral T).continuous using 1
  funext i
  simp only [Function.comp_apply, map_smul, hB.deterministicWienerIntegral_apply]

/-- For a Brownian process, use its pre-Brownian finite-dimensional law to construct the
deterministic Wiener integral. -/
protected noncomputable def IsBrownianReal.deterministicWienerIntegral
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  hB.toIsPreBrownianReal.deterministicWienerIntegral T

@[simp]
theorem IsBrownianReal.deterministicWienerIntegral_apply
    (hB : IsBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    hB.deterministicWienerIntegral T f =
      hB.toIsPreBrownianReal.deterministicWienerIntegral T f := rfl

end ProbabilityTheory
