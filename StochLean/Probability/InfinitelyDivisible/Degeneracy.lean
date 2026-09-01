/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Bounds
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Degeneracy detected by characteristic functions

Unit modulus at every frequency forces a real probability law to be a point mass.  The proof is
measure-theoretic: equality in the unit-circle expectation is established through a vanishing
nonnegative integral, and two incommensurable frequencies isolate a single real point.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory

theorem charFun_ae_eq_of_norm_eq_one (μ : ProbabilityMeasure ℝ) (t : ℝ)
    (h : ‖charFun (μ : Measure ℝ) t‖ = 1) :
    (fun x : ℝ ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =ᵐ[(μ : Measure ℝ)]
      (fun _ ↦ charFun (μ : Measure ℝ) t) := by
  let f : ℝ → ℂ := fun x ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  let c : ℂ := charFun (μ : Measure ℝ) t
  have hcSq : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  have hfNorm (x : ℝ) : ‖f x‖ = 1 := by
    dsimp [f]
    exact Complex.norm_exp_ofReal_mul_I (t * x)
  have hfInt : Integrable f (μ : Measure ℝ) := by
    apply (integrable_const (1 : ℂ)).mono (by fun_prop)
    exact ae_of_all _ fun x ↦ by simp [hfNorm]
  let q : ℝ → ℝ := fun x ↦ ((f x) * starRingEnd ℂ c).re
  have hqInt : Integrable q (μ : Measure ℝ) :=
    (hfInt.mul_const (starRingEnd ℂ c)).re
  have hqIntegral : (∫ x, q x ∂(μ : Measure ℝ)) = 1 := by
    calc
      (∫ x, q x ∂(μ : Measure ℝ)) =
          ((∫ x, f x * starRingEnd ℂ c ∂(μ : Measure ℝ)) : ℂ).re := by
            change (∫ x, RCLike.re (f x * starRingEnd ℂ c) ∂(μ : Measure ℝ)) =
              RCLike.re (∫ x, f x * starRingEnd ℂ c ∂(μ : Measure ℝ))
            exact integral_re (hfInt.mul_const (starRingEnd ℂ c))
      _ = ((∫ x, f x ∂(μ : Measure ℝ)) * starRingEnd ℂ c).re := by
            rw [integral_mul_const]
      _ = (c * starRingEnd ℂ c).re := by simp [f, c, charFun_apply_real]
      _ = 1 := by rw [Complex.mul_conj, hcSq]; norm_num
  let g : ℝ → ℝ := fun x ↦ Complex.normSq (f x - c)
  have hgEq (x : ℝ) : g x = 2 - 2 * q x := by
    rw [show g x = Complex.normSq (f x - c) by rfl, Complex.normSq_sub,
      show Complex.normSq (f x) = 1 by
        rw [Complex.normSq_eq_norm_sq, hfNorm]; norm_num,
      hcSq]
    simp only [q]
    ring
  have hgInt : Integrable g (μ : Measure ℝ) := by
    have hconst : Integrable (fun _ : ℝ ↦ (2 : ℝ)) (μ : Measure ℝ) :=
      integrable_const 2
    have hmul : Integrable (fun x ↦ 2 * q x) (μ : Measure ℝ) := hqInt.const_mul 2
    have hi : Integrable (fun x ↦ 2 - 2 * q x) (μ : Measure ℝ) := hconst.sub hmul
    apply hi.congr
    exact ae_of_all _ fun x ↦ (hgEq x).symm
  have hgIntegral : (∫ x, g x ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_congr_ae (ae_of_all _ hgEq),
      integral_sub (integrable_const 2) (hqInt.const_mul 2), integral_const,
      integral_const_mul, hqIntegral]
    norm_num
  have hgZero : g =ᵐ[(μ : Measure ℝ)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ Complex.normSq_nonneg _) hgInt).mp hgIntegral
  filter_upwards [hgZero] with x hx
  have : f x - c = 0 := Complex.normSq_eq_zero.mp hx
  exact sub_eq_zero.mp this

theorem exp_mul_I_eq_exp_mul_I_imp_sub_mem_two_pi_int {x y : ℝ}
    (h : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) :
    ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = x - y := by
  have hcos : Real.cos (x - y) = 1 := by
    have hq : Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (((x - y : ℝ) : ℂ) * Complex.I) =
          (x : ℂ) * Complex.I - (y : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_sub, h]
      exact div_self (Complex.exp_ne_zero _)
    have hre := congrArg Complex.re hq
    simpa only [Complex.exp_ofReal_mul_I_re, Complex.one_re] using hre
  exact (Real.cos_eq_one_iff (x - y)).mp hcos

theorem eq_of_two_incommensurable_phases {x y : ℝ}
    (h₁ : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I))
    (h₂ : Complex.exp (((Real.sqrt 2 * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((Real.sqrt 2 * y : ℝ) : ℂ) * Complex.I)) : x = y := by
  obtain ⟨k, hk⟩ := exp_mul_I_eq_exp_mul_I_imp_sub_mem_two_pi_int h₁
  obtain ⟨l, hl⟩ := exp_mul_I_eq_exp_mul_I_imp_sub_mem_two_pi_int h₂
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hkl : Real.sqrt 2 * (k : ℝ) = (l : ℝ) := by
    apply (mul_right_cancel₀ hpi)
    calc
      Real.sqrt 2 * (k : ℝ) * (2 * Real.pi) = Real.sqrt 2 * (x - y) := by
        rw [mul_assoc, hk]
      _ = Real.sqrt 2 * x - Real.sqrt 2 * y := by ring
      _ = (l : ℝ) * (2 * Real.pi) := hl.symm
  by_cases hk0 : k = 0
  · subst k
    apply sub_eq_zero.mp
    simpa using hk.symm
  · exact (irrational_sqrt_two.ne_rat
      ((l : ℚ) / (k : ℚ)) (by
        push_cast
        field_simp
        exact hkl)).elim

theorem eq_pointMass_of_charFun_norm_eq_one (μ : ProbabilityMeasure ℝ)
    (h : ∀ t : ℝ, ‖charFun (μ : Measure ℝ) t‖ = 1) :
    ∃ x : ℝ, μ = ProbabilityMeasure.pointMass x := by
  have h₁ := charFun_ae_eq_of_norm_eq_one μ 1 (h 1)
  have h₂ := charFun_ae_eq_of_norm_eq_one μ (Real.sqrt 2) (h (Real.sqrt 2))
  have hboth := h₁.and h₂
  obtain ⟨x, hx⟩ := hboth.exists
  refine ⟨x, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  have hxy : (fun y : ℝ ↦ y) =ᵐ[(μ : Measure ℝ)] (fun _ ↦ x) := by
    filter_upwards [hboth] with y hy
    apply eq_of_two_incommensurable_phases
    · simpa using hy.1.trans hx.1.symm
    · simpa [mul_assoc] using hy.2.trans hx.2.symm
  calc
    (μ : Measure ℝ) = (μ : Measure ℝ).map (fun y : ℝ ↦ y) := by simp
    _ = (μ : Measure ℝ).map (fun _ : ℝ ↦ x) := Measure.map_congr hxy
    _ = Measure.dirac x := by simp [Measure.map_const]
    _ = (ProbabilityMeasure.pointMass x : Measure ℝ) := rfl

end ProbabilityTheory
