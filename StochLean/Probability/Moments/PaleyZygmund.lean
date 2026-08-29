/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Paley--Zygmund inequality

The zero-threshold form below is Exercise 5.1.1 in Klenke.  Its multiplicative statement avoids
division by a possibly zero second moment; the familiar quotient form follows under strict
positivity.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Paley--Zygmund at threshold zero, in a form valid without a nonzero-second-moment side
condition. -/
theorem integral_sq_le_prob_pos_mul_integral_sq {X : Ω → ℝ} (hX : Measurable X)
    (hX_nonneg : 0 ≤ᵐ[P] X) (hX_mem : MemLp X (ENNReal.ofReal 2) P) :
    (∫ ω, X ω ∂P) ^ 2 ≤ P.real {ω | 0 < X ω} * ∫ ω, X ω ^ 2 ∂P := by
  let A : Set Ω := {ω | 0 < X ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hX
  let I : Ω → ℝ := A.indicator fun _ ↦ 1
  have hI_nonneg : 0 ≤ᵐ[P] I := ae_of_all _ fun ω ↦ by
    simp only [I, Set.indicator_apply]
    split_ifs <;> positivity
  have hI_mem : MemLp I (ENNReal.ofReal 2) P :=
    memLp_indicator_const (ENNReal.ofReal 2) hA 1 (Or.inr (measure_ne_top P A))
  have hprod : (fun ω ↦ X ω * I ω) =ᵐ[P] X := by
    filter_upwards [hX_nonneg] with ω hω
    by_cases hpos : 0 < X ω
    · simp [I, A, hpos]
    · have hz : X ω = 0 := le_antisymm (le_of_not_gt hpos) hω
      simp [I, A, hz]
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hX_nonneg hI_nonneg hX_mem hI_mem
  rw [integral_congr_ae hprod] at hcs
  have hmean_nonneg : 0 ≤ ∫ ω, X ω ∂P := integral_nonneg_of_ae hX_nonneg
  have hsquare_nonneg : 0 ≤ ∫ ω, X ω ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have hindicator : (∫ ω, I ω ^ (2 : ℝ) ∂P) = P.real A := by
    calc
      (∫ ω, I ω ^ (2 : ℝ) ∂P) = ∫ ω, I ω ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω ↦ by
          simp only [I, Real.rpow_two, Set.indicator_apply]
          split_ifs <;> norm_num
      _ = P.real A := by
        rw [show I = A.indicator (1 : Ω → ℝ) by
          ext ω
          change A.indicator (fun _ : Ω ↦ (1 : ℝ)) ω =
            A.indicator (fun _ : Ω ↦ (1 : ℝ)) ω
          rfl]
        exact integral_indicator_one hA
  rw [hindicator] at hcs
  have hcs' : ∫ ω, X ω ∂P ≤
      Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (P.real A) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hcs
  have hprob_nonneg : 0 ≤ P.real A := ENNReal.toReal_nonneg
  have hsqrt_sq : Real.sqrt (∫ ω, X ω ^ 2 ∂P) ^ 2 = ∫ ω, X ω ^ 2 ∂P :=
    Real.sq_sqrt hsquare_nonneg
  have hprob_sqrt_sq : Real.sqrt (P.real A) ^ 2 = P.real A :=
    Real.sq_sqrt hprob_nonneg
  have hright_nonneg :
      0 ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (P.real A) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The usual quotient form of Paley--Zygmund at threshold zero. -/
theorem integral_sq_div_integral_sq_le_prob_pos {X : Ω → ℝ} (hX : Measurable X)
    (hX_nonneg : 0 ≤ᵐ[P] X) (hX_mem : MemLp X (ENNReal.ofReal 2) P)
    (hsecond : 0 < ∫ ω, X ω ^ 2 ∂P) :
    (∫ ω, X ω ∂P) ^ 2 / (∫ ω, X ω ^ 2 ∂P) ≤ P.real {ω | 0 < X ω} := by
  exact (div_le_iff₀ hsecond).2
    (integral_sq_le_prob_pos_mul_integral_sq hX hX_nonneg hX_mem)

end ProbabilityTheory
