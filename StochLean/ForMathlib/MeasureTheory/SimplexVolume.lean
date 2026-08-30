/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volumes of nonnegative simplices

This module supplies the finite-dimensional Lebesgue-volume calculation used by exponential
arrival-time constructions.  The statement is generic measure theory and deliberately does not
live in the Poisson-process namespace.
-/

@[expose] public section

open Set Finset
open scoped ENNReal

namespace MeasureTheory

noncomputable section

/-- The nonnegative coordinate simplex with coordinate sum at most `t`. -/
def nonnegativeSimplex (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}

lemma measurableSet_nonnegativeSimplex (n : ℕ) (t : ℝ) :
    MeasurableSet (nonnegativeSimplex n t) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩
    {x : Fin n → ℝ | ∑ i, x i ≤ t})
  have h1 : MeasurableSet (⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i}) :=
    MeasurableSet.iInter fun i : Fin n ↦
      measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  convert h1.inter h2 using 1
  ext x
  simp

lemma nonnegativeSimplex_eq_empty_of_neg {n : ℕ} {t : ℝ} (ht : t < 0) :
    nonnegativeSimplex n t = ∅ := by
  ext x
  change (((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t) ↔ False)
  constructor
  · intro hx
    have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ ↦ hx.1 i
    exact (not_le_of_gt ht) (hsum.trans hx.2)
  · simp

/-- Fubini recurrence for nonnegative simplex volume. -/
lemma volume_nonnegativeSimplex_succ (n : ℕ) (t : ℝ) :
    volume (nonnegativeSimplex (n + 1) t) =
      ∫⁻ a in Icc 0 t, volume (nonnegativeSimplex n (t - a)) := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0
  let R : Set (ℝ × (Fin n → ℝ)) :=
    {p | 0 ≤ p.1 ∧ p.2 ∈ nonnegativeSimplex n (t - p.1)}
  have hR : MeasurableSet R := by
    change MeasurableSet ({p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} ∩
      {p : ℝ × (Fin n → ℝ) | (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ t - p.1})
    have hrest1 : MeasurableSet (⋂ i : Fin n,
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.2 i}) :=
      MeasurableSet.iInter fun i : Fin n ↦
        measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
    have hrest2 : MeasurableSet
        {p : ℝ × (Fin n → ℝ) | ∑ i, p.2 i ≤ t - p.1} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    refine (measurableSet_le measurable_const measurable_fst).inter ?_
    convert hrest1.inter hrest2 using 1
    ext p
    simp
  have hpre : e ⁻¹' R = nonnegativeSimplex (n + 1) t := by
    ext x
    simp only [Set.mem_preimage, R, Set.mem_ofPred_eq, nonnegativeSimplex, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_symm_apply, Fin.tail, Fin.sum_univ_succ]
    constructor
    · rintro ⟨hx0, hxrest, hxsum⟩
      refine ⟨?_, by linarith⟩
      intro i
      refine Fin.cases hx0 (fun j ↦ ?_) i
      simpa using hxrest j
    · rintro ⟨hx, hxsum⟩
      refine ⟨hx 0, fun j ↦ ?_, by linarith⟩
      simpa using hx j.succ
  have hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  calc
    volume (nonnegativeSimplex (n + 1) t) = (Measure.map e volume) R := by
      rw [Measure.map_apply e.measurable hR, hpre]
    _ = volume R := by rw [hpres.map_eq]
    _ = ∫⁻ a : ℝ, volume (Prod.mk a ⁻¹' R) := Measure.prod_apply hR
    _ = ∫⁻ a in Icc 0 t, volume (nonnegativeSimplex n (t - a)) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro a
      by_cases ha0 : 0 ≤ a
      · by_cases hat : a ≤ t
        · have hfiber : Prod.mk a ⁻¹' R = nonnegativeSimplex n (t - a) := by
            ext y
            simp [R, ha0]
          simp [hfiber, ha0, hat]
        · have hneg : t - a < 0 := sub_neg.mpr (lt_of_not_ge hat)
          have hfiber : Prod.mk a ⁻¹' R = ∅ := by
            ext y
            simp [R, ha0, nonnegativeSimplex_eq_empty_of_neg hneg]
          simp [hfiber, ha0, hat]
      · have hfiber : Prod.mk a ⁻¹' R = ∅ := by
          ext y
          simp [R, ha0]
        simp [hfiber, ha0]

private lemma integral_sub_pow_div_factorial (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ a in Icc 0 t, (t - a) ^ n / (n.factorial : ℝ) =
      t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) t]
  rw [integral_pow]
  simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero n), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.factorial_ne_zero]

/-- The `n`-dimensional nonnegative simplex of radius `t ≥ 0` has volume `t^n / n!`. -/
theorem volume_nonnegativeSimplex (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume (nonnegativeSimplex n t) =
      ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) := by
  induction n generalizing t with
  | zero =>
      have hs : nonnegativeSimplex 0 t = Set.univ := by
        ext x
        simp [nonnegativeSimplex, ht]
      rw [hs, volume_pi]
      simpa only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one,
        ENNReal.ofReal_one] using
        (Measure.pi_empty_univ (fun _ : Fin 0 ↦ (volume : Measure ℝ)))
  | succ n ih =>
      rw [volume_nonnegativeSimplex_succ]
      calc
        (∫⁻ a in Icc 0 t, volume (nonnegativeSimplex n (t - a))) =
            ∫⁻ a in Icc 0 t,
              ENNReal.ofReal ((t - a) ^ n / (n.factorial : ℝ)) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro a ha
          exact ih (sub_nonneg.mpr ha.2)
        _ = ENNReal.ofReal
            (∫ a in Icc 0 t, (t - a) ^ n / (n.factorial : ℝ)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (by fun_prop : Continuous (fun a : ℝ ↦
                (t - a) ^ n / (n.factorial : ℝ))).integrableOn_Icc
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
            exact div_nonneg (pow_nonneg (sub_nonneg.mpr ha.2) n) (Nat.cast_nonneg _)
        _ = ENNReal.ofReal (t ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [integral_sub_pow_div_factorial n ht]

end

end MeasureTheory
