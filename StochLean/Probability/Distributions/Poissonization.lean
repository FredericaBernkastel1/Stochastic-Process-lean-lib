/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Distributions.Multinomial
public import StochLean.Probability.GeneratingFunction.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Poissonization of categorical samples

This module proves the characteristic-function identities behind Poisson splitting.  They are
kept distribution-generic so that the uniform-point construction only has to supply its finite
categorization law.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal ProbabilityTheory

namespace ProbabilityTheory

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

omit [DecidableEq κ] in
/-- Characteristic function of a categorical one-hot vector. -/
theorem charFunDual_map_categoricalOneHotReal (p : PMF κ)
    (L : StrongDual ℝ (κ → ℝ)) :
    charFunDual (p.toMeasure.map categoricalOneHotReal) L =
      ∑ a, (p a).toReal * Complex.exp (L (categoricalOneHotReal a) * Complex.I) := by
  rw [charFunDual_apply, integral_map .of_discrete (by fun_prop), PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Algebra.smul_def]

omit [DecidableEq κ] in
/-- The characteristic function of `n` categorical counts is the `n`th power of the one-trial
one-hot characteristic function. -/
theorem charFunDual_map_multinomial_counts (p : PMF κ) (n : ℕ)
    (L : StrongDual ℝ (κ → ℝ)) :
    charFunDual ((PMF.multinomial p n).toMeasure.map categoricalCountsReal) L =
      (charFunDual (p.toMeasure.map categoricalOneHotReal) L) ^ n := by
  let P : Measure (Fin n → κ) := Measure.pi fun _ : Fin n ↦ p.toMeasure
  have hmOneHot : Measurable (categoricalOneHotReal (κ := κ)) := measurable_of_countable _
  have hmap (i : Fin n) :
      P.map (fun x ↦ categoricalOneHotReal (x i)) =
        p.toMeasure.map categoricalOneHotReal := by
    calc
      P.map (fun x ↦ categoricalOneHotReal (x i)) =
          (P.map fun x ↦ x i).map categoricalOneHotReal := by
        symm
        rw [Measure.map_map hmOneHot (measurable_pi_apply i)]
        rfl
      _ = p.toMeasure.map categoricalOneHotReal := by
        rw [(measurePreserving_eval (fun _ : Fin n ↦ p.toMeasure) i).map_eq]
  have hIndep : iIndepFun
      (fun i (x : Fin n → κ) ↦ categoricalOneHotReal (x i)) P := by
    have hEval : iIndepFun (fun i (x : Fin n → κ) ↦ x i) P :=
      iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
    exact hEval.comp (fun _ ↦ categoricalOneHotReal) (fun _ ↦ hmOneHot)
  have hchar := hIndep.charFunDual_map_fun_sum_eq_prod
    (fun _ ↦ (hmOneHot.comp (measurable_pi_apply _)).aemeasurable)
  rw [PMF.multinomial_toMeasure, Measure.map_map
    measurable_categoricalCountsReal measurable_categoricalCounts]
  have hfun : categoricalCountsReal ∘ categoricalCounts =
      fun x : Fin n → κ ↦ ∑ i, categoricalOneHotReal (x i) := by
    funext x
    exact categoricalCountsReal_comp_eq_sum_oneHotReal x
  rw [hfun]
  have hcharL := congrFun hchar L
  have hmap' (i : Fin n) :
      P.map (categoricalOneHotReal ∘ fun x ↦ x i) =
        p.toMeasure.map categoricalOneHotReal := by
    simpa only [Function.comp_def] using hmap i
  rw [Finset.prod_apply] at hcharL
  simp_rw [hmap'] at hcharL
  simpa only [P, Function.comp_apply, Finset.prod_const, Finset.card_fin] using hcharL

namespace PMF

/-- Canonical PMF associated with Mathlib's Poisson probability measure. -/
def poissonLaw (r : NNReal) : PMF ℕ := (poissonMeasure r).toPMF

@[simp]
theorem poissonLaw_toMeasure (r : NNReal) : (poissonLaw r).toMeasure = poissonMeasure r :=
  Measure.toPMF_toMeasure _

@[simp]
theorem poissonLaw_apply (r : NNReal) (n : ℕ) :
    poissonLaw r n = poissonMeasure r {n} :=
  rfl

theorem poissonLaw_toReal_apply (r : NNReal) (n : ℕ) :
    (poissonLaw r n).toReal = Real.exp (-r) * r ^ n / Nat.factorial n := by
  simpa only [poissonLaw_apply, measureReal_def] using poissonMeasure_real_singleton r n

/-- A Poisson number of independent categorical trials. -/
def poissonizedMultinomial (r : NNReal) (p : PMF κ) : PMF (κ → ℕ) :=
  (poissonLaw r).bind fun n ↦ multinomial p n

omit [DecidableEq κ] in
/-- The Poissonized multinomial law is the countable mixture of its fixed-size laws. -/
theorem poissonizedMultinomial_toMeasure (r : NNReal) (p : PMF κ) :
    (poissonizedMultinomial r p).toMeasure =
      Measure.sum fun n ↦ poissonLaw r n • (multinomial p n).toMeasure := by
  ext s hs
  rw [poissonizedMultinomial, PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply, smul_eq_mul]

omit [DecidableEq κ] in
/-- After casting counts to reals, the Poissonized law is the corresponding mixture of cast
fixed-size multinomial laws. -/
theorem poissonizedMultinomial_map_countsReal (r : NNReal) (p : PMF κ) :
    (poissonizedMultinomial r p).toMeasure.map categoricalCountsReal =
      Measure.sum fun n ↦ poissonLaw r n •
        ((multinomial p n).toMeasure.map categoricalCountsReal) := by
  rw [poissonizedMultinomial_toMeasure, Measure.map_sum
    measurable_categoricalCountsReal.aemeasurable]
  apply congrArg Measure.sum
  funext n
  exact Measure.map_smul _ _ _

end PMF

omit [DecidableEq κ] in
/-- Characteristic function of a Poissonized categorical count vector. -/
theorem charFunDual_map_poissonizedMultinomial (r : NNReal) (p : PMF κ)
    (L : StrongDual ℝ (κ → ℝ)) :
    charFunDual ((PMF.poissonizedMultinomial r p).toMeasure.map categoricalCountsReal) L =
      Complex.exp ((r : ℝ) *
        (charFunDual (p.toMeasure.map categoricalOneHotReal) L - 1)) := by
  rw [PMF.poissonizedMultinomial_map_countsReal, charFunDual_apply]
  have hint : Integrable (BoundedContinuousFunction.probCharDual L)
      (Measure.sum fun n ↦ PMF.poissonLaw r n •
        ((PMF.multinomial p n).toMeasure.map categoricalCountsReal)) := by
    rw [← PMF.poissonizedMultinomial_map_countsReal]
    exact (BoundedContinuousFunction.probCharDual L).integrable _
  change (∫ v, BoundedContinuousFunction.probCharDual L v ∂Measure.sum fun n ↦
    PMF.poissonLaw r n • ((PMF.multinomial p n).toMeasure.map categoricalCountsReal)) = _
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure, BoundedContinuousFunction.probCharDual_apply,
    ← charFunDual_apply,
    charFunDual_map_multinomial_counts, PMF.poissonLaw_toReal_apply]
  simp only [Algebra.smul_def]
  let z := charFunDual (p.toMeasure.map categoricalOneHotReal) L
  change (∑' n : ℕ, ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / Nat.factorial n) : ℝ) * z ^ n) =
    Complex.exp ((r : ℝ) * (z - 1))
  calc
    (∑' n : ℕ, ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / Nat.factorial n) : ℝ) * z ^ n) =
        (Real.exp (-(r : ℝ)) : ℂ) * ∑' n : ℕ, (((r : ℂ) * z) ^ n / Nat.factorial n) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      push_cast
      rw [mul_pow]
      ring
    _ = (Real.exp (-(r : ℝ)) : ℂ) * Complex.exp ((r : ℂ) * z) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * z)).tsum_eq,
        Complex.exp_eq_exp_ℂ]
    _ = Complex.exp ((r : ℝ) * (z - 1)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf

/-- Poisson characteristic function in the Banach-space dual presentation on `ℝ`. -/
theorem charFunDual_map_cast_poissonMeasure (r : NNReal) (L : StrongDual ℝ ℝ) :
    charFunDual (poissonMeasure r |>.map fun n : ℕ ↦ (n : ℝ)) L =
      Complex.exp ((r : ℝ) * (Complex.exp (L 1 * Complex.I) - 1)) := by
  have hL : L = InnerProductSpace.toDualMap ℝ ℝ (L 1) := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x * L 1 := by rw [map_smul]; rfl
      _ = L 1 * x := mul_comm _ _
      _ = InnerProductSpace.toDualMap ℝ ℝ (L 1) x := by
        rw [InnerProductSpace.toDualMap_apply_apply]
        exact mul_comm _ _
  rw [hL, ← charFun_eq_charFunDual_toDualMap]
  simpa only [InnerProductSpace.toDualMap_apply_apply, Real.inner_apply, one_mul, mul_one] using
    charFun_map_cast_poissonMeasure r (L 1)

namespace PMF

/-- Product law of independent Poisson counts with rates `r * p a`. -/
def independentPoissonCounts (r : NNReal) (p : PMF κ) : PMF (κ → ℕ) :=
  (Measure.pi fun a ↦ poissonMeasure (r * (p a).toNNReal)).toPMF

omit [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] in
@[simp]
theorem independentPoissonCounts_toMeasure (r : NNReal) (p : PMF κ) :
    (independentPoissonCounts r p).toMeasure =
      Measure.pi fun a ↦ poissonMeasure (r * (p a).toNNReal) :=
  Measure.toPMF_toMeasure _

end PMF

omit [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] in
/-- Casting the independent Poisson count vector coordinatewise produces the product of the
corresponding cast Poisson measures. -/
theorem map_independentPoissonCounts_countsReal (r : NNReal) (p : PMF κ) :
    (PMF.independentPoissonCounts r p).toMeasure.map categoricalCountsReal =
      Measure.pi fun a ↦
        (poissonMeasure (r * (p a).toNNReal)).map fun n : ℕ ↦ (n : ℝ) := by
  rw [PMF.independentPoissonCounts_toMeasure]
  change (Measure.pi fun a ↦ poissonMeasure (r * (p a).toNNReal)).map
      (fun c a ↦ ((c a : ℕ) : ℝ)) = _
  exact Measure.pi_map_pi fun _ ↦ (measurable_of_countable _).aemeasurable

omit [DecidableEq κ] in
/-- Characteristic function of a vector of independent Poisson counts with rates `r * p a`. -/
theorem charFunDual_map_independentPoissonCounts (r : NNReal) (p : PMF κ)
    (L : StrongDual ℝ (κ → ℝ)) :
    charFunDual ((PMF.independentPoissonCounts r p).toMeasure.map categoricalCountsReal) L =
      Complex.exp ((r : ℝ) *
        (charFunDual (p.toMeasure.map categoricalOneHotReal) L - 1)) := by
  classical
  rw [map_independentPoissonCounts_countsReal, charFunDual_pi]
  simp_rw [charFunDual_map_cast_poissonMeasure]
  rw [← Complex.exp_sum, charFunDual_map_categoricalOneHotReal]
  congr 1
  have hpSum : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
    have hp : ∑ a, p a = 1 := by
      simpa only [tsum_fintype] using p.tsum_coe
    rw [hp, ENNReal.toReal_one]
  simp_rw [ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.single_apply]
  have hOneHot (a : κ) : Pi.single a (1 : ℝ) = categoricalOneHotReal a := by
    funext b
    simp [Pi.single_apply, categoricalOneHotReal, eq_comm]
  simp_rw [hOneHot]
  have hpSumC : ∑ a, ((p a).toReal : ℂ) = 1 := by
    exact_mod_cast hpSum
  push_cast
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [mul_one]
  rw [hpSumC]
  ring

omit [DecidableEq κ] in
/-- Poissonizing the sample size splits the multinomial count vector into independent Poisson
coordinates.  This is the finite categorical form of the Poisson splitting theorem. -/
theorem PMF.poissonizedMultinomial_eq_independentPoissonCounts (r : NNReal) (p : PMF κ) :
    PMF.poissonizedMultinomial r p = PMF.independentPoissonCounts r p := by
  classical
  apply PMF.toMeasure_injective
  have hCastInj : Function.Injective (categoricalCountsReal (κ := κ)) := by
    intro c d h
    funext a
    have ha : (c a : ℝ) = (d a : ℝ) := by
      simpa only [categoricalCountsReal] using congrFun h a
    exact_mod_cast ha
  have hCastEmb : MeasurableEmbedding (categoricalCountsReal (κ := κ)) :=
    measurable_categoricalCountsReal.measurableEmbedding hCastInj
  apply hCastEmb.map_injective
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map_poissonizedMultinomial,
    charFunDual_map_independentPoissonCounts]

end

end ProbabilityTheory
