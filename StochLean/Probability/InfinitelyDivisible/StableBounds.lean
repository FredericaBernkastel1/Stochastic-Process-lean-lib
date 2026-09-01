/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Degeneracy
public import StochLean.Probability.InfinitelyDivisible.Stable
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchineConverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounds for stable probability laws

The modulus of a stable characteristic function scales homogeneously.  Combined with the global
Gaussian lower bound for infinitely divisible characteristic functions, this proves that the
index of a nondegenerate real stable law is at most two.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal ProbabilityTheory Topology

namespace ProbabilityTheory

theorem stable_exponentCost_scale
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    hstable.isStableInBroadSense.isInfinitelyDivisible.exponentCost
        (((n : ℝ) ^ (1 / α)) * t) =
      (n : ℝ) * hstable.isStableInBroadSense.isInfinitelyDivisible.exponentCost t := by
  let hID := hstable.isStableInBroadSense.isInfinitelyDivisible
  obtain ⟨d, hpow⟩ := hstable.2.2 n hn
  have hcf := congrArg
    (fun ρ : ProbabilityMeasure ℝ => ‖charFun (ρ : Measure ℝ) t‖) hpow
  rw [ProbabilityMeasure.charFun_convPow_real,
    ProbabilityMeasure.charFun_affineMap] at hcf
  rw [norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at hcf
  rw [← hID.exp_exponent, ← hID.exp_exponent] at hcf
  simp only [Complex.norm_exp] at hcf
  rw [← Real.exp_nat_mul] at hcf
  have hcost := Real.exp_injective hcf
  change -(hID.exponent (((n : ℝ) ^ (1 / α)) * t)).re =
    (n : ℝ) * (-(hID.exponent t).re)
  linarith [hcost]

theorem IsStableInBroadSenseWithIndex.exists_exponentCost_pos
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) :
    ∃ t : ℝ, 0 < hstable.isStableInBroadSense.isInfinitelyDivisible.exponentCost t := by
  let hID := hstable.isStableInBroadSense.isInfinitelyDivisible
  by_contra hnone
  push Not at hnone
  have hzero (t : ℝ) : hID.exponentCost t = 0 :=
    le_antisymm (hnone t) (hID.exponentCost_nonneg t)
  have hnorm (t : ℝ) : ‖charFun (μ : Measure ℝ) t‖ = 1 := by
    rw [← hID.exp_exponent, Complex.norm_exp]
    have hrew : (hID.exponent t).re = -hID.exponentCost t := by
      change (hID.exponent t).re = -(-(hID.exponent t).re)
      ring
    rw [hrew, hzero]
    norm_num
  obtain ⟨x, hx⟩ := eq_pointMass_of_charFun_norm_eq_one μ hnorm
  exact hstable.2.1 x hx

/-- The scaling index of a nondegenerate real stable law cannot exceed two. -/
theorem IsStableInBroadSenseWithIndex.index_le_two
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) : α ≤ 2 := by
  by_contra hα
  have hαtwo : 2 < α := lt_of_not_ge hα
  have hαpos : 0 < α := hstable.1
  let hID := hstable.isStableInBroadSense.isInfinitelyDivisible
  obtain ⟨t, ht⟩ :=
    IsStableInBroadSenseWithIndex.exists_exponentCost_pos hstable
  obtain ⟨ε, hε, hgauss⟩ := hID.exists_gaussian_charFun_lowerBound
  have hpoint (n : ℕ) :
      hID.exponentCost t ≤
        Real.log 2 / ((n + 1 : ℕ) : ℝ) +
          ε * t ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (2 / α - 1)) := by
    let m : ℕ := n + 1
    have hm : 0 < m := by omega
    have hmR : 0 < (m : ℝ) := by positivity
    let s : ℝ := ((m : ℝ) ^ (1 / α)) * t
    have hnorm : ‖charFun (μ : Measure ℝ) s‖ =
        Real.exp (-((m : ℝ) * hID.exponentCost t)) := by
      rw [← hID.exp_exponent, Complex.norm_exp]
      have hrew : (hID.exponent s).re = -hID.exponentCost s := by
        change (hID.exponent s).re = -(-(hID.exponent s).re)
        ring
      rw [hrew, stable_exponentCost_scale hstable m hm t]
    have hlower := hgauss s
    rw [hnorm] at hlower
    have hhalf : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hexp : Real.exp (-(Real.log 2 + ε * s ^ 2)) ≤
        Real.exp (-((m : ℝ) * hID.exponentCost t)) := by
      calc
        Real.exp (-(Real.log 2 + ε * s ^ 2)) =
            (1 / 2 : ℝ) * Real.exp (-ε * s ^ 2) := by
              rw [neg_add, Real.exp_add, hhalf]
              congr 1
              congr 1
              ring
        _ ≤ _ := hlower
    have hcost : (m : ℝ) * hID.exponentCost t ≤
        Real.log 2 + ε * s ^ 2 := by
      have := Real.exp_le_exp.mp hexp
      linarith
    have hrpowSquare :
        (((m : ℝ) ^ (1 / α)) * t) ^ 2 / (m : ℝ) =
          t ^ 2 * ((m : ℝ) ^ (2 / α - 1)) := by
      have hmnonneg : 0 ≤ (m : ℝ) := hmR.le
      have hp : ((m : ℝ) ^ ((1 / α) * 2)) =
          (((m : ℝ) ^ (1 / α)) ^ 2) := by
        calc
          ((m : ℝ) ^ ((1 / α) * 2)) =
              (((m : ℝ) ^ (1 / α)) ^ (2 : ℝ)) :=
            Real.rpow_mul hmnonneg (1 / α) 2
          _ = (((m : ℝ) ^ (1 / α)) ^ (2 : ℕ)) :=
            Real.rpow_natCast _ 2
      calc
        (((m : ℝ) ^ (1 / α)) * t) ^ 2 / (m : ℝ) =
            t ^ 2 * (((m : ℝ) ^ (1 / α)) ^ 2 / (m : ℝ)) := by ring
        _ = t ^ 2 * (((m : ℝ) ^ ((1 / α) * 2)) / (m : ℝ)) := by
          exact congrArg (fun x : ℝ => t ^ 2 * (x / (m : ℝ))) hp.symm
        _ = t ^ 2 * (((m : ℝ) ^ ((1 / α) * 2)) / ((m : ℝ) ^ (1 : ℝ))) := by
          rw [Real.rpow_one]
        _ = t ^ 2 * ((m : ℝ) ^ ((1 / α) * 2 - 1)) := by
          exact congrArg (fun x : ℝ => t ^ 2 * x)
            (Real.rpow_sub hmR ((1 / α) * 2) 1).symm
        _ = t ^ 2 * ((m : ℝ) ^ (2 / α - 1)) := by
          congr 2
          field_simp
    have hdiv := (div_le_div_iff_of_pos_right hmR).2 hcost
    dsimp [s] at hdiv
    have hfinal : hID.exponentCost t ≤
        Real.log 2 / (m : ℝ) + ε * t ^ 2 * ((m : ℝ) ^ (2 / α - 1)) := by
      calc
        hID.exponentCost t = ((m : ℝ) * hID.exponentCost t) / (m : ℝ) := by
          field_simp
        _ ≤ (Real.log 2 + ε * (((m : ℝ) ^ (1 / α)) * t) ^ 2) / (m : ℝ) := hdiv
        _ = Real.log 2 / (m : ℝ) +
            ε * ((((m : ℝ) ^ (1 / α)) * t) ^ 2 / (m : ℝ)) := by ring
        _ = Real.log 2 / (m : ℝ) +
            ε * t ^ 2 * ((m : ℝ) ^ (2 / α - 1)) := by
          rw [hrpowSquare]
          ring
    simpa [m] using hfinal
  let β : ℝ := 1 - 2 / α
  have hβ : 0 < β := by
    dsimp [β]
    have : 2 / α < 1 := (div_lt_one hαpos).2 hαtwo
    linarith
  have hmTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    change Tendsto (Nat.cast ∘ fun n : ℕ => n + 1) atTop atTop
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hfirst : Tendsto (fun n : ℕ => Real.log 2 / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := hmTop.const_div_atTop (Real.log 2)
  have hsecondBase : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-β))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hβ).comp hmTop
  have hsecond : Tendsto
      (fun n : ℕ => ε * t ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (2 / α - 1)))
      atTop (𝓝 0) := by
    have hexponent : 2 / α - 1 = -β := by
      dsimp [β]
      ring
    simpa [hexponent] using hsecondBase.const_mul (ε * t ^ 2)
  have hsum : Tendsto
      (fun n : ℕ => Real.log 2 / ((n + 1 : ℕ) : ℝ) +
        ε * t ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (2 / α - 1)))
      atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  have hcostNonpos : hID.exponentCost t ≤ 0 :=
    ge_of_tendsto' hsum hpoint
  linarith

/-- The canonical Gaussian alternative in Theorem 16.22 for an indexed stable law. -/
theorem IsStableInBroadSenseWithIndex.exists_triplet_gaussianDichotomy
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) :
    ∃ eta : LevyTriplet, eta.Represents μ ∧
      (eta.gaussianVariance = 0 ∨ α = 2) := by
  obtain ⟨eta, heta⟩ := hstable.isStableInBroadSense.isInfinitelyDivisible
    |>.exists_representingTriplet
  refine ⟨eta, heta, ?_⟩
  by_cases hzero : eta.gaussianVariance = 0
  · exact Or.inl hzero
  · right
    apply LevyTriplet.index_eq_two_of_gaussianVariance_pos hstable heta
    exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hzero))

theorem IsStableInBroadSenseWithIndex.gaussianVariance_eq_zero_of_index_lt_two
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) (hα : α < 2)
    {eta : LevyTriplet} (heta : eta.Represents μ) :
    eta.gaussianVariance = 0 := by
  by_contra hzero
  have hpos : 0 < (eta.gaussianVariance : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hzero)
  have := LevyTriplet.index_eq_two_of_gaussianVariance_pos hstable heta hpos
  linarith

theorem IsStableInBroadSenseWithIndex.index_mem_Ioc
    {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hstable : μ.IsStableInBroadSenseWithIndex α) : α ∈ Set.Ioc 0 2 :=
  ⟨hstable.1, IsStableInBroadSenseWithIndex.index_le_two hstable⟩

end ProbabilityTheory
