/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.HasLaw
public import StochLean.Probability.InfinitelyDivisible.Basic
public import StochLean.Probability.Process.StationaryIncrements

/-!
# Processes with stationary independent increments

This file joins Mathlib's independent-increment predicate with StochLean's stationary-increment
predicate.  The associated law family remains a separate datum so that process semantics and
law-level convolution semantics are not conflated.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

/-- Stationary independent increments, with neither a time-zero normalization nor path regularity
silently included. -/
def HasStationaryIndependentIncrements {T : Type*} [Preorder T] [AddMonoid T] [Sub E]
    (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop :=
  HasStationaryIncrements X P ∧ HasIndepIncrements X P

namespace HasStationaryIndependentIncrements

variable {T : Type*} [Preorder T] [AddMonoid T] [Sub E]
  {X : T → Ω → E} {P : Measure Ω}

theorem stationaryIncrements (hX : HasStationaryIndependentIncrements X P) :
    HasStationaryIncrements X P := hX.1

theorem indepIncrements (hX : HasStationaryIndependentIncrements X P) :
    HasIndepIncrements X P := hX.2

end HasStationaryIndependentIncrements

section FiniteIncrementLaws

variable [AddCommGroup E]

/-- Exact finite-dimensional increment laws for a stationary-increment family.  Quantifying over
every finite ordered partition prevents pairwise independence from standing in for genuine
finite-family independence. -/
def HasFiniteStationaryIncrementLaws (X : ℝ≥0 → Ω → E)
    (ν : ℝ≥0 → ProbabilityMeasure E) (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n (t : Fin (n + 1) → ℝ≥0), Monotone t →
    HasLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω)
      (Measure.pi fun i : Fin n ↦ (ν (t i.succ - t i.castSucc) : Measure E)) P

namespace HasFiniteStationaryIncrementLaws

variable {X : ℝ≥0 → Ω → E} {P : Measure Ω} {ν : ℝ≥0 → ProbabilityMeasure E}

/-- A single coordinate of the finite increment law has the prescribed lag law. -/
theorem coordinateLaw (hX : HasFiniteStationaryIncrementLaws X ν P)
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (i : Fin n) :
    HasLaw (fun ω ↦ X (t i.succ) ω - X (t i.castSucc) ω)
      (ν (t i.succ - t i.castSucc)) P := by
  have hJoint := hX n t ht
  have hEval :=
    (measurePreserving_eval
      (fun j : Fin n ↦ (ν (t j.succ - t j.castSucc) : Measure E)) i).hasLaw
  simpa only [Function.comp_def] using hEval.comp hJoint

/-- One-interval specialization of the finite-dimensional law. -/
theorem incrementLaw (hX : HasFiniteStationaryIncrementLaws X ν P)
    (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (ν (t - s)) P := by
  let τ : Fin 2 → ℝ≥0 := fun i ↦ if i = 0 then s else t
  have hτmono : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [τ, hst] at hij ⊢
  have h := hX.coordinateLaw τ hτmono (0 : Fin 1)
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simpa only [τ, Fin.succ_zero_eq_one, Fin.castSucc_zero, hone, if_false,
    if_true, Fin.zero_eta] using h

/-- Product finite-dimensional laws give Mathlib's genuine independent-increments predicate. -/
theorem hasIndepIncrements [IsProbabilityMeasure P]
    (hX : HasFiniteStationaryIncrementLaws X ν P) :
    HasIndepIncrements X P := by
  intro n t ht
  let Y : Fin n → Ω → E :=
    fun i ω ↦ X (t i.succ) ω - X (t i.castSucc) ω
  let μ : Fin n → Measure E :=
    fun i ↦ (ν (t i.succ - t i.castSucc) : Measure E)
  have hcoord : ∀ i, HasLaw (Y i) (μ i) P :=
    fun i ↦ hX.coordinateLaw t ht i
  exact (iIndepFun_iff_hasLaw_pi_pi hcoord).2 (hX n t ht)

/-- The lag-indexed finite laws imply stationary increments. -/
theorem hasStationaryIncrements (hX : HasFiniteStationaryIncrementLaws X ν P) :
    HasStationaryIncrements X P := by
  intro s t
  have hlater := hX.incrementLaw s (s + t) (by simp)
  have href := hX.incrementLaw 0 t (by simp)
  rw [add_tsub_cancel_left] at hlater
  rw [tsub_zero] at href
  exact hlater.identDistrib href

theorem hasStationaryIndependentIncrements [IsProbabilityMeasure P]
    (hX : HasFiniteStationaryIncrementLaws X ν P) :
    HasStationaryIndependentIncrements X P :=
  ⟨hX.hasStationaryIncrements, hX.hasIndepIncrements⟩

end HasFiniteStationaryIncrementLaws

end FiniteIncrementLaws

section LawFamily

variable [AddCommGroup E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {P : Measure Ω} {ν : ℝ≥0 → ProbabilityMeasure E}

/-- `ν t` is the law of the increment from time zero to time `t`. -/
def HasIncrementLawFamily (X : ℝ≥0 → Ω → E) (ν : ℝ≥0 → ProbabilityMeasure E)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ t, HasLaw (fun ω ↦ X t ω - X 0 ω) (ν t) P

omit [MeasurableAdd₂ E] in
theorem HasIncrementLawFamily.hasLaw (hν : HasIncrementLawFamily X ν P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ X t ω - X 0 ω) (ν t) P := hν t

/-- The increment laws of an SII process form a convolution semigroup.  The proof uses the
stationary law of the later increment, Mathlib's two-increment independence theorem, and the
telescoping identity. -/
theorem HasStationaryIndependentIncrements.isConvolutionSemigroup
    (hX : HasStationaryIndependentIncrements X P) (hν : HasIncrementLawFamily X ν P) :
    IsConvolutionSemigroup ν := by
  intro s t
  have hfirst : HasLaw (fun ω ↦ X s ω - X 0 ω) (ν s) P := hν s
  have hlater : HasLaw (fun ω ↦ X (s + t) ω - X s ω) (ν t) P :=
    (hX.stationaryIncrements s t).symm.hasLaw (hν t)
  have hindep :
      (fun ω ↦ X s ω - X 0 ω) ⟂ᵢ[P] (fun ω ↦ X (s + t) ω - X s ω) :=
    hX.indepIncrements.indepFun_sub_sub (by simp) (by simp)
  have hsum : HasLaw
      (fun ω ↦ (X s ω - X 0 ω) + (X (s + t) ω - X s ω))
      ((ν s : Measure E) ∗ (ν t : Measure E)) P :=
    hindep.hasLaw_fun_add hfirst hlater
  have htel : (fun ω ↦ (X s ω - X 0 ω) + (X (s + t) ω - X s ω)) =
      (fun ω ↦ X (s + t) ω - X 0 ω) := by
    funext ω
    abel
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.coe_conv]
  exact (hν (s + t)).map_eq.symm.trans (htel ▸ hsum.map_eq)

/-- Consequently every increment marginal of an SII process is infinitely divisible. -/
theorem HasStationaryIndependentIncrements.incrementLaw_isInfinitelyDivisible
    (hX : HasStationaryIndependentIncrements X P) (hν : HasIncrementLawFamily X ν P)
    (t : ℝ≥0) : ProbabilityMeasure.IsInfinitelyDivisible (ν t) :=
  (hX.isConvolutionSemigroup hν).isInfinitelyDivisible t

end LawFamily

end ProbabilityTheory
