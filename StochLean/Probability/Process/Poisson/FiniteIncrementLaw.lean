/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Basic
public import Mathlib.Probability.HasLaw

/-!
# Finite-dimensional Poisson increment laws

This module packages the genuinely finite-dimensional statement required by the exponential-
arrival construction.  The hypothesis is quantified over every finite ordered partition, rather
than merely over two successive intervals.  From it we recover Mathlib's canonical
`HasIndepIncrements` predicate and each one-interval Poisson law.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Joint Poisson law for the increments along every finite ordered partition. -/
def HasFinitePoissonIncrementLaws (X : NNReal → Ω → ℕ) (rate : NNReal)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n (t : Fin (n + 1) → NNReal), Monotone t →
    HasLaw (fun ω (i : Fin n) ↦ X (t i.succ) ω - X (t i.castSucc) ω)
      (Measure.pi fun i : Fin n ↦
        poissonMeasure (rate * (t i.succ - t i.castSucc))) P

namespace HasFinitePoissonIncrementLaws

variable {X : NNReal → Ω → ℕ} {rate : NNReal}

omit [IsProbabilityMeasure P] in
/-- Every coordinate of a finite joint increment law has its prescribed Poisson marginal. -/
theorem coordinateLaw (hX : HasFinitePoissonIncrementLaws X rate P)
    {n : ℕ} (t : Fin (n + 1) → NNReal) (ht : Monotone t) (i : Fin n) :
    HasLaw (fun ω ↦ X (t i.succ) ω - X (t i.castSucc) ω)
      (poissonMeasure (rate * (t i.succ - t i.castSucc))) P := by
  have hJoint := hX n t ht
  have hEval :=
    (measurePreserving_eval
      (fun j : Fin n ↦ poissonMeasure (rate * (t j.succ - t j.castSucc))) i).hasLaw
  simpa only [Function.comp_def] using hEval.comp hJoint

/-- Arbitrary finite joint product laws imply the canonical independent-increments predicate. -/
theorem hasIndepIncrements (hX : HasFinitePoissonIncrementLaws X rate P) :
    HasIndepIncrements X P := by
  intro n t ht
  let Y : Fin n → Ω → ℕ :=
    fun i ω ↦ X (t i.succ) ω - X (t i.castSucc) ω
  let μ : Fin n → Measure ℕ :=
    fun i ↦ poissonMeasure (rate * (t i.succ - t i.castSucc))
  have hcoord : ∀ i, HasLaw (Y i) (μ i) P :=
    fun i ↦ hX.coordinateLaw t ht i
  exact (iIndepFun_iff_hasLaw_pi_pi hcoord).2 (hX n t ht)

omit [IsProbabilityMeasure P] in
/-- The one-interval member of the finite-dimensional family. -/
theorem incrementLaw (hX : HasFinitePoissonIncrementLaws X rate P)
    (s t : NNReal) (hst : s ≤ t) :
    HasLaw (fun ω ↦ X t ω - X s ω) (poissonMeasure (rate * (t - s))) P := by
  let τ : Fin 2 → NNReal := fun i ↦ if i = 0 then s else t
  have hτmono : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [τ, hst] at hij ⊢
  have h := hX.coordinateLaw τ hτmono (0 : Fin 1)
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simpa only [τ, Fin.succ_zero_eq_one, Fin.castSucc_zero, hone, if_false,
    if_true, Fin.zero_eta] using h

/-- Construction principle: finite partition laws plus the corrected common-event path
properties produce a Poisson process. -/
theorem isPoissonProcess (hLaw : HasFinitePoissonIncrementLaws X rate P)
    (hmeas : ∀ t, AEMeasurable (X t) P)
    (hzero : X 0 =ᵐ[P] fun _ ↦ 0)
    (hmono : HasMonotonePaths X P)
    (hright : HasRightContinuousPaths X P) :
    IsPoissonProcess X rate P where
  aemeasurable := hmeas
  initial := hzero
  monotonePaths := hmono
  rightContinuousPaths := hright
  indepIncrements := hLaw.hasIndepIncrements
  incrementLaw := hLaw.incrementLaw

omit [IsProbabilityMeasure P] in
/-- Four-increment acceptance test.  It prevents a proof of a two-increment special case from
silently standing in for the finite-dimensional statement required in Klenke 5.36. -/
theorem fourIncrementLaw (hX : HasFinitePoissonIncrementLaws X rate P)
    (t : Fin 5 → NNReal) (ht : Monotone t) :
    HasLaw (fun ω (i : Fin 4) ↦ X (t i.succ) ω - X (t i.castSucc) ω)
      (Measure.pi fun i : Fin 4 ↦
        poissonMeasure (rate * (t i.succ - t i.castSucc))) P :=
  hX 4 t ht

end HasFinitePoissonIncrementLaws

end ProbabilityTheory
