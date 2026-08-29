/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.Poisson.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Interval-count axioms for Poisson processes

This file formalizes Klenke's interval axioms P1--P5 for a counting process.  In addition to
those axioms, the predicate records the design-level path convention used by StochLean: paths are
almost surely monotone and right-continuous on one common event, and the process starts at zero.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The number of events in the half-open time interval `(s, t]`.  Statements about this count
carry the hypothesis `s ≤ t`, so natural subtraction is genuine count subtraction. -/
def poissonIntervalCount (X : NNReal → Ω → ℕ) (s t : NNReal) (ω : Ω) : ℕ :=
  X t ω - X s ω

/-- Klenke's P1--P5 interval-count axioms, together with the corrected path semantics fixed by
the StochLean design: one common almost-sure event supports monotone right-continuous paths. -/
structure SatisfiesPoissonIntervalAxioms (X : NNReal → Ω → ℕ)
    (P : Measure Ω := by volume_tac) [IsProbabilityMeasure P] : Prop where
  aemeasurable : ∀ t, AEMeasurable (X t) P
  initial : X 0 =ᵐ[P] fun _ ↦ 0
  monotonePaths : HasMonotonePaths X P
  rightContinuousPaths : HasRightContinuousPaths X P
  /-- P1: adjacent interval counts add. -/
  intervalAdditive : ∀ r s t, r ≤ s → s ≤ t →
    poissonIntervalCount X r t =ᵐ[P] fun ω ↦
      poissonIntervalCount X r s ω + poissonIntervalCount X s t ω
  /-- P2: the law of an interval count depends only on its length. -/
  stationaryIntervalLaw : ∀ r s t u, r ≤ s → t ≤ u → s - r = u - t →
    IdentDistrib (poissonIntervalCount X r s) (poissonIntervalCount X t u) P P
  /-- P3: counts on successive disjoint intervals are independent. -/
  indepIncrements : HasIndepIncrements X P
  /-- P4: every bounded interval has a finite first moment. -/
  finiteMean : ∀ s t, s ≤ t →
    Integrable (fun ω ↦ (poissonIntervalCount X s t ω : ℝ)) P
  /-- P5: the probability of two or more events in an interval of length `ε` is `o(ε)`.
  This is stated in Klenke's exact `limsup` form. -/
  rareMultipleJump :
    limsup (fun ε : ℝ ↦
      P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε)
      (𝓝[>] 0) = 0

/-- The exact upper tail of a Poisson law above one. -/
theorem poissonMeasure_real_Ici_two (r : NNReal) :
    (poissonMeasure r).real (Ici 2) =
      1 - Real.exp (-r) - Real.exp (-r) * r := by
  have hcompl : Ici (2 : ℕ) = (Iic (1 : ℕ))ᶜ := by
    ext n
    simp only [mem_Ici, mem_compl_iff, mem_Iic]
    omega
  have hsmall : Iic (1 : ℕ) = ({0} : Set ℕ) ∪ {1} := by
    ext n
    simp only [mem_Iic, mem_union, mem_singleton_iff]
    omega
  rw [hcompl, measureReal_compl measurableSet_Iic, hsmall,
    measureReal_union (Set.disjoint_singleton_left.2 (by simp)) (MeasurableSet.singleton 1),
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  norm_num
  ring

/-- The Poisson upper tail above one is little-oh of its rate at zero. -/
theorem tendsto_poisson_two_or_more_div (r : NNReal) : Tendsto
    (fun x : ℝ ↦ (1 - Real.exp (-(r : ℝ) * x) -
      Real.exp (-(r : ℝ) * x) * (r : ℝ) * x) / x)
    (𝓝[>] 0) (𝓝 0) := by
  have hg : HasDerivAt (fun x : ℝ ↦ -(r : ℝ) * x) (-(r : ℝ)) 0 :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id 0).const_mul (-(r : ℝ))
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (-(r : ℝ) * x))
      (Real.exp (-(r : ℝ) * 0) * (-(r : ℝ))) 0 :=
    (Real.hasDerivAt_exp (-(r : ℝ) * 0)).comp 0 hg
  have hd := ((hasDerivAt_const (x := 0) (c := (1 : ℝ))).sub he).sub
    ((he.mul_const (r : ℝ)).mul (hasDerivAt_id 0))
  have hs := hd.tendsto_slope_zero_right
  simpa [smul_eq_mul, inv_mul_eq_div] using hs

/-- The natural-number coordinate is integrable under every Poisson law. -/
theorem integrable_natCast_poisson (r : NNReal) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff, ← summable_nat_add_iff 1]
  refine ((Real.summable_pow_div_factorial (r : ℝ)).mul_left
      (Real.exp (-(r : ℝ)) * (r : ℝ))).congr fun n ↦ ?_
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_factorial, pow_succ]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- A random variable with a Poisson law has a finite first moment. -/
theorem HasLaw.integrable_natCast_poissonMeasure {P : Measure Ω} {Y : Ω → ℕ} {r : NNReal}
    (hY : HasLaw Y (poissonMeasure r) P) : Integrable (fun ω ↦ (Y ω : ℝ)) P := by
  have hmap : Integrable (fun n : ℕ ↦ (n : ℝ)) (P.map Y) := by
    rw [hY.map_eq]
    exact integrable_natCast_poisson r
  simpa only [Function.comp_def] using hmap.comp_aemeasurable hY.aemeasurable

namespace IsPoissonProcess

variable {X : NNReal → Ω → ℕ} {rate : NNReal} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Every Poisson process satisfies Klenke's interval-count axioms P1--P5. -/
theorem satisfiesPoissonIntervalAxioms (hX : IsPoissonProcess X rate P) :
    SatisfiesPoissonIntervalAxioms X P := by
  refine
    { aemeasurable := hX.aemeasurable
      initial := hX.initial
      monotonePaths := hX.monotonePaths
      rightContinuousPaths := hX.rightContinuousPaths
      intervalAdditive := ?_
      stationaryIntervalLaw := ?_
      indepIncrements := hX.indepIncrements
      finiteMean := ?_
      rareMultipleJump := ?_ }
  · intro r s t hrs hst
    filter_upwards [hX.monotonePaths] with ω hmono
    simp only [poissonIntervalCount]
    have hrs' := hmono hrs
    have hst' := hmono hst
    change X r ω ≤ X s ω at hrs'
    change X s ω ≤ X t ω at hst'
    omega
  · intro r s t u hrs htu hlen
    have h₁ := hX.incrementLaw r s hrs
    have h₂ := hX.incrementLaw t u htu
    have h₁' : HasLaw (poissonIntervalCount X r s)
        (poissonMeasure (rate * (s - r))) P := by
      change HasLaw (fun ω ↦ X s ω - X r ω) (poissonMeasure (rate * (s - r))) P
      exact h₁
    have h₂' : HasLaw (poissonIntervalCount X t u)
        (poissonMeasure (rate * (s - r))) P := by
      rw [hlen]
      change HasLaw (fun ω ↦ X u ω - X t ω) (poissonMeasure (rate * (u - t))) P
      exact h₂
    exact h₁'.identDistrib h₂'
  · intro s t hst
    exact (hX.incrementLaw s t hst).integrable_natCast_poissonMeasure
  · have htend : Tendsto
        (fun ε : ℝ ↦
          P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε)
        (𝓝[>] 0) (𝓝 0) := by
      apply (tendsto_poisson_two_or_more_div rate).congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : 0 < ε := hε
      have hLaw := hX.incrementLaw 0 (Real.toNNReal ε) bot_le
      have hmeasure :
          P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} =
            (poissonMeasure (rate * Real.toNNReal ε)).real (Ici 2) := by
        have hm := hLaw.measureReal_eq (p := fun n : ℕ ↦ 2 ≤ n) measurableSet_Ici
        simp only [tsub_zero] at hm
        change P.real {ω | 2 ≤ X (Real.toNNReal ε) ω - X 0 ω} =
          (poissonMeasure (rate * Real.toNNReal ε)).real {n | 2 ≤ n} at hm
        change P.real {ω | 2 ≤ X (Real.toNNReal ε) ω - X 0 ω} =
          (poissonMeasure (rate * Real.toNNReal ε)).real (Ici 2)
        rw [show Ici (2 : ℕ) = {n | 2 ≤ n} by ext n; simp]
        exact hm
      rw [hmeasure, poissonMeasure_real_Ici_two]
      simp [Real.coe_toNNReal ε hεpos.le]
      ring
    exact htend.limsup_eq

end IsPoissonProcess

end ProbabilityTheory
