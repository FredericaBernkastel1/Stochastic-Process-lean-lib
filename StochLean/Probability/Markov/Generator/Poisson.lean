/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Generator.Uniqueness
public import StochLean.Probability.Process.Poisson.Basic

/-!
# The Poisson counting Q-matrix

The pure-birth counting generator is the acceptance test for uniformization.  Its only
off-diagonal transition is from `x` to `x + 1`; starting from zero, the uniformized transition
law is Mathlib's canonical `poissonMeasure`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Generator of a Poisson counting process with the given nonnegative rate. -/
def poissonQMatrix (rate : ℝ≥0) (x y : ℕ) : ℝ :=
  if y = x + 1 then rate else if y = x then -rate else 0

/-- The Poisson counting generator is a conservative Q-matrix. -/
theorem isQMatrix_poissonQMatrix (rate : ℝ≥0) : IsQMatrix (poissonQMatrix rate) := by
  constructor
  · intro x y hxy
    by_cases hy : y = x + 1
    · simp [poissonQMatrix, hy]
    · simp [poissonQMatrix, hy, Ne.symm hxy]
  · intro x
    let z : {y : ℕ // y ≠ x} := ⟨x + 1, Nat.succ_ne_self x⟩
    apply summable_of_ne_finset_zero (s := {z})
    intro y hy
    have hyz : y ≠ z := by simpa using hy
    have hsucc : (y : ℕ) ≠ x + 1 := by
      intro h
      apply hyz
      exact Subtype.ext h
    simp [poissonQMatrix, hsucc, y.property]
  · intro x
    let z : {y : ℕ // y ≠ x} := ⟨x + 1, Nat.succ_ne_self x⟩
    rw [tsum_eq_single z]
    · simp [poissonQMatrix, z]
    · intro y hy
      have hsucc : (y : ℕ) ≠ x + 1 := by
        intro h
        apply hy
        exact Subtype.ext h
      simp [poissonQMatrix, hsucc, y.property]

/-- Every state of the Poisson counting generator has the declared exit rate. -/
theorem exitRate_poissonQMatrix (rate : ℝ≥0) (x : ℕ) :
    exitRate (poissonQMatrix rate) x = rate := by
  simp [exitRate, poissonQMatrix]

/-- The Poisson rate itself dominates all exit rates. -/
theorem isUniformizationRate_poissonQMatrix (rate : ℝ≥0) :
    IsUniformizationRate (poissonQMatrix rate) rate where
  nonneg := rate.coe_nonneg
  dominates x := by rw [exitRate_poissonQMatrix]

/-- At positive rate, one uniformization step is the deterministic successor kernel. -/
theorem uniformizationKernel_poissonQMatrix_of_pos
    (rate : ℝ≥0) (hrate : 0 < rate) :
    uniformizationKernel (poissonQMatrix rate) rate =
      Kernel.deterministic (fun x : ℕ => x + 1) (measurable_of_countable _) := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
  by_cases hyx : y = x
  · subst y
    rw [uniformizationKernel, if_neg (by exact_mod_cast hrate.ne')]
    change positiveUniformizationMeasure (poissonQMatrix rate) rate x {x} = _
    rw [positiveUniformizationMeasure_apply_self]
    simp [exitRate_poissonQMatrix, hrate.ne']
  · rw [uniformizationKernel, if_neg (by exact_mod_cast hrate.ne')]
    change positiveUniformizationMeasure (poissonQMatrix rate) rate x {y} = _
    rw [positiveUniformizationMeasure_apply_of_ne _ _ (Ne.symm hyx)]
    by_cases hsucc : y = x + 1
    · simp [poissonQMatrix, hsucc, hrate.ne']
    · simp [poissonQMatrix, hsucc, hyx]

/-- Powers of the deterministic successor kernel add the step count. -/
theorem deterministicSucc_pow (n : ℕ) :
    (Kernel.deterministic (fun x : ℕ => x + 1) (measurable_of_countable _)) ^ n =
      Kernel.deterministic (fun x : ℕ => x + n) (measurable_of_countable _) := by
  induction n with
  | zero =>
      change Kernel.id =
        Kernel.deterministic (fun x : ℕ => x + 0) (measurable_of_countable _)
      apply Kernel.ext
      intro x
      simp [Kernel.id_apply, Kernel.deterministic_apply]
  | succ n ih =>
      rw [pow_succ', ih]
      change
        Kernel.deterministic (fun x : ℕ => x + 1) (measurable_of_countable _) ∘ₖ
          Kernel.deterministic (fun x : ℕ => x + n) (measurable_of_countable _) = _
      rw [Kernel.deterministic_comp_deterministic]
      apply Kernel.deterministic_congr
      funext x
      simp [Function.comp_def, Nat.add_assoc]

/-- Starting from zero, uniformization of the positive-rate Poisson Q-matrix recovers the
canonical Poisson transition law. -/
theorem uniformizedSemigroup_poissonQMatrix_apply_zero_of_pos
    (rate : ℝ≥0) (hrate : 0 < rate) (t : ℝ≥0) :
    uniformizedSemigroup (poissonQMatrix rate) rate t 0 = poissonMeasure (rate * t) := by
  apply Measure.ext_of_singleton
  intro y
  rw [uniformizedSemigroup, Kernel.sum_apply' _ 0 (measurableSet_singleton y)]
  rw [uniformizationKernel_poissonQMatrix_of_pos rate hrate]
  simp_rw [deterministicSucc_pow, scaleKernel_apply, Measure.smul_apply, smul_eq_mul,
    Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
  rw [tsum_eq_single y]
  · rw [poissonMeasure_singleton]
    simp
  · intro n hny
    simp [hny]

/-- The zero-rate acceptance case also agrees with the canonical degenerate Poisson law. -/
theorem uniformizedSemigroup_poissonQMatrix_apply_zero_zero_rate (t : ℝ≥0) :
    uniformizedSemigroup (poissonQMatrix 0) 0 t 0 = poissonMeasure 0 := by
  rw [uniformizedSemigroup_zero_rate]
  apply Measure.ext_of_singleton
  intro y
  rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
    poissonMeasure_singleton]
  by_cases hy : y = 0
  · subst y
    simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hy
    simp

/-- Uniformization of the Poisson Q-matrix has the expected generator. -/
theorem hasQMatrix_poissonUniformizedSemigroup (rate : ℝ≥0) :
    HasQMatrix (uniformizedSemigroup (poissonQMatrix rate) rate) (poissonQMatrix rate) :=
  hasQMatrix_uniformizedSemigroup (isQMatrix_poissonQMatrix rate)
    (isUniformizationRate_poissonQMatrix rate)

end ProbabilityTheory
