/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Branching.Basic
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Extinction probabilities for Galton--Watson processes

Starting from zero, iterating the offspring PGF gives the probability of extinction by a finite
generation. The increasing limit is the least fixed point of the PGF on `[0, 1]`.
-/

@[expose] public section

open Filter Topology

namespace ProbabilityTheory.GaltonWatson

noncomputable section

/-- The finite-generation extinction approximation obtained by iterating the offspring PGF at
zero. -/
def extinctionApprox (offspring : PMF ℕ) : ℕ → unitInterval
  | 0 => 0
  | n + 1 => ⟨offspring.pgf (extinctionApprox offspring n),
      offspring.pgf_mem_unitInterval (extinctionApprox offspring n)⟩

@[simp]
lemma extinctionApprox_zero (offspring : PMF ℕ) : extinctionApprox offspring 0 = 0 :=
  rfl

@[simp]
lemma extinctionApprox_succ (offspring : PMF ℕ) (n : ℕ) :
    extinctionApprox offspring (n + 1) =
      ⟨offspring.pgf (extinctionApprox offspring n),
        offspring.pgf_mem_unitInterval (extinctionApprox offspring n)⟩ :=
  rfl

lemma extinctionApprox_le_succ (offspring : PMF ℕ) (n : ℕ) :
    extinctionApprox offspring n ≤ extinctionApprox offspring (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      change offspring.pgf (extinctionApprox offspring n) ≤
        offspring.pgf (extinctionApprox offspring (n + 1))
      exact offspring.monotone_pgf ih

/-- The finite-generation extinction approximations form an increasing sequence. -/
lemma monotone_extinctionApprox (offspring : PMF ℕ) :
    Monotone (extinctionApprox offspring) :=
  monotone_nat_of_le_succ (extinctionApprox_le_succ offspring)

/-- The eventual extinction probability, defined as the increasing supremum of the
finite-generation approximations. -/
def extinctionProbability (offspring : PMF ℕ) : unitInterval :=
  ⨆ n, extinctionApprox offspring n

lemma extinctionApprox_le_probability (offspring : PMF ℕ) (n : ℕ) :
    extinctionApprox offspring n ≤ extinctionProbability offspring :=
  le_iSup (extinctionApprox offspring) n

/-- The finite-generation approximations converge to the extinction probability. -/
theorem tendsto_extinctionApprox (offspring : PMF ℕ) :
    Tendsto (extinctionApprox offspring) atTop (𝓝 (extinctionProbability offspring)) :=
  tendsto_atTop_iSup (monotone_extinctionApprox offspring)

/-- The extinction probability is a fixed point of the offspring PGF. -/
theorem pgf_extinctionProbability (offspring : PMF ℕ) :
    offspring.pgf (extinctionProbability offspring) = extinctionProbability offspring := by
  have hlim := tendsto_extinctionApprox offspring
  have hpgf : Tendsto (fun n ↦ offspring.pgf (extinctionApprox offspring n)) atTop
      (𝓝 (offspring.pgf (extinctionProbability offspring))) :=
    offspring.continuous_pgf.continuousAt.tendsto.comp hlim
  have hshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hshiftReal :
      Tendsto (fun n ↦ ((extinctionApprox offspring (n + 1) : unitInterval) : ℝ)) atTop
        (𝓝 ((extinctionProbability offspring : unitInterval) : ℝ)) :=
    (continuous_subtype_val.tendsto (extinctionProbability offspring)).comp hshift
  have hlim' : Tendsto (fun n ↦ offspring.pgf (extinctionApprox offspring n)) atTop
      (𝓝 (extinctionProbability offspring)) := by
    simpa only [extinctionApprox_succ] using hshiftReal
  exact tendsto_nhds_unique hpgf hlim'

lemma extinctionApprox_le_fixed (offspring : PMF ℕ) {s : unitInterval}
    (hs : offspring.pgf s = s) (n : ℕ) : extinctionApprox offspring n ≤ s := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      change offspring.pgf (extinctionApprox offspring n) ≤ s
      calc
        offspring.pgf (extinctionApprox offspring n) ≤ offspring.pgf s :=
          offspring.monotone_pgf ih
        _ = s := hs

/-- The extinction probability is the least fixed point of the offspring PGF on `[0, 1]`. -/
theorem extinctionProbability_le_fixed (offspring : PMF ℕ) {s : unitInterval}
    (hs : offspring.pgf s = s) : extinctionProbability offspring ≤ s := by
  apply iSup_le
  exact extinctionApprox_le_fixed offspring hs

end

end ProbabilityTheory.GaltonWatson
