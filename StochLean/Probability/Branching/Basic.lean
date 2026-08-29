/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.RandomSum

/-!
# Galton--Watson generation laws

For a process started from one ancestor, the next generation is a random sum of independent
offspring counts. The recursion below records this law-level construction directly.
-/

@[expose] public section

namespace ProbabilityTheory.GaltonWatson

noncomputable section

/-- The offspring PGF as an endomorphism of the unit interval. -/
def offspringPGF (offspring : PMF ℕ) (z : unitInterval) : unitInterval :=
  ⟨offspring.pgf z, offspring.pgf_mem_unitInterval z⟩

@[simp]
lemma coe_offspringPGF (offspring : PMF ℕ) (z : unitInterval) :
    (offspringPGF offspring z : ℝ) = offspring.pgf z :=
  rfl

/-- The law of generation `n` in a Galton--Watson process started from one ancestor. -/
def generationLaw (offspring : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 1
  | n + 1 => PMF.randomSum (generationLaw offspring n) offspring

@[simp]
lemma generationLaw_zero (offspring : PMF ℕ) :
    generationLaw offspring 0 = PMF.pure 1 :=
  rfl

@[simp]
lemma generationLaw_succ (offspring : PMF ℕ) (n : ℕ) :
    generationLaw offspring (n + 1) =
      PMF.randomSum (generationLaw offspring n) offspring :=
  rfl

/-- The PGF of the next generation is obtained by composing the current-generation PGF with the
offspring PGF. -/
lemma pgf_generationLaw_succ (offspring : PMF ℕ) (n : ℕ) (z : unitInterval) :
    (generationLaw offspring (n + 1)).pgf z =
      (generationLaw offspring n).pgf
        ⟨offspring.pgf z, offspring.pgf_mem_unitInterval z⟩ := by
  rw [generationLaw_succ, PMF.pgf_randomSum]

/-- The generation-`n` PGF is the `n`-fold iterate of the offspring PGF. -/
theorem pgf_generationLaw_iterate (offspring : PMF ℕ) (n : ℕ) (z : unitInterval) :
    (generationLaw offspring n).pgf z =
      ((offspringPGF offspring)^[n] z : unitInterval) := by
  induction n generalizing z with
  | zero => simp [generationLaw]
  | succ n ih =>
      rw [pgf_generationLaw_succ, ih, Function.iterate_succ_apply]
      rfl

end

end ProbabilityTheory.GaltonWatson
