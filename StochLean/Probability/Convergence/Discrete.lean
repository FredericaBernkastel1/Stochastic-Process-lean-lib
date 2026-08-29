/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.Basic
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Convergence of natural-number-valued laws

This file provides the coefficientwise-to-PGF direction of the discrete convergence principle.
The domination is intrinsic: at every `z < 1`, all mass-weighted terms are bounded by the
summable geometric series `z ^ n`; at `z = 1`, every PGF is exactly one.
-/

@[expose] public section

open Filter Topology

namespace PMF

noncomputable section

variable {ι : Type*} {l : Filter ι} {p : ι → PMF ℕ} {q : PMF ℕ}

/-- Coefficientwise convergence of natural-number-valued laws implies convergence of their PGFs
at every point of `[0, 1]`. -/
theorem tendsto_pgf_of_tendsto_mass
    (h : ∀ n, Tendsto (fun i ↦ (p i).massReal n) l (𝓝 (q.massReal n)))
    (z : unitInterval) : Tendsto (fun i ↦ (p i).pgf z) l (𝓝 (q.pgf z)) := by
  by_cases hz : (z : ℝ) = 1
  · have hz' : z = 1 := Subtype.ext hz
    simp only [hz', pgf_one]
    exact tendsto_const_nhds
  · have hzlt : (z : ℝ) < 1 := lt_of_le_of_ne z.property.2 hz
    have hgeom : Summable fun n : ℕ ↦ (z : ℝ) ^ n := by
      apply summable_geometric_of_norm_lt_one
      simpa [Real.norm_eq_abs, abs_of_nonneg z.property.1]
    have ht := tendsto_tsum_of_dominated_convergence
      (𝓕 := l) (f := fun i n ↦ (p i).massReal n * (z : ℝ) ^ n)
      (g := fun n ↦ q.massReal n * (z : ℝ) ^ n)
      (bound := fun n ↦ (z : ℝ) ^ n) hgeom
      (fun n ↦ (h n).mul_const ((z : ℝ) ^ n))
      (Filter.Eventually.of_forall fun i n ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((p i).massReal_nonneg n),
          abs_of_nonneg (pow_nonneg z.property.1 n)]
        exact mul_le_of_le_one_left (pow_nonneg z.property.1 n) ((p i).massReal_le_one n))
    simpa only [pgf] using ht

end

end PMF
