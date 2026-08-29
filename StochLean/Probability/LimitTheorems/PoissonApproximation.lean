/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Poisson approximation

Mathlib `v4.33.0` already contains the point-probability Poisson limit theorem under the canonical
name `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`. StochLean re-exports that
implementation instead of maintaining a duplicate theorem.
-/
