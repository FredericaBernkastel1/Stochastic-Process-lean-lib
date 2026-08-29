/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.Basic
public import Mathlib.Probability.Distributions.Geometric

/-!
# Probability-generating-function domain regression

The sparse heavy-tailed law below has a perfectly valid PGF on `[0,1]`, while its formal power
series diverges at every real `z > 1`.  This guards the basic API against silently totalizing an
out-of-domain series.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace PMF

noncomputable section

def sparseHalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- A geometric law transported to the square numbers. -/
def sparseHeavyTail : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure sparseHalf).toPMF.map fun n ↦ n ^ 2

private theorem square_injective : Function.Injective (fun n : ℕ ↦ n ^ 2) :=
  Nat.pow_left_injective (by decide)

theorem sparseHeavyTail_massReal_square (n : ℕ) :
    sparseHeavyTail.massReal (n ^ 2) = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [massReal, sparseHeavyTail, PMF.map_apply, tsum_eq_single n]
  · rw [if_pos rfl, Measure.toPMF_apply,
      ProbabilityTheory.geometricMeasure_singleton (p := sparseHalf) (by
        intro h
        have hv := congrArg Subtype.val h
        norm_num [sparseHalf] at hv)]
    rw [ENNReal.toReal_ofReal]
    · calc
        (1 - (sparseHalf : ℝ)) ^ n * (sparseHalf : ℝ) =
            (1 / 2 : ℝ) ^ n * (1 / 2) := by norm_num [sparseHalf]
        _ = (1 / 2 : ℝ) ^ (n + 1) := (pow_succ _ _).symm
    · exact ProbabilityTheory.geometricMeasure_nonneg sparseHalf n
  · intro b hbn
    rw [if_neg]
    exact fun hsq ↦ hbn (square_injective hsq.symm)

/-- For this law the real power series is non-summable at every `z > 1`. -/
theorem not_summable_sparseHeavyTail_mul_pow {z : ℝ} (hz : 1 < z) :
    ¬ Summable (fun n ↦ sparseHeavyTail.massReal n * z ^ n) := by
  intro hsum
  have hsub : Summable (fun n ↦
      sparseHeavyTail.massReal (n ^ 2) * z ^ (n ^ 2)) :=
    hsum.comp_injective square_injective
  have htend := hsub.tendsto_atTop_zero
  have hzpow : ∀ᶠ n in atTop, (2 : ℝ) ≤ z ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hz).eventually_ge_atTop 2
  have hlower : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ sparseHeavyTail.massReal (n ^ 2) * z ^ (n ^ 2) := by
    filter_upwards [hzpow] with n hn
    rw [sparseHeavyTail_massReal_square]
    have hznonneg : 0 ≤ z := le_trans (by norm_num) hz.le
    have hpow : (2 : ℝ) ^ n ≤ z ^ (n ^ 2) := by
      calc
        (2 : ℝ) ^ n ≤ (z ^ n) ^ n := pow_le_pow_left₀ (by norm_num) hn n
        _ = z ^ (n ^ 2) := by rw [← pow_mul, pow_two]
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (n + 1) * 2 ^ n := by
        calc
          (1 / 2 : ℝ) = (1 / 2) * (((1 / 2) * 2) ^ n) := by norm_num
          _ = (1 / 2 : ℝ) ^ (n + 1) * 2 ^ n := by
            rw [mul_pow, pow_succ]
            ring
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) * z ^ (n ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _)
  have hsmall : ∀ᶠ n in atTop,
      sparseHeavyTail.massReal (n ^ 2) * z ^ (n ^ 2) < 1 / 4 := by
    have hopen : Set.Iio (1 / 4 : ℝ) ∈ 𝓝 0 := by
      exact Iio_mem_nhds (by norm_num)
    exact htend.eventually hopen
  obtain ⟨n, hn, h'n⟩ := (hlower.and hsmall).exists
  linarith

/-- The basic `[0,1]` PGF remains available for the same heavy-tailed law. -/
example (z : unitInterval) : ℝ := sparseHeavyTail.pgf z

end

end PMF
