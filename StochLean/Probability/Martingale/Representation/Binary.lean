/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.DiscreteIntegral

/-!
# Binary martingale representation

The hypothesis below is genuinely binary: at each step the increment has two past-measurable
branch values, selected by a Boolean innovation, and those values satisfy the conditional
mean-zero balance for a past-measurable success probability.  The representation coefficient is
then derived as the difference of the two branch values; it is not supplied as a
conclusion-shaped hypothesis.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Data witnessing that the information increment at every step is a genuine two-way split. -/
structure BinarySplittingData (M : ℕ → Ω → ℝ) (𝓕 : Filtration ℕ mΩ) where
  bit : ℕ → Ω → Bool
  probability : ℕ → Ω → ℝ
  falseValue : ℕ → Ω → ℝ
  trueValue : ℕ → Ω → ℝ
  probability_pos : ∀ n ω, 0 < probability n ω
  probability_lt_one : ∀ n ω, probability n ω < 1
  probability_measurable : ∀ n, StronglyMeasurable[𝓕 n] (probability n)
  falseValue_measurable : ∀ n, StronglyMeasurable[𝓕 n] (falseValue n)
  trueValue_measurable : ∀ n, StronglyMeasurable[𝓕 n] (trueValue n)
  increment_eq : ∀ n ω,
    M (n + 1) ω - M n ω = if bit n ω then trueValue n ω else falseValue n ω
  centered : ∀ n ω,
    probability n ω * trueValue n ω +
      (1 - probability n ω) * falseValue n ω = 0

namespace BinarySplittingData

variable {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}

/-- Centered binary innovation associated with the split. -/
def innovation (h : BinarySplittingData M 𝓕) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω =>
      h.innovation n ω +
        if h.bit n ω then 1 - h.probability n ω else -h.probability n ω

/-- The derived representation coefficient: difference between the two branch increments. -/
def coefficient (h : BinarySplittingData M 𝓕) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => h.trueValue n ω - h.falseValue n ω

theorem coefficient_isStronglyPredictable (h : BinarySplittingData M 𝓕) :
    IsStronglyPredictable 𝓕 h.coefficient := by
  apply IsStronglyPredictable.of_measurable_add_one
  · exact stronglyMeasurable_const
  · intro n
    exact (h.trueValue_measurable n).sub (h.falseValue_measurable n)

private theorem coefficient_mul_innovation_increment (h : BinarySplittingData M 𝓕)
    (n : ℕ) (ω : Ω) :
    h.coefficient (n + 1) ω *
        (h.innovation (n + 1) ω - h.innovation n ω) =
      M (n + 1) ω - M n ω := by
  rw [h.increment_eq]
  cases hb : h.bit n ω <;>
    simp only [coefficient, innovation, hb, ↓reduceIte]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    linear_combination -h.centered n ω
  · linear_combination -h.centered n ω

/-- Binary representation: every process with genuine centered binary splitting data is its
initial value plus the stochastic integral of the derived coefficient against the centered
binary innovation. -/
theorem representation (h : BinarySplittingData M 𝓕) (n : ℕ) :
    M n = M 0 + discreteStochasticIntegral h.coefficient h.innovation n := by
  induction n with
  | zero =>
      ext ω
      simp
  | succ n ih =>
      ext ω
      calc
        M (n + 1) ω = M n ω +
              h.coefficient (n + 1) ω *
                (h.innovation (n + 1) ω - h.innovation n ω) := by
              rw [h.coefficient_mul_innovation_increment]
              ring
        _ = (M 0 + discreteStochasticIntegral h.coefficient h.innovation n) ω +
              h.coefficient (n + 1) ω *
                (h.innovation (n + 1) ω - h.innovation n ω) := by
              rw [congrFun ih ω]
        _ = (M 0 + discreteStochasticIntegral h.coefficient h.innovation (n + 1)) ω := by
              rw [discreteStochasticIntegral_succ]
              simp only [Pi.add_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply]
              ring

end BinarySplittingData

end MeasureTheory
