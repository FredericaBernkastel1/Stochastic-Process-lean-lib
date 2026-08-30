/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Recurrence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Green kernels and occupation counts

The Green value is the extended sum of all transition probabilities, including the visit at time
zero.  The occupation bridge below is stated once for any path law with the required one-time
marginals, so later constructions need only establish their marginal formula.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace Kernel

variable {E : Type*} [MeasurableSpace E]

/-- The Green kernel, or expected total number of visits at the level of transition powers. -/
noncomputable def green (κ : Kernel E E) (x y : E) : ℝ≥0∞ :=
  ∑' n : ℕ, (κ ^ n) x {y}

/-- Every fixed-time transition mass is bounded by the Green value. -/
theorem pow_apply_le_green (κ : Kernel E E) (x y : E) (n : ℕ) :
    (κ ^ n) x {y} ≤ κ.green x y :=
  ENNReal.le_tsum n

/-- Green values are nonnegative. -/
theorem green_nonneg (κ : Kernel E E) (x y : E) : 0 ≤ κ.green x y :=
  bot_le

/-- Taking a fixed path from `x` to `y` before accumulating visits gives a lower bound on the
Green kernel. -/
theorem pow_mul_green_le_green [MeasurableSingletonClass E]
    (κ : Kernel E E) [IsMarkovKernel κ] (x y z : E) (m : ℕ) :
    (κ ^ m) x {y} * κ.green y z ≤ κ.green x z := by
  rw [green, green, ← ENNReal.tsum_mul_left]
  calc
    (∑' n : ℕ, (κ ^ m) x {y} * (κ ^ n) y {z}) ≤
        ∑' n : ℕ, (κ ^ (m + n)) x {z} := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
      calc
        (κ ^ m) x {y} * (κ ^ n) y {z} =
            ∫⁻ a in {y}, (κ ^ n) a {z} ∂(κ ^ m) x := by
              rw [lintegral_singleton]
              ring
        _ ≤ ∫⁻ a, (κ ^ n) a {z} ∂(κ ^ m) x :=
          setLIntegral_le_lintegral _ _
    _ ≤ ∑' n : ℕ, (κ ^ n) x {z} :=
      ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_left_cancel h)
        (fun n => (κ ^ n) x {z})

/-- Accumulating visits before taking a fixed path from `y` to `z` gives the complementary Green
lower bound. -/
theorem green_mul_pow_le_green [MeasurableSingletonClass E]
    (κ : Kernel E E) [IsMarkovKernel κ] (x y z : E) (m : ℕ) :
    κ.green x y * (κ ^ m) y {z} ≤ κ.green x z := by
  rw [green, green, ← ENNReal.tsum_mul_right]
  calc
    (∑' n : ℕ, (κ ^ n) x {y} * (κ ^ m) y {z}) ≤
        ∑' n : ℕ, (κ ^ (n + m)) x {z} := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [Kernel.pow_add_apply_eq_lintegral κ n m x (measurableSet_singleton z)]
      calc
        (κ ^ n) x {y} * (κ ^ m) y {z} =
            ∫⁻ a in {y}, (κ ^ m) a {z} ∂(κ ^ n) x := by
              rw [lintegral_singleton]
              ring
        _ ≤ ∫⁻ a, (κ ^ m) a {z} ∂(κ ^ n) x :=
          setLIntegral_le_lintegral _ _
    _ ≤ ∑' n : ℕ, (κ ^ n) x {z} :=
      ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h)
        (fun n => (κ ^ n) x {z})

/-- Infinite Green mass propagates along a reachable prefix. -/
theorem green_eq_top_of_canReach_left [MeasurableSingletonClass E]
    (κ : Kernel E E) [IsMarkovKernel κ] {x y z : E}
    (hxy : κ.CanReach x y) (hyz : κ.green y z = ∞) :
    κ.green x z = ∞ := by
  obtain ⟨m, hm⟩ := hxy
  have hbound := pow_mul_green_le_green κ x y z m
  rw [hyz] at hbound
  have hne : (κ ^ m) x {y} ≠ 0 := ne_of_gt hm
  rw [ENNReal.mul_top hne] at hbound
  exact top_unique hbound

/-- Infinite Green mass propagates along a reachable suffix. -/
theorem green_eq_top_of_canReach_right [MeasurableSingletonClass E]
    (κ : Kernel E E) [IsMarkovKernel κ] {x y z : E}
    (hxy : κ.green x y = ∞) (hyz : κ.CanReach y z) :
    κ.green x z = ∞ := by
  obtain ⟨m, hm⟩ := hyz
  have hbound := green_mul_pow_le_green κ x y z m
  rw [hxy] at hbound
  have hne : (κ ^ m) y {z} ≠ 0 := ne_of_gt hm
  rw [ENNReal.top_mul hne] at hbound
  exact top_unique hbound

/-- Infinite diagonal Green mass is constant on communicating states. -/
theorem green_self_eq_top_of_communicates [MeasurableSingletonClass E]
    (κ : Kernel E E) [IsMarkovKernel κ] {x y : E}
    (hxy : κ.CanReach x y) (hyx : κ.CanReach y x)
    (hx : κ.green x x = ∞) : κ.green y y = ∞ := by
  have hxx_to_xy : κ.green x y = ∞ := green_eq_top_of_canReach_right κ hx hxy
  exact green_eq_top_of_canReach_left κ hyx hxx_to_xy

end Kernel

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Extended expected number of visits to `y` under an arbitrary path law. -/
noncomputable def expectedVisits (μ : Measure (ℕ → E)) (y : E) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' n : ℕ, ({z : ℕ → E | z n = y}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂μ

/-- Occupation formula for a path law whose one-time marginals are the kernel powers. -/
theorem expectedVisits_eq_green_of_marginals
    (κ : Kernel E E) (x y : E) (μ : Measure (ℕ → E))
    (hmarg : ∀ n : ℕ, μ {z | z n = y} = (κ ^ n) x {y}) :
    expectedVisits μ y = κ.green x y := by
  have hset (n : ℕ) : MeasurableSet {z : ℕ → E | z n = y} :=
    (show Measurable (fun z : ℕ → E => z n) from measurable_pi_apply n)
      (measurableSet_singleton y)
  rw [expectedVisits, Kernel.green, lintegral_tsum]
  apply tsum_congr
  intro n
  rw [lintegral_indicator]
  · simp [hmarg n]
  · exact hset n
  · exact fun n =>
      (measurable_const.indicator (hset n)).aemeasurable

/-- The canonical Markov-chain path law realizes the Green kernel as an expected visit count. -/
theorem expectedVisits_markovChainLaw_eq_green
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    expectedVisits (markovChainLaw κ x) y = κ.green x y := by
  apply expectedVisits_eq_green_of_marginals κ x y (markovChainLaw κ x)
  intro n
  exact markovChainLaw_apply_coordinate κ x n (measurableSet_singleton y)

end ProbabilityTheory
