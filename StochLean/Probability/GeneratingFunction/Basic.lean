/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability generating functions

The probability generating function is defined from a Mathlib `PMF ℕ`, hence from the law rather
than from a chosen random-variable realization. Its public domain is `unitInterval`; no value of a
possibly divergent power series outside the natural basic domain is exposed.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PMF

noncomputable section

/-- The real-valued mass of a natural-number-valued probability law. -/
def massReal (p : PMF ℕ) (n : ℕ) : ℝ :=
  (p n).toReal

lemma massReal_nonneg (p : PMF ℕ) (n : ℕ) : 0 ≤ p.massReal n :=
  ENNReal.toReal_nonneg

lemma massReal_le_one (p : PMF ℕ) (n : ℕ) : p.massReal n ≤ 1 := by
  simpa only [massReal, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one n)

lemma summable_massReal (p : PMF ℕ) : Summable p.massReal := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

@[simp]
lemma tsum_massReal (p : PMF ℕ) : ∑' n, p.massReal n = 1 := by
  have hp : (∑' n, (p n).toNNReal) = (1 : NNReal) := by
    rw [NNReal.tsum_eq_toNNReal_tsum]
    simp_rw [ENNReal.coe_toNNReal (p.apply_ne_top _)]
    rw [p.tsum_coe]
    rfl
  change (∑' n, ((p n).toNNReal : ℝ)) = 1
  rw [← NNReal.coe_tsum, hp]
  rfl

/-- A natural-number-valued probability law is determined by its real masses. -/
theorem ext_massReal {p q : PMF ℕ} (h : ∀ n, p.massReal n = q.massReal n) : p = q := by
  apply PMF.ext
  intro n
  exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top n) (q.apply_ne_top n)).mp (h n)

lemma massReal_bind (p : PMF ℕ) (q : ℕ → PMF ℕ) (k : ℕ) :
    (p.bind q).massReal k = ∑' n, p.massReal n * (q n).massReal k := by
  rw [massReal, PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul, massReal]
  · intro n
    exact ENNReal.mul_ne_top (p.apply_ne_top n) ((q n).apply_ne_top k)

/-- The probability generating function of a probability mass function, on its unconditional
domain of convergence `[0, 1]`. -/
def pgf (p : PMF ℕ) (z : unitInterval) : ℝ :=
  ∑' n, p.massReal n * (z : ℝ) ^ n

@[simp]
lemma pgf_pure (n : ℕ) (z : unitInterval) : (PMF.pure n).pgf z = (z : ℝ) ^ n := by
  rw [pgf, tsum_eq_single n]
  · simp [massReal]
  · intro b hb
    simp [massReal, PMF.pure_apply, hb]

lemma summable_pgf (p : PMF ℕ) (z : unitInterval) :
    Summable fun n ↦ p.massReal n * (z : ℝ) ^ n := by
  apply Summable.of_norm_bounded p.summable_massReal
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.massReal_nonneg n),
    abs_of_nonneg (pow_nonneg z.property.1 n)]
  exact mul_le_of_le_one_right (p.massReal_nonneg n)
    (pow_le_one₀ z.property.1 z.property.2)

@[simp]
lemma pgf_one (p : PMF ℕ) : p.pgf 1 = 1 := by
  simp [pgf]

@[simp]
lemma pgf_zero (p : PMF ℕ) : p.pgf 0 = p.massReal 0 := by
  rw [pgf, tsum_eq_single 0]
  · simp
  · intro b hb
    simp [zero_pow hb]

lemma pgf_nonneg (p : PMF ℕ) (z : unitInterval) : 0 ≤ p.pgf z :=
  tsum_nonneg fun n ↦ mul_nonneg (p.massReal_nonneg n) (pow_nonneg z.property.1 n)

lemma pgf_le_one (p : PMF ℕ) (z : unitInterval) : p.pgf z ≤ 1 := by
  rw [← p.tsum_massReal]
  exact Summable.tsum_le_tsum
    (fun n ↦ mul_le_of_le_one_right (p.massReal_nonneg n)
      (pow_le_one₀ z.property.1 z.property.2))
    (p.summable_pgf z) p.summable_massReal

lemma pgf_mem_unitInterval (p : PMF ℕ) (z : unitInterval) : p.pgf z ∈ unitInterval :=
  ⟨p.pgf_nonneg z, p.pgf_le_one z⟩

lemma monotone_pgf (p : PMF ℕ) : Monotone p.pgf := by
  intro x y hxy
  exact Summable.tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ x.property.1 hxy n)
      (p.massReal_nonneg n))
    (p.summable_pgf x) (p.summable_pgf y)

/-- The PGF of a monadic mixture is the corresponding mixture of PGFs. -/
lemma pgf_bind (p : PMF ℕ) (q : ℕ → PMF ℕ) (z : unitInterval) :
    (p.bind q).pgf z = ∑' n, p.massReal n * (q n).pgf z := by
  let f : ℕ × ℕ → ℝ := fun x ↦
    p.massReal x.1 * (q x.1).massReal x.2 * (z : ℝ) ^ x.2
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x ↦
    mul_nonneg (mul_nonneg (p.massReal_nonneg x.1) ((q x.1).massReal_nonneg x.2))
      (pow_nonneg z.property.1 x.2)
  have hf : Summable f := by
    rw [summable_prod_of_nonneg hf_nonneg]
    constructor
    · intro n
      simpa only [f, mul_assoc] using ((q n).summable_pgf z).mul_left (p.massReal n)
    · apply Summable.of_nonneg_of_le
          (fun n ↦ tsum_nonneg fun k ↦ hf_nonneg (n, k)) (fun n ↦ ?_)
          p.summable_massReal
      rw [show (∑' k, f (n, k)) = p.massReal n * (q n).pgf z by
        rw [pgf, ← (q n).summable_pgf z |>.tsum_mul_left (p.massReal n)]
        apply tsum_congr
        intro k
        simp only [f]
        ring]
      exact mul_le_of_le_one_right (p.massReal_nonneg n) ((q n).pgf_le_one z)
  rw [pgf]
  simp_rw [massReal_bind]
  calc
    ∑' k, (∑' n, p.massReal n * (q n).massReal k) * (z : ℝ) ^ k =
        ∑' k, ∑' n, f (n, k) := by
          apply tsum_congr
          intro k
          have hk : Summable fun n ↦ p.massReal n * (q n).massReal k := by
            exact p.summable_massReal.of_nonneg_of_le
              (fun n ↦ mul_nonneg (p.massReal_nonneg n) ((q n).massReal_nonneg k))
              (fun n ↦ mul_le_of_le_one_right (p.massReal_nonneg n)
                ((q n).massReal_le_one k))
          rw [← hk.tsum_mul_right ((z : ℝ) ^ k)]
    _ = ∑' n, ∑' k, f (n, k) := hf.tsum_comm
    _ = ∑' n, p.massReal n * (q n).pgf z := by
      apply tsum_congr
      intro n
      rw [pgf, ← (q n).summable_pgf z |>.tsum_mul_left (p.massReal n)]
      apply tsum_congr
      intro k
      simp only [f]
      ring

/-- Mapping a natural-number-valued law transforms its PGF by substituting the mapped exponent. -/
lemma pgf_map (p : PMF ℕ) (g : ℕ → ℕ) (z : unitInterval) :
    (p.map g).pgf z = ∑' n, p.massReal n * (z : ℝ) ^ g n := by
  rw [← p.bind_pure_comp g, pgf_bind]
  apply tsum_congr
  intro n
  simp only [Function.comp_apply, pgf_pure]

/-- A measure-level law bridge. This is the same PGF after converting a discrete probability
measure to Mathlib's canonical `PMF`. -/
def _root_.MeasureTheory.Measure.pgf (μ : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure μ] (z : unitInterval) : ℝ :=
  μ.toPMF.pgf z

@[simp]
lemma pgf_toMeasure (p : PMF ℕ) (z : unitInterval) : p.toMeasure.pgf z = p.pgf z := by
  simp only [MeasureTheory.Measure.pgf, PMF.toMeasure_toPMF]

end

end PMF
