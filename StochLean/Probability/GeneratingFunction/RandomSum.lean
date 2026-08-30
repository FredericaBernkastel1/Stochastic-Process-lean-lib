/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.Analytic
public import Mathlib.Probability.Independence.Integration

/-!
# Convolution powers and random sums

The constructions in this file are law-level objects. `convolutionPow q n` is the law of the sum
of `n` independent variables with law `q`, and `randomSum p q` mixes these laws with count law `p`.
Using `PMF.bind` keeps the independence/product construction canonical and avoids introducing a
second random-variable representation.
-/

@[expose] public section

namespace PMF

noncomputable section

/-- Additive convolution of two probability laws on an additive type. -/
def convolution {A : Type*} [Add A] (p q : PMF A) : PMF A :=
  p.bind fun m ↦ q.map fun n ↦ m + n

/-- The law of the sum of `n` independent variables with common law `p`. -/
def convolutionPow {A : Type*} [AddMonoid A] (p : PMF A) : ℕ → PMF A
  | 0 => PMF.pure 0
  | n + 1 => convolution (convolutionPow p n) p

/-- The law of a random sum with count law `p` and summand law `q`. -/
def randomSum {A : Type*} [AddMonoid A] (p : PMF ℕ) (q : PMF A) : PMF A :=
  p.bind (convolutionPow q)

@[simp]
lemma convolutionPow_zero {A : Type*} [AddMonoid A] (p : PMF A) :
    convolutionPow p 0 = PMF.pure 0 :=
  rfl

@[simp]
lemma convolutionPow_succ {A : Type*} [AddMonoid A] (p : PMF A) (n : ℕ) :
    convolutionPow p (n + 1) = convolution (convolutionPow p n) p :=
  rfl

@[simp]
lemma convolution_pure_pure {A : Type*} [Add A] (m n : A) :
    convolution (PMF.pure m) (PMF.pure n) = PMF.pure (m + n) := by
  simp [convolution, PMF.pure_map]

@[simp]
lemma convolutionPow_pure {A : Type*} [AddMonoid A] (a : A) (n : ℕ) :
    convolutionPow (PMF.pure a) n = PMF.pure (n • a) := by
  induction n with
  | zero => simp
  | succ n ih => simp [convolutionPow, ih, succ_nsmul]

@[simp]
lemma randomSum_pure_count {A : Type*} [AddMonoid A] (n : ℕ) (q : PMF A) :
    randomSum (PMF.pure n) q = convolutionPow q n := by
  simp [randomSum]

@[simp]
lemma randomSum_pure_summand {A : Type*} [AddMonoid A] (p : PMF ℕ) (a : A) :
    randomSum p (PMF.pure a) = p.map fun n ↦ n • a := by
  rw [randomSum]
  have h : convolutionPow (PMF.pure a) = fun n ↦ PMF.pure (n • a) :=
    funext fun n ↦ convolutionPow_pure a n
  rw [h]
  change p.bind (PMF.pure ∘ fun n ↦ n • a) = _
  exact p.bind_pure_comp (fun n ↦ n • a)

@[simp]
lemma randomSum_pure_zero {A : Type*} [AddMonoid A] (p : PMF ℕ) :
    randomSum p (PMF.pure (0 : A)) = PMF.pure 0 := by
  rw [randomSum_pure_summand]
  have h : (fun n : ℕ ↦ n • (0 : A)) = Function.const ℕ 0 := by
    funext n
    simp
  rw [h]
  exact p.map_const (b := (0 : A))

lemma pgf_map_add (p : PMF ℕ) (m : ℕ) (z : unitInterval) :
    (p.map fun n ↦ m + n).pgf z = (z : ℝ) ^ m * p.pgf z := by
  rw [pgf_map, pgf, ← p.summable_pgf z |>.tsum_mul_left ((z : ℝ) ^ m)]
  apply tsum_congr
  intro n
  rw [pow_add]
  ring

/-- The PGF transforms additive convolution into multiplication. -/
lemma pgf_convolution (p q : PMF ℕ) (z : unitInterval) :
    (convolution p q).pgf z = p.pgf z * q.pgf z := by
  rw [convolution, pgf_bind]
  simp_rw [pgf_map_add]
  calc
    ∑' n, p.massReal n * ((z : ℝ) ^ n * q.pgf z) =
        ∑' n, (p.massReal n * (z : ℝ) ^ n) * q.pgf z := by
          apply tsum_congr
          intro n
          ring
    _ = p.pgf z * q.pgf z := by
      rw [p.summable_pgf z |>.tsum_mul_right]
      rfl

/-- The PGF of an `n`-fold convolution is the `n`th power of the original PGF. -/
lemma pgf_convolutionPow (p : PMF ℕ) (n : ℕ) (z : unitInterval) :
    (convolutionPow p n).pgf z = (p.pgf z) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convolutionPow_succ, pgf_convolution, ih, pow_succ]

/-- The random-sum composition formula for probability generating functions. -/
theorem pgf_randomSum (p q : PMF ℕ) (z : unitInterval) :
    (randomSum p q).pgf z =
      p.pgf ⟨q.pgf z, q.pgf_mem_unitInterval z⟩ := by
  rw [randomSum, pgf_bind]
  simp_rw [pgf_convolutionPow]
  rfl

end

end PMF

namespace ProbabilityTheory

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The random-variable form of PGF multiplicativity.  Its law-level counterpart is
`PMF.pgf_convolution`; this bridge keeps the realization-specific statement in terms of the
canonical expectation and `IndepFun`. -/
theorem IndepFun.integral_pow_add_eq_mul [IsProbabilityMeasure P]
    {X Y : Ω → ℕ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hXY : IndepFun X Y P)
    (z : unitInterval) :
    (∫ ω, (z : ℝ) ^ (X ω + Y ω) ∂P) =
      (∫ ω, (z : ℝ) ^ X ω ∂P) * ∫ ω, (z : ℝ) ^ Y ω ∂P := by
  have hm : Measurable fun n : ℕ ↦ (z : ℝ) ^ n := measurable_of_countable _
  have hi := (hXY.comp hm hm).integral_fun_mul_eq_mul_integral
    (hm.comp_aemeasurable hX).aestronglyMeasurable
    (hm.comp_aemeasurable hY).aestronglyMeasurable
  simpa only [pow_add, Function.comp_apply] using hi

/-- If two independent natural-valued random variables have laws `p` and `q`, the PGF of their
sum is the product of the two law-level PGFs. -/
theorem IndepFun.integral_pow_add_eq_pgf_mul [IsProbabilityMeasure P]
    {X Y : Ω → ℕ} {p q : PMF ℕ}
    (hX : HasLaw X p.toMeasure P) (hY : HasLaw Y q.toMeasure P) (hXY : IndepFun X Y P)
    (z : unitInterval) :
    (∫ ω, (z : ℝ) ^ (X ω + Y ω) ∂P) = p.pgf z * q.pgf z := by
  rw [hXY.integral_pow_add_eq_mul hX.aemeasurable hY.aemeasurable,
    ← hX.pgf_eq_integral_pow, ← hY.pgf_eq_integral_pow, PMF.pgf_toMeasure, PMF.pgf_toMeasure]

end ProbabilityTheory
