/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.EmpiricalProcess.CDF
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Sym.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Empirical probability measures

The sample-size parameter is `n`, but the sample contains the first `n + 1` observations. Thus the
empty-sample case is absent from the type-level API, matching `empiricalCDF`.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace E]

/-- The unordered tuple represented by a finite vector.  This is the plain set-theoretic
quotient by coordinate permutations. -/
def unorderedTuple {n : ℕ} (x : Fin n → E) : Sym E n :=
  Sym.ofVector (List.Vector.ofFn x)

omit [MeasurableSpace E] in
theorem coe_unorderedTuple {n : ℕ} (x : Fin n → E) :
    (unorderedTuple x : Multiset E) = (List.ofFn x : Multiset E) := by
  rw [unorderedTuple, Sym.ofVector]
  apply Multiset.coe_eq_coe.mpr
  change (List.Vector.ofFn x).toList.Perm (List.ofFn x)
  rw [List.Vector.toList_ofFn]

/-- Multiplicity in a multiset, with the classical equality decision kept inside the definition
instead of exposed as a mathematical hypothesis. -/
noncomputable def multisetMultiplicity (a : E) (s : Multiset E) : ℕ :=
  @Multiset.countP E (fun b ↦ b = a) (Classical.decPred _) s

omit [MeasurableSpace E] in
private theorem card_filter_eq_multisetMultiplicity [DecidableEq E]
    {n : ℕ} (x : Fin n → E) (a : E) :
    (Finset.univ.filter fun i ↦ x i = a).card =
      Multiset.countP (fun b ↦ b = a) (List.ofFn x : Multiset E) := by
  rw [← Fin.univ_val_map x, Multiset.countP_map]
  rfl

/-- The empirical probability measure of a nonempty finite tuple.  Its type enforces a sample
size of `n + 1`, so division by zero cannot occur. -/
noncomputable def empiricalProbabilityMeasureOfTuple {n : ℕ} (x : Fin (n + 1) → E) :
    Measure E :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

theorem empiricalProbabilityMeasureOfTuple_apply {n : ℕ} (x : Fin (n + 1) → E)
    {s : Set E} (hs : MeasurableSet s) :
    empiricalProbabilityMeasureOfTuple x s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, s.indicator 1 (x i) := by
  simp [empiricalProbabilityMeasureOfTuple, Measure.smul_apply, hs, Measure.dirac_apply']

instance empiricalProbabilityMeasureOfTuple.instIsProbabilityMeasure
    {n : ℕ} (x : Fin (n + 1) → E) :
    IsProbabilityMeasure (empiricalProbabilityMeasureOfTuple x) where
  measure_univ := by
    rw [empiricalProbabilityMeasureOfTuple_apply x MeasurableSet.univ]
    simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)

theorem empiricalProbabilityMeasureOfTuple_singleton [MeasurableSingletonClass E]
    {n : ℕ} (x : Fin (n + 1) → E) (a : E) :
    empiricalProbabilityMeasureOfTuple x {a} =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        (multisetMultiplicity a (unorderedTuple x : Multiset E) : ℕ) := by
  classical
  rw [empiricalProbabilityMeasureOfTuple_apply x (measurableSet_singleton a)]
  congr 1
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [Finset.sum_boole]
  norm_cast
  rw [coe_unorderedTuple]
  exact_mod_cast card_filter_eq_multisetMultiplicity x a

/-- On a space with measurable singletons, the empirical measure remembers the complete
unordered finite sample, including multiplicities. -/
theorem unorderedTuple_eq_of_empiricalProbabilityMeasureOfTuple_eq
    [MeasurableSingletonClass E] {n : ℕ} {x y : Fin (n + 1) → E}
    (hxy : empiricalProbabilityMeasureOfTuple x = empiricalProbabilityMeasureOfTuple y) :
    unorderedTuple x = unorderedTuple y := by
  classical
  apply Sym.ext
  rw [Multiset.ext]
  intro a
  have hs := congrArg (fun ν : Measure E ↦ ν {a}) hxy
  rw [empiricalProbabilityMeasureOfTuple_singleton x a,
    empiricalProbabilityMeasureOfTuple_singleton y a] at hs
  have hcancel := congrArg
    (fun z : ENNReal ↦ ((n + 1 : ℕ) : ENNReal) * z) hs
  have hN0 : ((n + 1 : ℕ) : ENNReal) ≠ 0 := by simp
  have hNtop : ((n + 1 : ℕ) : ENNReal) ≠ ∞ := by simp
  simp only [← mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, one_mul] at hcancel
  have hmult :
      multisetMultiplicity a (unorderedTuple x : Multiset E) =
        multisetMultiplicity a (unorderedTuple y : Multiset E) := by
    exact_mod_cast hcancel
  simpa [multisetMultiplicity, Multiset.count, eq_comm] using hmult

omit [MeasurableSpace E] in
/-- Two finite tuples have the same unordered tuple exactly strongly enough for one to be
obtained from the other by a coordinate permutation.  This is the finite combinatorial bridge
used by the empirical-measure factorization theorem. -/
theorem exists_perm_of_unorderedTuple_eq {n : ℕ} {x y : Fin n → E}
    (hxy : unorderedTuple x = unorderedTuple y) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, x (σ i) = y i := by
  induction n with
  | zero =>
      exact ⟨Equiv.refl _, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      have hmem : y 0 ∈ List.ofFn x := by
        have hm : (List.ofFn x : Multiset E) = (List.ofFn y : Multiset E) := by
          simpa only [← coe_unorderedTuple] using
            congrArg (fun s : Sym E (n + 1) ↦ (s : Multiset E)) hxy
        rw [← Multiset.mem_coe, hm, Multiset.mem_coe]
        simp
      obtain ⟨p, hp⟩ := (List.mem_ofFn.mp hmem)
      let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
      let x' : Fin (n + 1) → E := fun i ↦ x (τ i)
      have hx'0 : x' 0 = y 0 := by simpa [x', τ] using hp
      have hx' : unorderedTuple x' = unorderedTuple x := by
        apply Sym.ext
        rw [coe_unorderedTuple, coe_unorderedTuple]
        exact Quotient.sound (τ.ofFn_comp_perm x)
      have hm : (List.ofFn x' : Multiset E) = (List.ofFn y : Multiset E) := by
        simpa only [← coe_unorderedTuple] using
          congrArg (fun s : Sym E (n + 1) ↦ (s : Multiset E)) (hx'.trans hxy)
      have htail :
          unorderedTuple (fun i : Fin n ↦ x' i.succ) =
            unorderedTuple (fun i : Fin n ↦ y i.succ) := by
        apply Sym.ext
        rw [coe_unorderedTuple, coe_unorderedTuple]
        rw [List.ofFn_succ, List.ofFn_succ] at hm
        rw [hx'0] at hm
        change y 0 ::ₘ (List.ofFn (fun i : Fin n ↦ x' i.succ) : Multiset E) =
          y 0 ::ₘ (List.ofFn (fun i : Fin n ↦ y i.succ) : Multiset E) at hm
        exact (Multiset.cons_inj_right (y 0)).mp hm
      obtain ⟨ρ, hρ⟩ := ih htail
      let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (p, ρ)
      refine ⟨σ, Fin.cases ?_ ?_⟩
      · simpa [σ] using hp
      · intro i
        simpa [σ, x', τ] using hρ i

/-- The empirical probability measure of the first `n + 1` observations. -/
noncomputable def empiricalProbabilityMeasure (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : Measure E :=
  ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), Measure.dirac (X k ω)

theorem empiricalProbabilityMeasure_apply (X : ℕ → Ω → E) (n : ℕ) (ω : Ω)
    {s : Set E} (hs : MeasurableSet s) :
    empiricalProbabilityMeasure X n ω s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), s.indicator 1 (X k ω) := by
  simp [empiricalProbabilityMeasure, Measure.smul_apply, hs, Measure.dirac_apply']

instance empiricalProbabilityMeasure.instIsProbabilityMeasure
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (empiricalProbabilityMeasure X n ω) where
  measure_univ := by
    rw [empiricalProbabilityMeasure_apply X n ω MeasurableSet.univ]
    simp only [Nat.cast_add, Nat.cast_one, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)

/-- Integrating a real test function against the empirical measure is the finite sample average.

No measurability or ambient integrability hypothesis on `f` is needed: the measure has finite
support and measurable singletons make every point evaluation at a Dirac mass integrable. -/
theorem integral_empiricalProbabilityMeasure [MeasurableSingletonClass E]
    (X : ℕ → Ω → E) (f : E → ℝ) (n : ℕ) (ω : Ω) :
    ∫ x, f x ∂empiricalProbabilityMeasure X n ω =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), f (X k ω) := by
  rw [empiricalProbabilityMeasure, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul]
  · intro k hk
    exact integrable_dirac (by simp)

/-- Evaluating the empirical measure of a real sample on `(-∞, t]` recovers its empirical CDF. -/
theorem empiricalProbabilityMeasure_Iic (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    (empiricalProbabilityMeasure X n ω (Set.Iic t)).toReal =
      empiricalCDFSequence X n ω t := by
  rw [empiricalProbabilityMeasure_apply X n ω measurableSet_Iic]
  rw [empiricalCDFSequence, empiricalCDF_eq_average_indicator]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_sum (by
    intro k hk
    simp only [Set.indicator_apply]
    split <;> simp)]
  simp only [ENNReal.toReal_natCast]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
  split <;> simp

end ProbabilityTheory
