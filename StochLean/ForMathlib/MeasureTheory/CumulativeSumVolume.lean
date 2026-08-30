/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.SimplexVolume
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Volume preservation for cumulative sums

The cumulative-sum map from interarrival gaps to ordered arrival coordinates is unit lower
triangular.  This module proves that it preserves finite-dimensional Lebesgue measure and uses
that fact to evaluate ordered simplices and finite products of ordered arrival blocks.
-/

@[expose] public section

open Set Finset
open scoped ENNReal

namespace MeasureTheory

noncomputable section

/-- The unit lower-triangular matrix implementing finite cumulative sums. -/
def cumulativeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if j ≤ i then 1 else 0

@[simp]
lemma cumulativeMatrix_det (n : ℕ) : (cumulativeMatrix n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [cumulativeMatrix]
  · intro i j hij
    have h : ¬j ≤ i := not_le.mpr (by simpa using hij)
    simp [cumulativeMatrix, h]

/-- Cumulative sums as a linear equivalence. -/
def cumulativeLinearEquiv (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) (cumulativeMatrix n)
    (by rw [cumulativeMatrix_det]; exact isUnit_one)

@[simp]
lemma cumulativeLinearEquiv_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    cumulativeLinearEquiv n x i = ∑ j ∈ Finset.Iic i, x j := by
  change (Matrix.toLin' (cumulativeMatrix n)) x i = _
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, cumulativeMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma cumulativeLinearEquiv_map_volume (n : ℕ) :
    Measure.map (cumulativeLinearEquiv n) volume = volume := by
  change Measure.map (Matrix.toLin' (cumulativeMatrix n)) volume = volume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi]
  · rw [cumulativeMatrix_det]
    simp
  · rw [cumulativeMatrix_det]
    exact one_ne_zero

/-- The measurable equivalence underlying `cumulativeLinearEquiv`. -/
def cumulativeMeasurableEquiv (n : ℕ) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (cumulativeLinearEquiv n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- Finite cumulative sums preserve Lebesgue measure. -/
lemma measurePreserving_cumulativeLinearEquiv (n : ℕ) :
    MeasurePreserving (cumulativeLinearEquiv n) volume volume := by
  refine ⟨(cumulativeLinearEquiv n).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  exact cumulativeLinearEquiv_map_volume n

/-- Ordered arrival coordinates obtained from nonnegative gaps of total length at most `t`. -/
def orderedSimplex (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  cumulativeLinearEquiv n '' nonnegativeSimplex n t

lemma measurableSet_orderedSimplex (n : ℕ) (t : ℝ) :
    MeasurableSet (orderedSimplex n t) := by
  change MeasurableSet (cumulativeMeasurableEquiv n '' nonnegativeSimplex n t)
  exact (cumulativeMeasurableEquiv n).measurableSet_image.mpr
    (measurableSet_nonnegativeSimplex n t)

/-- An ordered `n`-arrival simplex has volume `t^n / n!`. -/
theorem volume_orderedSimplex (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume (orderedSimplex n t) = ENNReal.ofReal (t ^ n / (n.factorial : ℝ)) := by
  have hp := measurePreserving_cumulativeLinearEquiv n
  rw [← hp.measure_preimage (measurableSet_orderedSimplex n t).nullMeasurableSet]
  have hpre : cumulativeLinearEquiv n ⁻¹' orderedSimplex n t = nonnegativeSimplex n t := by
    exact Set.preimage_image_eq _ (cumulativeLinearEquiv n).injective
  rw [hpre, volume_nonnegativeSimplex n ht]

lemma orderedSimplex_nonneg {n : ℕ} {t : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ orderedSimplex n t) (i : Fin n) : 0 ≤ y i := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [cumulativeLinearEquiv_apply]
  exact Finset.sum_nonneg fun _ _ ↦ hx.1 _

lemma orderedSimplex_monotone {n : ℕ} {t : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ orderedSimplex n t) : Monotone y := by
  obtain ⟨x, hx, rfl⟩ := hy
  intro i j hij
  simp_rw [cumulativeLinearEquiv_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_Iic] at hq ⊢
    exact le_trans hq hij
  · intro q _ _
    exact hx.1 q

lemma orderedSimplex_le {n : ℕ} {t : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ orderedSimplex n t) (i : Fin n) : y i ≤ t := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [cumulativeLinearEquiv_apply]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun q _ _ ↦ hx.1 q).trans hx.2

/-- The inverse cumulative-sum coordinates are nonnegative for every nonnegative monotone
arrival vector. -/
lemma cumulativeLinearEquiv_symm_nonneg {n : ℕ} {y : Fin n → ℝ}
    (hmono : Monotone y) (hnonneg : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ (cumulativeLinearEquiv n).symm y i := by
  let x := (cumulativeLinearEquiv n).symm y
  have hxy : cumulativeLinearEquiv n x = y := (cumulativeLinearEquiv n).apply_symm_apply y
  intro i
  have htotal : ∑ q ∈ Finset.Iic i, x q = y i := by
    rw [← cumulativeLinearEquiv_apply, hxy]
  have hsplit : ∑ q ∈ Finset.Iic i, x q = x i + ∑ q ∈ Finset.Iio i, x q := by
    rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  have hle : ∑ q ∈ Finset.Iio i, x q ≤ y i := by
    by_cases hi : i.val = 0
    · have hset : Finset.Iio i = ∅ := by
        ext q
        simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
        change i.val ≤ q.val
        omega
      rw [hset, Finset.sum_empty]
      exact hnonneg i
    · let p : Fin n := ⟨i.val - 1, by omega⟩
      have hset : Finset.Iic p = Finset.Iio i := by
        ext q
        simp only [Finset.mem_Iic, Finset.mem_Iio]
        change (q.val ≤ i.val - 1 ↔ q.val < i.val)
        omega
      rw [← hset]
      rw [← cumulativeLinearEquiv_apply, hxy]
      exact hmono (by
        change i.val - 1 ≤ i.val
        omega)
  change 0 ≤ x i
  linarith

lemma sum_cumulativeLinearEquiv_symm {n : ℕ} (y : Fin (n + 1) → ℝ) :
    ∑ i, (cumulativeLinearEquiv (n + 1)).symm y i = y (Fin.last n) := by
  have h := cumulativeLinearEquiv_apply (n + 1)
    ((cumulativeLinearEquiv (n + 1)).symm y) (Fin.last n)
  rw [(cumulativeLinearEquiv (n + 1)).apply_symm_apply] at h
  have hset : Finset.Iic (Fin.last n) = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    exact Fin.le_last i
  rw [hset] at h
  exact h.symm

lemma mem_orderedSimplex_iff {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (y : Fin n → ℝ) :
    y ∈ orderedSimplex n t ↔
      (∀ i, 0 ≤ y i) ∧ Monotone y ∧ (∀ i, y i ≤ t) := by
  constructor
  · intro hy
    exact ⟨fun i ↦ orderedSimplex_nonneg hy i,
      orderedSimplex_monotone hy, fun i ↦ orderedSimplex_le hy i⟩
  · rintro ⟨hnonneg, hmono, hupper⟩
    let x := (cumulativeLinearEquiv n).symm y
    refine ⟨x, ⟨cumulativeLinearEquiv_symm_nonneg hmono hnonneg, ?_⟩,
      (cumulativeLinearEquiv n).apply_symm_apply y⟩
    cases n with
    | zero => simpa using ht
    | succ m =>
        rw [sum_cumulativeLinearEquiv_symm]
        exact hupper (Fin.last m)

/-- A finite product of ordered arrival simplices, one for every time block. -/
def orderedBlockChamber {n : ℕ} (k : Fin n → ℕ) (d : Fin n → ℝ) :
    Set (∀ j : Fin n, Fin (k j) → ℝ) :=
  Set.pi Set.univ fun j ↦ orderedSimplex (k j) (d j)

lemma measurableSet_orderedBlockChamber {n : ℕ} (k : Fin n → ℕ) (d : Fin n → ℝ) :
    MeasurableSet (orderedBlockChamber k d) := by
  exact MeasurableSet.univ_pi fun j ↦ measurableSet_orderedSimplex (k j) (d j)

/-- Arrival chambers factor into the product of their simplex volumes. -/
theorem volume_orderedBlockChamber {n : ℕ} (k : Fin n → ℕ) (d : Fin n → ℝ)
    (hd : ∀ j, 0 ≤ d j) :
    volume (orderedBlockChamber k d) =
      ∏ j, ENNReal.ofReal ((d j) ^ (k j) / ((k j).factorial : ℝ)) := by
  rw [orderedBlockChamber, volume_pi_pi]
  apply Finset.prod_congr rfl
  intro j _
  exact volume_orderedSimplex (k j) (hd j)

end

end MeasureTheory
