/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lévy measures on the real line

The primitive predicate contains exactly the zero-atom condition and finiteness of the truncated
second moment.  Sigma-finiteness is derived by a countable level-set exhaustion and is deliberately
not installed as a global instance.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- The canonical nonnegative Lévy integrand `min(1,x²)`. -/
noncomputable def levyIntegrand (x : ℝ) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (x ^ 2))

theorem measurable_levyIntegrand : Measurable levyIntegrand := by
  exact measurable_const.min
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2))

@[simp]
theorem levyIntegrand_zero : levyIntegrand 0 = 0 := by
  simp [levyIntegrand]

theorem levyIntegrand_pos {x : ℝ} (hx : x ≠ 0) : 0 < levyIntegrand x := by
  simp only [levyIntegrand, lt_min_iff, zero_lt_one, true_and]
  exact ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hx)

theorem levyIntegrand_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    levyIntegrand x = ENNReal.ofReal (x ^ 2) := by
  rw [levyIntegrand, min_eq_right]
  apply ENNReal.ofReal_le_one.mpr
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx.le
    _ = 1 := by norm_num

theorem levyIntegrand_toReal_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    (levyIntegrand x).toReal = x ^ 2 := by
  rw [levyIntegrand_of_abs_lt_one hx, ENNReal.toReal_ofReal (sq_nonneg x)]

theorem levyIntegrand_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : levyIntegrand x = 1 := by
  rw [levyIntegrand, min_eq_left]
  apply ENNReal.one_le_ofReal.mpr
  calc
    (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
    _ ≤ |x| ^ 2 := (sq_le_sq₀ zero_le_one (abs_nonneg x)).mpr hx
    _ = x ^ 2 := sq_abs x

theorem levyIntegrand_toReal_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    (levyIntegrand x).toReal = 1 := by
  rw [levyIntegrand_of_one_le_abs hx]
  simp

/-- Scaling the argument of the Lévy integrand costs only the finite factor
`max 1 a²`.  This is the measure-theoretic estimate behind affine triplet maps. -/
theorem levyIntegrand_mul_le (a x : ℝ) :
    levyIntegrand (a * x) ≤ ENNReal.ofReal (max 1 (a ^ 2)) * levyIntegrand x := by
  unfold levyIntegrand
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg a)]
  have ha : (0 : ℝ) ≤ max 1 (a ^ 2) := le_trans zero_le_one (le_max_left _ _)
  by_cases hx : ENNReal.ofReal (x ^ 2) ≤ 1
  · rw [min_eq_right hx]
    apply min_le_iff.mpr
    right
    gcongr
    exact le_max_right _ _
  · rw [min_eq_left (le_of_not_ge hx)]
    apply min_le_iff.mpr
    left
    simp

/-- Minimal real Lévy-measure semantics. -/
def IsLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ (∫⁻ x, levyIntegrand x ∂ν) < ∞

/-- A discrete infinite-activity Lévy measure with atoms geometrically approaching zero. -/
noncomputable def geometricLevyMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ ↦ Measure.dirac (((2 : ℝ)⁻¹) ^ n)

@[simp]
theorem geometricLevyMeasure_atom_zero : geometricLevyMeasure {0} = 0 := by
  rw [geometricLevyMeasure, Measure.sum_apply _ (MeasurableSet.singleton 0)]
  simp

private theorem levyIntegrand_geometricLevyMeasure_atom_le (n : ℕ) :
    levyIntegrand (((2 : ℝ)⁻¹) ^ n) ≤ ((4 : ℝ≥0∞)⁻¹) ^ n := by
  unfold levyIntegrand
  refine (min_le_right _ _).trans_eq ?_
  have hx : (((2 : ℝ)⁻¹) ^ n) ^ 2 = ((4 : ℝ)⁻¹) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hx, ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  norm_num

/-- The geometric atomic example satisfies the minimal Lévy-measure predicate. -/
theorem isLevyMeasure_geometricLevyMeasure : IsLevyMeasure geometricLevyMeasure := by
  refine ⟨geometricLevyMeasure_atom_zero, ?_⟩
  rw [geometricLevyMeasure, lintegral_sum_measure]
  simp_rw [lintegral_dirac' _ measurable_levyIntegrand]
  exact lt_of_le_of_lt
    (ENNReal.summable.tsum_le_tsum levyIntegrand_geometricLevyMeasure_atom_le ENNReal.summable)
    (tsum_geometric_lt_top.mpr (by norm_num))

/-- The geometric atomic Lévy measure has genuinely infinite total mass. -/
theorem geometricLevyMeasure_univ : geometricLevyMeasure Set.univ = ∞ := by
  rw [geometricLevyMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp

namespace IsLevyMeasure

variable {ν : Measure ℝ}

theorem atom_zero (hν : IsLevyMeasure ν) : ν {0} = 0 := hν.1

theorem lintegral_lt_top (hν : IsLevyMeasure ν) :
    (∫⁻ x, levyIntegrand x ∂ν) < ∞ := hν.2

/-- Scaling a Lévy measure by a finite nonnegative constant preserves the minimal predicate. -/
theorem smul (hν : IsLevyMeasure ν) (c : ℝ≥0) : IsLevyMeasure (c • ν) := by
  constructor
  · simp [Measure.smul_apply, hν.atom_zero]
  · rw [MeasureTheory.lintegral_smul_measure]
    exact ENNReal.mul_lt_top (by simp) hν.lintegral_lt_top

theorem add {κ : Measure ℝ} (hν : IsLevyMeasure ν) (hκ : IsLevyMeasure κ) :
    IsLevyMeasure (ν + κ) := by
  constructor
  · simp [Measure.add_apply, hν.atom_zero, hκ.atom_zero]
  · rw [lintegral_add_measure]
    exact ENNReal.add_lt_top.mpr ⟨hν.lintegral_lt_top, hκ.lintegral_lt_top⟩

/-- A finite measure with no atom at zero is a Lévy measure. -/
theorem of_isFiniteMeasure [IsFiniteMeasure ν] (hzero : ν {0} = 0) : IsLevyMeasure ν := by
  refine ⟨hzero, lt_of_le_of_lt ?_ (measure_lt_top ν Set.univ)⟩
  calc
    (∫⁻ x, levyIntegrand x ∂ν) ≤ ∫⁻ _x, 1 ∂ν :=
      lintegral_mono fun x => min_le_left _ _
    _ = ν Set.univ := by simp

/-- Pushforward under a nonzero real scaling preserves the minimal Lévy-measure predicate. -/
theorem map_mul (hν : IsLevyMeasure ν) {a : ℝ} (ha : a ≠ 0) :
    IsLevyMeasure (ν.map (fun x => a * x)) := by
  constructor
  · rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0)]
    have hpre : (fun x : ℝ => a * x) ⁻¹' ({0} : Set ℝ) = {0} := by
      ext x
      simp [ha]
    rw [hpre, hν.atom_zero]
  · rw [lintegral_map measurable_levyIntegrand (by fun_prop)]
    refine lt_of_le_of_lt (lintegral_mono (fun x => levyIntegrand_mul_le a x)) ?_
    rw [lintegral_const_mul _ measurable_levyIntegrand]
    exact ENNReal.mul_lt_top (by simp) hν.lintegral_lt_top

/-- Positive level sets of the Lévy integrand.
Their thresholds are strictly positive and finite. -/
def spanningLevel (n : ℕ) : Set ℝ :=
  {x | ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ levyIntegrand x}

theorem measure_spanningLevel_lt_top (hν : IsLevyMeasure ν) (n : ℕ) :
    ν (spanningLevel n) < ∞ := by
  let c : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hc0 : c ≠ 0 := by
    simp [c]
  have hmul : c * ν (spanningLevel n) < ∞ :=
    lt_of_le_of_lt (mul_meas_ge_le_lintegral measurable_levyIntegrand c) hν.2
  rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
  · exact h.2
  · exact (hc0 h).elim
  · simp [h]

/-- Sigma-finiteness follows from the two primitive Lévy-measure conditions.  This theorem returns
the typeclass value explicitly and does not add an instance. -/
theorem sigmaFinite (hν : IsLevyMeasure ν) : SigmaFinite ν := by
  let S : Set (Set ℝ) := Set.range spanningLevel ∪ {{0}}
  apply Measure.sigmaFinite_of_countable
    ((Set.countable_range (spanningLevel : ℕ → Set ℝ)).union
      (Set.countable_singleton ({0} : Set ℝ)))
  · intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨n, rfl⟩
      exact hν.measure_spanningLevel_lt_top n
    · simp only [Set.mem_singleton_iff] at hs
      subst s
      simp [hν.atom_zero]
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x = 0
    · subst x
      refine Set.mem_sUnion.mpr ⟨{0}, ?_, ?_⟩
      · exact Or.inr (Set.mem_singleton {0})
      · exact Set.mem_singleton 0
    · have hpos : 0 < levyIntegrand x := levyIntegrand_pos hx
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp at hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine Set.mem_sUnion.mpr ⟨spanningLevel m, ?_, ?_⟩
      · exact Or.inl ⟨m, rfl⟩
      · exact hn.le

end IsLevyMeasure

end ProbabilityTheory
