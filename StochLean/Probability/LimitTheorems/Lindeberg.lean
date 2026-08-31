/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.LimitTheorems.TriangularArray
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Lindeberg and Lyapunov conditions

The general definitions use a strictly positive real variance scale.  Their nonnegative
expectations are represented by `lintegral`, so neither definition depends on a totalized real
integral outside its natural domain.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The nonnegative Lindeberg tail numerator for row `n`. -/
noncomputable def lindebergNumerator {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (v : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j, ∫⁻ ω in {ω | ε ^ 2 * v n < (X n j ω) ^ 2},
    ENNReal.ofReal ((X n j ω) ^ 2) ∂P

/-- Lindeberg's condition at an explicit strictly positive scale. -/
def SatisfiesLindebergAtScale {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (v : ℕ → ℝ) : Prop :=
  (∀ n, 0 < v n) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n ↦ (ENNReal.ofReal (v n))⁻¹ * lindebergNumerator X P v ε n)
      atTop (𝓝 0)

/-- Lindeberg's condition at the row-sum variance scale.  Positivity of every row variance is a
genuine part of the predicate. -/
def SatisfiesLindeberg {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  SatisfiesLindebergAtScale X P fun n ↦ variance (triangularRowSum X n) P

/-- Unit-scale Lindeberg condition used by normalized arrays. -/
def SatisfiesUnitLindeberg {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  SatisfiesLindebergAtScale X P fun _ ↦ 1

/-- The Lyapunov numerator with real exponent `r`. -/
noncomputable def lyapunovNumerator {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (r : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j, ∫⁻ ω, ENNReal.ofReal (|X n j ω| ^ r) ∂P

/-- Lyapunov's condition at a strictly positive scale and exponent `r > 2`. -/
def SatisfiesLyapunovAtScale {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (v : ℕ → ℝ) (r : ℝ) : Prop :=
  2 < r ∧ (∀ n, 0 < v n) ∧
    Tendsto
      (fun n ↦ (ENNReal.ofReal ((v n) ^ (r / 2)))⁻¹ * lyapunovNumerator X P r n)
      atTop (𝓝 0)

/-- Klenke's `δ > 0` parametrization is the specialization `r = 2 + δ`. -/
def SatisfiesLyapunovDeltaAtScale {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (v : ℕ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ SatisfiesLyapunovAtScale X P v (2 + δ)

theorem SatisfiesLindebergAtScale.scale_pos {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} {v : ℕ → ℝ} (h : SatisfiesLindebergAtScale X P v) (n : ℕ) :
    0 < v n :=
  h.1 n

theorem SatisfiesLyapunovAtScale.exponent_gt_two {k : ℕ → ℕ}
    {X : TriangularArray k Ω} {P : Measure Ω} {v : ℕ → ℝ} {r : ℝ}
    (h : SatisfiesLyapunovAtScale X P v r) : 2 < r :=
  h.1

theorem satisfiesLindeberg_iff_unit {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hindep : IsRowIndependent X P) (hnorm : IsNormedArray X P) :
    SatisfiesLindeberg X P ↔ SatisfiesUnitLindeberg X P := by
  have hv : (fun n ↦ variance (triangularRowSum X n) P) = fun _ ↦ 1 := by
    funext n
    exact variance_triangularRowSum_eq_one hindep hnorm n
  simp only [SatisfiesLindeberg, SatisfiesUnitLindeberg, hv]

/-- The unit-scale Lindeberg condition forces every row maximum to vanish in probability. -/
theorem SatisfiesUnitLindeberg.isNullArray {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hL : SatisfiesUnitLindeberg X P) (hX : IsMeasurableArray X) :
    IsNullArray X P := by
  intro ε hε
  have hnum : Tendsto (fun n ↦ lindebergNumerator X P (fun _ ↦ 1) ε n) atTop (𝓝 0) := by
    simpa [SatisfiesUnitLindeberg, SatisfiesLindebergAtScale] using hL.2 ε hε
  have hε2_pos : 0 < ENNReal.ofReal (ε ^ 2) := ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)
  have hbound : ∀ n, triangularRowMaxTail X P ε n ≤
      (ENNReal.ofReal (ε ^ 2))⁻¹ * lindebergNumerator X P (fun _ ↦ 1) ε n := by
    intro n
    refine Finset.sup_le fun j _ ↦ ?_
    let s : Set Ω := {ω | ε < |X n j ω|}
    have habs : Measurable (fun ω ↦ |X n j ω|) := by
      simpa [Real.norm_eq_abs] using (hX n j).norm
    have hs : MeasurableSet s := measurableSet_lt measurable_const habs
    let f : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal ((X n j ω) ^ 2)
    have hf : Measurable f := ENNReal.measurable_ofReal.comp ((hX n j).pow_const 2)
    have hset : s ⊆ {ω | ENNReal.ofReal (ε ^ 2) ≤ f ω} := by
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      apply le_of_lt
      have hsqabs : ε ^ 2 < |X n j ω| ^ 2 :=
        (sq_lt_sq₀ hε.le (abs_nonneg _)).2 hω
      simpa only [sq_abs] using hsqabs
    have hmark := meas_ge_le_lintegral_div (μ := P.restrict s) hf.aemeasurable
      hε2_pos.ne' ENNReal.ofReal_ne_top
    have hleft : (P.restrict s) {ω | ENNReal.ofReal (ε ^ 2) ≤ f ω} = P s := by
      rw [Measure.restrict_apply (measurableSet_le measurable_const hf)]
      rw [Set.inter_eq_right.mpr hset]
    rw [hleft, ENNReal.div_eq_inv_mul] at hmark
    refine hmark.trans ?_
    gcongr
    unfold lindebergNumerator
    have hs_eq : s = {ω | ε ^ 2 * 1 < (X n j ω) ^ 2} := by
      ext ω
      simp only [s, Set.mem_ofPred_eq, mul_one]
      simpa only [sq_abs] using (sq_lt_sq₀ hε.le (abs_nonneg (X n j ω))).symm
    rw [hs_eq]
    change (∫⁻ ω in {ω | ε ^ 2 * 1 < (X n j ω) ^ 2},
        ENNReal.ofReal ((X n j ω) ^ 2) ∂P) ≤
      ∑ j, ∫⁻ ω in {ω | ε ^ 2 * 1 < (X n j ω) ^ 2},
        ENNReal.ofReal ((X n j ω) ^ 2) ∂P
    have hnonneg : ∀ i : Fin (k n),
        0 ≤ ∫⁻ ω in {ω | ε ^ 2 * 1 < (X n i ω) ^ 2},
          ENNReal.ofReal ((X n i ω) ^ 2) ∂P := fun _ ↦ bot_le
    exact Finset.single_le_sum (fun i _ ↦ hnonneg i) (Finset.mem_univ j)
  have hupper : Tendsto
      (fun n ↦ (ENNReal.ofReal (ε ^ 2))⁻¹ * lindebergNumerator X P (fun _ ↦ 1) ε n)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hnum
      (Or.inr (ENNReal.inv_ne_top.mpr hε2_pos.ne'))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ ↦ bot_le) hbound

/-- For an independent normalized triangular array, Lindeberg's condition implies nullity. -/
theorem SatisfiesLindeberg.isNullArray {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hL : SatisfiesLindeberg X P) (hX : IsMeasurableArray X)
    (hindep : IsRowIndependent X P) (hnorm : IsNormedArray X P) : IsNullArray X P :=
  ((satisfiesLindeberg_iff_unit hindep hnorm).mp hL).isNullArray hX

end ProbabilityTheory
