/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Triangular arrays

The rows are ordinary dependent functions.  Nonemptiness, measurability, rowwise independence,
centering, and variance normalization are deliberately separate predicates.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real triangular array with row `n` indexed by `Fin (k n)`. -/
abbrev TriangularArray (k : ℕ → ℕ) (Ω : Type*) :=
  (n : ℕ) → Fin (k n) → Ω → ℝ

/-- Every row of the triangular array is nonempty. -/
def HasNonemptyRows (k : ℕ → ℕ) : Prop :=
  ∀ n, 0 < k n

/-- Sum of row `n`. -/
def triangularRowSum {k : ℕ → ℕ} (X : TriangularArray k Ω) (n : ℕ) : Ω → ℝ :=
  ∑ j, X n j

/-- Entry measurability is explicit and is not inferred from independence. -/
def IsMeasurableArray {k : ℕ → ℕ} (X : TriangularArray k Ω) : Prop :=
  ∀ n j, Measurable (X n j)

/-- Independence is required within each row only.  No relation between distinct rows is imposed. -/
def IsRowIndependent {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n, iIndepFun (X n) P

/-- Every entry is integrable and centered.  This predicate contains no independence or variance
normalization hypothesis. -/
def IsCenteredArray {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ n j, Integrable (X n j) P ∧ ∫ ω, X n j ω ∂P = 0

/-- Every entry is square-integrable and the entry variances in each row sum to one.  Centering and
independence remain separate predicates. -/
def IsNormedArray {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  (∀ n j, MemLp (X n j) 2 P) ∧
    ∀ n, ∑ j, variance (X n j) P = 1

/-- Largest tail probability in row `n`.  This is a maximum, never a sum of tail probabilities. -/
def triangularRowMaxTail {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (ε : ℝ) (n : ℕ) : ℝ≥0∞ :=
  Finset.univ.sup fun j : Fin (k n) ↦ P {ω | ε < |X n j ω|}

/-- Klenke's null-array condition, in its equivalent finite-row maximum form. -/
def IsNullArray {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (triangularRowMaxTail X P ε) atTop (𝓝 0)

/-- Source-facing eventual-uniform formulation of the null-array condition. -/
def IsNullArrayEventual {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ →
    ∀ᶠ n in atTop, ∀ j : Fin (k n),
      P {ω | ε < |X n j ω|} < ENNReal.ofReal δ

theorem measurable_triangularRowSum {k : ℕ → ℕ} {X : TriangularArray k Ω}
    (hX : IsMeasurableArray X) (n : ℕ) : Measurable (triangularRowSum X n) := by
  unfold triangularRowSum
  have hfun : (∑ j, X n j) = fun ω ↦ ∑ j, X n j ω := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun]
  exact Finset.measurable_fun_sum Finset.univ fun i _hi ↦ hX n i

/-- Rowwise independence and square integrability give the expected finite variance identity. -/
theorem variance_triangularRowSum_eq_sum {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hindep : IsRowIndependent X P)
    (hL2 : ∀ n j, MemLp (X n j) 2 P) (n : ℕ) :
    variance (triangularRowSum X n) P = ∑ j, variance (X n j) P := by
  unfold triangularRowSum
  exact IndepFun.variance_sum
    (s := Finset.univ) (X := X n)
    (fun i _hi ↦ hL2 n i)
    (fun _i _hi _j _hj hij ↦ (hindep n).indepFun hij)

/-- A normed independent row has row-sum variance exactly one. -/
theorem variance_triangularRowSum_eq_one {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hindep : IsRowIndependent X P) (hnorm : IsNormedArray X P) (n : ℕ) :
    variance (triangularRowSum X n) P = 1 := by
  rw [variance_triangularRowSum_eq_sum hindep hnorm.1 n, hnorm.2 n]

/-- Each entry tail is bounded by the finite-row maximum. -/
theorem tail_le_triangularRowMaxTail {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) (ε : ℝ) (n : ℕ) (j : Fin (k n)) :
    P {ω | ε < |X n j ω|} ≤ triangularRowMaxTail X P ε n := by
  exact Finset.le_sup (s := Finset.univ) (f := fun i : Fin (k n) ↦ P {ω | ε < |X n i ω|})
    (Finset.mem_univ j)

/-- The maximum-tail formulation gives the source-facing eventual uniform bound over every entry
in a row. -/
theorem IsNullArray.eventually_forall_tail_lt {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hX : IsNullArray X P) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ j : Fin (k n), P {ω | ε < |X n j ω|} < ENNReal.ofReal δ := by
  have hnhds : Set.Iio (ENNReal.ofReal δ) ∈ 𝓝 (0 : ℝ≥0∞) :=
    Iio_mem_nhds (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [(hX ε hε).eventually hnhds] with n hn j
  exact (tail_le_triangularRowMaxTail X P ε n j).trans_lt hn

/-- The finite-row maximum definition is equivalent to Klenke's eventual uniform tail bound. -/
theorem isNullArray_iff_eventual {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} : IsNullArray X P ↔ IsNullArrayEventual X P := by
  constructor
  · intro h ε δ hε hδ
    exact h.eventually_forall_tail_lt hε hδ
  · intro h ε hε
    rw [tendsto_order]
    refine ⟨?_, ?_⟩
    · intro a ha
      simp at ha
    · intro a ha
      by_cases ha_top : a = ∞
      · subst a
        filter_upwards [h ε 1 hε zero_lt_one] with n hn
        exact (Finset.sup_lt_iff (by simp)).2 fun j _ ↦ (hn j).trans_le (by simp)
      · have ha_real : 0 < a.toReal := ENNReal.toReal_pos ha.ne' ha_top
        filter_upwards [h ε (a.toReal / 2) hε (half_pos ha_real)] with n hn
        refine (Finset.sup_lt_iff ha).2 fun j _ ↦ (hn j).trans ?_
        have heq : ENNReal.ofReal (a.toReal / 2) = a / 2 := by
          simp [div_eq_mul_inv, ENNReal.ofReal_toReal ha_top, ha_real.le]
        rw [heq, ENNReal.div_lt_iff]
        · calc
            a = a * 1 := by simp
            _ < a * 2 := by
              gcongr
              norm_num
        · norm_num
        · norm_num

end ProbabilityTheory
