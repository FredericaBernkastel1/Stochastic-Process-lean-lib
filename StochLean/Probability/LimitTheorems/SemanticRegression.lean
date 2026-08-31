/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.LimitTheorems.Lindeberg
public import StochLean.Probability.Series.ThreeSeries
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Semantic regressions for classical limit-theorem foundations
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem isRowIndependent_iff {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω) :
    IsRowIndependent X P ↔ ∀ n, iIndepFun (X n) P :=
  Iff.rfl

theorem isNormedArray_iff {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω) :
    IsNormedArray X P ↔
      (∀ n j, MemLp (X n j) 2 P) ∧ ∀ n, ∑ j, variance (X n j) P = 1 :=
  Iff.rfl

theorem isNullArray_uses_row_max {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω) :
    IsNullArray X P ↔ ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ Finset.univ.sup fun j : Fin (k n) ↦ P {ω | ε < |X n j ω|})
        atTop (𝓝 0) :=
  Iff.rfl

theorem isNullArray_eventual_uniform_iff {k : ℕ → ℕ} (X : TriangularArray k Ω)
    (P : Measure Ω) :
    IsNullArray X P ↔ IsNullArrayEventual X P :=
  isNullArray_iff_eventual

/-- Row nonemptiness is a genuine independent input, not hidden in the array representation. -/
example : HasNonemptyRows (fun _ : ℕ ↦ 1) := by
  intro n
  simp

/-- Finite-row maximum and sum are observably different operations. -/
theorem two_tail_max_ne_sum :
    (Finset.univ.sup (fun _ : Fin 2 ↦ (1 : ℕ))) ≠ ∑ _ : Fin 2, (1 : ℕ) := by
  decide

omit [MeasurableSpace Ω] in
/-- The truncation boundary is included exactly as in Klenke. -/
theorem threeSeries_boundary_included (K : ℝ) (n : ℕ) (ω : Ω) (hK : 0 ≤ K) :
    threeSeriesTruncation (fun _ _ ↦ K) K n ω = K := by
  apply threeSeriesTruncation_of_le
  simp [abs_of_nonneg hK]

theorem lindeberg_scale_is_ne_zero {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} {v : ℕ → ℝ} (h : SatisfiesLindebergAtScale X P v) (n : ℕ) :
    v n ≠ 0 :=
  (h.scale_pos n).ne'

/-- The normalized-array bridge exposes the intended Lindeberg-to-nullity conclusion. -/
example {k : ℕ → ℕ} {X : TriangularArray k Ω} {P : Measure Ω}
    (hL : SatisfiesLindeberg X P) (hX : IsMeasurableArray X)
    (hindep : IsRowIndependent X P) (hnorm : IsNormedArray X P) : IsNullArray X P :=
  hL.isNullArray hX hindep hnorm

end ProbabilityTheory
