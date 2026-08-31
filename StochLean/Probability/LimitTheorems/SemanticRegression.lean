/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.LimitTheorems.Lindeberg
public import StochLean.Probability.LimitTheorems.MultivariateCLT
public import StochLean.Probability.Series.ThreeSeries
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Semantic regressions for classical limit-theorem foundations
-/

@[expose] public section

open Filter MeasureTheory Matrix WithLp
open scoped ENNReal MeasureTheory ProbabilityTheory RealInnerProductSpace Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem isRowIndependent_iff {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω) :
    IsRowIndependent X P ↔ ∀ n, iIndepFun (X n) P :=
  Iff.rfl

theorem isMeasurableArray_iff {k : ℕ → ℕ} (X : TriangularArray k Ω) :
    IsMeasurableArray X ↔ ∀ n j, Measurable (X n j) :=
  Iff.rfl

theorem isCenteredArray_iff {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω) :
    IsCenteredArray X P ↔
      ∀ n j, Integrable (X n j) P ∧ ∫ ω, X n j ω ∂P = 0 :=
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

/-- Klenke's `δ > 0` parametrization keeps the exact scale and implies Lindeberg. -/
example {k : ℕ → ℕ} {X : TriangularArray k Ω} {P : Measure Ω}
    {v : ℕ → ℝ} {δ : ℝ} (hL : SatisfiesLyapunovDeltaAtScale X P v δ)
    (hX : IsMeasurableArray X) : SatisfiesLindebergAtScale X P v :=
  hL.satisfiesLindebergAtScale hX

/-- Independent normalized rows have row-sum variance exactly one. -/
example {k : ℕ → ℕ} {X : TriangularArray k Ω} {P : Measure Ω}
    (hindep : IsRowIndependent X P) (hnorm : IsNormedArray X P) (n : ℕ) :
    variance (triangularRowSum X n) P = 1 :=
  variance_triangularRowSum_eq_one hindep hnorm n

/-- The public Lindeberg--Feller result is the forward implication, not an unaudited `iff`. -/
example {k : ℕ → ℕ} {X : TriangularArray k Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (hL : SatisfiesLindeberg X P) (hk : HasNonemptyRows k)
    (hX : IsMeasurableArray X) (hc : IsCenteredArray X P)
    (hi : IsRowIndependent X P) (hn : IsNormedArray X P) :
    Tendsto (triangularRowSumLaw X P hX) atTop (𝓝 standardGaussianProbabilityMeasure) :=
  hL.tendsto_map_triangularRowSum_standardGaussian hk hX hi hc hn

/-- The complete three-series API preserves both ordered-series occurrences and the inclusive
truncation boundary. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 < K) (hX : ∀ n, StronglyMeasurable (X n)) (hi : iIndepFun X P) :
    OrderedRandomSeriesConvergesAE X P ↔ KolmogorovThreeSeriesConditions X P K :=
  kolmogorovThreeSeries_iff hK hX hi

theorem orderedRandomSeriesConvergesAE_iff (X : ℕ → Ω → ℝ) (P : Measure Ω) :
    OrderedRandomSeriesConvergesAE X P ↔
      ∀ᵐ ω ∂P, ∃ s : ℝ,
        Tendsto (fun n ↦ orderedPartialSum (fun k ↦ X k ω) n) atTop (𝓝 s) :=
  Iff.rfl

theorem threeSeries_expectation_condition_is_ordered
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (K : ℝ)
    (h : KolmogorovThreeSeriesConditions X P K) :
    OrderedSeriesConverges (fun n ↦ ∫ ω, threeSeriesTruncation X K n ω ∂P) :=
  h.2.1

/-- The load-bearing finite-variance martingale result is exposed as a proved helper rather than a
ledger assumption. -/
example {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hX2 : ∀ n, MemLp (X n) 2 P)
    (hcenter : ∀ n, ∫ ω, X n ω ∂P = 0) (hindep : iIndepFun X P)
    (hvar : (∑' n, ENNReal.ofReal (variance (X n) P)) < ∞) :
    OrderedRandomSeriesConvergesAE X P :=
  orderedRandomSeriesConvergesAE_of_variance_tsum_lt_top
    hXstrong hX2 hcenter hindep hvar

/-- The multivariate CLT accepts a merely positive-semidefinite covariance matrix; no
invertibility or positive-definiteness premise is present. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (hX2 : MemLp (X 0) 2 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : ∀ t : EuclideanSpace ℝ ι,
      Var[fun ω ↦ ⟪t, X 0 ω⟫; P] = t ⬝ᵥ S *ᵥ t)
    (hindep : iIndepFun X P) (hident : ∀ n, IdentDistrib (X n) (X 0) P P) :
    TendstoInDistribution (normalizedVectorPartialSum X) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 S) :=
  tendstoInDistribution_normalizedVectorPartialSum hS hX2 hmean hvar hindep hident

/-- Ordered convergence is deliberately weaker than absolute summability: the alternating
harmonic series is accepted by the public ordered-series predicate. -/
theorem alternatingHarmonic_orderedSeriesConverges :
    OrderedSeriesConverges (fun n : ℕ ↦ (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) := by
  have hanti : Antitone (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1)
  exact hanti.tendsto_alternating_series_of_tendsto_zero
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The preceding ordered-convergent series is not absolutely summable. -/
theorem alternatingHarmonic_not_summable_abs :
    ¬ Summable (fun n : ℕ ↦ |(-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))|) := by
  have hshift : ¬ Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ))) := by
    exact_mod_cast mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast
  have habs : (fun n : ℕ ↦ |(-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))|) =
      fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ)) := by
    funext n
    simp [abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  rw [habs]
  exact hshift

end ProbabilityTheory
