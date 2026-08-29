/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analyticity and uniqueness of probability generating functions

The real power series associated with a natural-number-valued law is analytic on `(-1, 1)`.
The identity principle then shows that the PGF on `[0, 1]` determines the law.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace PMF

noncomputable section

private def pgfSeries (p : PMF ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ p.massReal

private lemma pgfSeries_sum_eq (p : PMF ℕ) (z : ℝ) :
    (pgfSeries p).sum z = ∑' n, p.massReal n * z ^ n := by
  change FormalMultilinearSeries.ofScalarsSum p.massReal z = _
  simpa [smul_eq_mul] using FormalMultilinearSeries.ofScalars_sum_eq p.massReal z

private lemma one_le_pgfSeries_radius (p : PMF ℕ) :
    (1 : ENNReal) ≤ (pgfSeries p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h : Summable fun n => |p.massReal n| := by
    simpa only [abs_of_nonneg (p.massReal_nonneg _)] using p.summable_massReal
  simpa [pgfSeries, Real.norm_eq_abs] using h

private lemma pgfSeries_hasFPowerSeriesOnBall (p : PMF ℕ) :
    HasFPowerSeriesOnBall (pgfSeries p).sum (pgfSeries p) 0 (pgfSeries p).radius :=
  (pgfSeries p).hasFPowerSeriesOnBall <|
    lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) (one_le_pgfSeries_radius p)

private lemma analyticOnNhd_pgfSeries (p : PMF ℕ) :
    AnalyticOnNhd ℝ (pgfSeries p).sum (Ioo (-1 : ℝ) 1) := by
  apply (pgfSeries_hasFPowerSeriesOnBall p).analyticOnNhd.mono
  intro z hz
  rw [mem_eball_zero_iff]
  apply lt_of_lt_of_le (b := 1) _ (one_le_pgfSeries_radius p)
  rw [enorm_eq_nnnorm]
  exact_mod_cast (show ‖z‖ < (1 : ℝ) by simpa [Real.norm_eq_abs, abs_lt] using hz)

/-- The probability generating function is continuous on its closed domain `[0, 1]`. -/
lemma continuous_pgf (p : PMF ℕ) : Continuous p.pgf := by
  apply continuous_tsum
  · intro n
    fun_prop
  · exact p.summable_massReal
  · intro n z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.massReal_nonneg n),
      abs_of_nonneg (pow_nonneg z.property.1 n)]
    exact mul_le_of_le_one_right (p.massReal_nonneg n)
      (pow_le_one₀ z.property.1 z.property.2)

/-- The real power series underlying a PGF is infinitely differentiable on `(-1, 1)`. -/
lemma contDiffOn_pgf_series (p : PMF ℕ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ ↦ ∑' n, p.massReal n * z ^ n) (Ioo (-1) 1) := by
  rw [← funext (pgfSeries_sum_eq p)]
  exact (analyticOnNhd_pgfSeries p).contDiffOn (uniqueDiffOn_Ioo (-1) 1)

/-- A natural-number-valued probability law is determined by its probability generating
function on `[0, 1]`. -/
theorem ext_pgf {p q : PMF ℕ} (h : p.pgf = q.pgf) : p = q := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hlocal : (pgfSeries p).sum =ᶠ[𝓝 (1 / 2 : ℝ)] (pgfSeries q).sum := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)] with z hz
    rw [pgfSeries_sum_eq, pgfSeries_sum_eq]
    simpa only [pgf] using congrFun h ⟨z, hz.1.le, hz.2.le⟩
  have hsums : EqOn (pgfSeries p).sum (pgfSeries q).sum (Ioo (-1) 1) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_pgfSeries p) (analyticOnNhd_pgfSeries q)
      isPreconnected_Ioo hhalf hlocal
  have hzero : (pgfSeries p).sum =ᶠ[𝓝 (0 : ℝ)] (pgfSeries q).sum := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with z hz
    exact hsums hz
  have hseries : pgfSeries p = pgfSeries q :=
    (pgfSeries_hasFPowerSeriesOnBall p).hasFPowerSeriesAt
      |>.eq_formalMultilinearSeries_of_eventually
        (pgfSeries_hasFPowerSeriesOnBall q).hasFPowerSeriesAt hzero
  have hmass : p.massReal = q.massReal :=
    FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ (by
      simpa only [pgfSeries] using hseries)
  exact ext_massReal (congrFun hmass)

end

end PMF
