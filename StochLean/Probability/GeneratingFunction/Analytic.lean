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
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Analyticity and uniqueness of probability generating functions

The real power series associated with a natural-number-valued law is analytic on `(-1, 1)`.
The identity principle then shows that the PGF on `[0, 1]` determines the law.
-/

@[expose] public section

open Filter MeasureTheory Set
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

/-- The `k`th descending-factorial moment, with `∞` retained when the moment diverges. -/
def factorialMoment (p : PMF ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∑' n, p n * (n.descFactorial k : ℝ≥0∞)

/-- The nonnegative extended-value coefficient series for the `k`th PGF derivative.  The public
domain remains `[0, 1]`; divergence at the boundary is represented by `∞`. -/
def factorialDerivativeSeries (p : PMF ℕ) (k : ℕ) (z : unitInterval) : ℝ≥0∞ :=
  ∑' n, p n * (n.descFactorial k : ℝ≥0∞) * ENNReal.ofReal (z : ℝ) ^ (n - k)

private lemma summable_descFactorial_mul_pow (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ ↦ (n.descFactorial k : ℝ) * r ^ (n - k) := by
  rw [← summable_nat_add_iff k]
  simpa [abs_of_nonneg hr0] using
    (summable_descFactorial_mul_geometric_of_norm_lt_one (R := ℝ) k
      (show ‖r‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hr0]))

/-- On the open unit interval of convergence, termwise differentiation gives the usual
descending-factorial coefficient series for every derivative order. -/
theorem iteratedDeriv_pgf_series (p : PMF ℕ) (k : ℕ) {z : ℝ} (hz : z ∈ Ioo (-1) 1) :
    iteratedDeriv k (fun x : ℝ ↦ ∑' n, p.massReal n * x ^ n) z =
      ∑' n, p.massReal n * (n.descFactorial k : ℝ) * z ^ (n - k) := by
  let s : Set ℝ := Ioo (-1) 1
  have hsum : ∀ t ∈ s, Summable fun n ↦ p.massReal n * t ^ n := by
    intro t ht
    apply Summable.of_norm_bounded p.summable_massReal
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.massReal_nonneg n), abs_pow]
    exact mul_le_of_le_one_right (p.massReal_nonneg n)
      (pow_le_one₀ (abs_nonneg t) (le_of_lt (abs_lt.mpr ht)))
  have hloc : ∀ q : ℕ, SummableLocallyUniformlyOn
      (fun n ↦ iteratedDerivWithin q (fun x : ℝ ↦ p.massReal n * x ^ n) s) s := by
    intro q
    apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_Ioo
    intro K hKs hKc
    by_cases hK : K.Nonempty
    · obtain ⟨z0, hz0, hmax⟩ := hKc.exists_isMaxOn hK continuous_abs.continuousOn
      let r : ℝ := |z0|
      have hr0 : 0 ≤ r := abs_nonneg _
      have hr1 : r < 1 := abs_lt.mpr (hKs hz0)
      let u : ℕ → ℝ := fun n ↦ p.massReal n * (n.descFactorial q : ℝ) * r ^ (n - q)
      have hu0 : ∀ n, 0 ≤ u n := fun n ↦
        mul_nonneg (mul_nonneg (p.massReal_nonneg n) (Nat.cast_nonneg _)) (pow_nonneg hr0 _)
      have hubase := summable_descFactorial_mul_pow q hr0 hr1
      have hu : Summable u := by
        apply hubase.of_nonneg_of_le hu0
        intro n
        dsimp [u]
        calc
          p.massReal n * (n.descFactorial q : ℝ) * r ^ (n - q) ≤
              1 * (n.descFactorial q : ℝ) * r ^ (n - q) := by
            gcongr
            exact p.massReal_le_one n
          _ = (n.descFactorial q : ℝ) * r ^ (n - q) := by ring
      refine ⟨u, hu, ?_⟩
      intro n x hx
      rw [iteratedDerivWithin_const_mul_field,
        iteratedDerivWithin_pow (hKs hx) isOpen_Ioo.uniqueDiffOn n q]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (p.massReal_nonneg n), abs_of_nonneg (Nat.cast_nonneg _)]
      dsimp [u, r]
      calc
        p.massReal n * ((n.descFactorial q : ℝ) * |x| ^ (n - q)) ≤
            p.massReal n * ((n.descFactorial q : ℝ) * |z0| ^ (n - q)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (abs_nonneg x) (hmax hx) _) (Nat.cast_nonneg _))
            (p.massReal_nonneg n)
        _ = p.massReal n * (n.descFactorial q : ℝ) * |z0| ^ (n - q) := by ring
    · refine ⟨0, summable_zero, ?_⟩
      intro n x hx
      exact (hK ⟨x, hx⟩).elim
  have hdiff : ∀ n q x, q ≤ k → x ∈ s →
      DifferentiableAt ℝ (iteratedDerivWithin q (fun z ↦ p.massReal n * z ^ n) s) x := by
    intro n q x _hq hx
    have hc : ContDiff ℝ ⊤ (fun z : ℝ ↦ p.massReal n * z ^ n) := by fun_prop
    have hu : UniqueDiffOn ℝ (insert x s) := by
      simpa [s, insert_eq_of_mem hx] using isOpen_Ioo.uniqueDiffOn
    exact (hc.contDiffWithinAt.differentiableWithinAt_iteratedDerivWithin (by simp) hu)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hwithin := iteratedDerivWithin_tsum k isOpen_Ioo hz hsum
    (fun q _hq1 _hqk ↦ hloc q) hdiff
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioo hz] at hwithin
  simpa only [iteratedDerivWithin_const_mul_field,
    iteratedDerivWithin_pow hz isOpen_Ioo.uniqueDiffOn, mul_assoc] using hwithin

/-- The extended derivative series is exactly the real iterated derivative at every `z < 1`. -/
theorem factorialDerivativeSeries_eq_ofReal_iteratedDeriv (p : PMF ℕ) (k : ℕ)
    (z : unitInterval) (hz : z < 1) :
    factorialDerivativeSeries p k z =
      ENNReal.ofReal (iteratedDeriv k (fun x : ℝ ↦ ∑' n, p.massReal n * x ^ n) z) := by
  have hzIoo : (z : ℝ) ∈ Ioo (-1) 1 := ⟨lt_of_lt_of_le (by norm_num) z.property.1,
    show (z : ℝ) < 1 from hz⟩
  rw [iteratedDeriv_pgf_series p k hzIoo]
  have hbase := summable_descFactorial_mul_pow k z.property.1 hz
  have hnonneg : ∀ n : ℕ,
      0 ≤ p.massReal n * (n.descFactorial k : ℝ) * (z : ℝ) ^ (n - k) := fun n ↦ by
    exact mul_nonneg (mul_nonneg (p.massReal_nonneg n) (Nat.cast_nonneg _))
      (pow_nonneg z.property.1 _)
  have hsum : Summable fun n : ℕ ↦
      p.massReal n * (n.descFactorial k : ℝ) * (z : ℝ) ^ (n - k) := by
    apply hbase.of_nonneg_of_le hnonneg
    intro n
    calc
      p.massReal n * (n.descFactorial k : ℝ) * (z : ℝ) ^ (n - k) ≤
          1 * (n.descFactorial k : ℝ) * (z : ℝ) ^ (n - k) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (p.massReal_le_one n) (Nat.cast_nonneg _))
          (pow_nonneg z.property.1 _)
      _ = (n.descFactorial k : ℝ) * (z : ℝ) ^ (n - k) := by ring
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul (mul_nonneg (p.massReal_nonneg n) (Nat.cast_nonneg _)),
    ENNReal.ofReal_mul (p.massReal_nonneg n), ENNReal.ofReal_pow z.property.1]
  simp only [massReal, ENNReal.ofReal_toReal (p.apply_ne_top n), ENNReal.ofReal_natCast]

private def pgfBoundaryPoint (j : ℕ) : unitInterval :=
  ⟨1 - (1 / 2 : ℝ) ^ j,
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)),
    by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j]⟩

private lemma monotone_pgfBoundaryPoint : Monotone pgfBoundaryPoint := by
  intro i j hij
  change 1 - (1 / 2 : ℝ) ^ i ≤ 1 - (1 / 2 : ℝ) ^ j
  exact sub_le_sub_left
    (pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hij) 1

private lemma tendsto_pgfBoundaryPoint : Tendsto pgfBoundaryPoint atTop (𝓝 1) := by
  apply tendsto_subtype_rng.2
  change Tendsto (fun j : ℕ ↦ 1 - (1 / 2 : ℝ) ^ j) atTop (𝓝 (1 : ℝ))
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_sub 1

private lemma tendsto_factorialDerivativeSeries_boundary_seq (p : PMF ℕ) (k : ℕ) :
    Tendsto (fun j ↦ factorialDerivativeSeries p k (pgfBoundaryPoint j)) atTop
      (𝓝 (factorialMoment p k)) := by
  let f : ℕ → ℕ → ℝ≥0∞ := fun j n ↦
    p n * (n.descFactorial k : ℝ≥0∞) *
      ENNReal.ofReal (pgfBoundaryPoint j : ℝ) ^ (n - k)
  let F : ℕ → ℝ≥0∞ := fun n ↦ p n * (n.descFactorial k : ℝ≥0∞)
  have hf : ∀ j, AEMeasurable (f j) (Measure.count : Measure ℕ) := fun _ ↦
    (measurable_of_countable _).aemeasurable
  have hmono : ∀ᵐ n ∂(Measure.count : Measure ℕ), Monotone fun j ↦ f j n := by
    filter_upwards with n
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ bot_le
    exact pow_le_pow_left'
      (ENNReal.ofReal_le_ofReal
        (show (pgfBoundaryPoint i : ℝ) ≤ pgfBoundaryPoint j from monotone_pgfBoundaryPoint hij)) _
  have htend : ∀ᵐ n ∂(Measure.count : Measure ℕ),
      Tendsto (fun j ↦ f j n) atTop (𝓝 (F n)) := by
    filter_upwards with n
    have hz : Tendsto (fun j ↦ ENNReal.ofReal (pgfBoundaryPoint j : ℝ)) atTop (𝓝 1) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_subtype_rng.mp tendsto_pgfBoundaryPoint)
    have hc : p n * (n.descFactorial k : ℝ≥0∞) ≠ ∞ :=
      ENNReal.mul_ne_top (p.apply_ne_top n) ENNReal.coe_ne_top
    have hzpow : Tendsto
        (fun j ↦ ENNReal.ofReal (pgfBoundaryPoint j : ℝ) ^ (n - k)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, one_pow] using
        ((ENNReal.continuous_pow (n - k)).tendsto 1 |>.comp hz)
    simpa [f, F] using ENNReal.Tendsto.const_mul hzpow (Or.inr hc)
  have h := lintegral_tendsto_of_tendsto_of_monotone hf hmono htend
  simpa [factorialDerivativeSeries, factorialMoment, f, F, lintegral_count] using h

lemma monotone_factorialDerivativeSeries (p : PMF ℕ) (k : ℕ) :
    Monotone (factorialDerivativeSeries p k) := by
  intro z w hzw
  apply ENNReal.tsum_le_tsum
  intro n
  apply mul_le_mul_of_nonneg_left _ bot_le
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (show (z : ℝ) ≤ w from hzw)) _

lemma factorialDerivativeSeries_le_factorialMoment (p : PMF ℕ) (k : ℕ)
    (z : unitInterval) : factorialDerivativeSeries p k z ≤ factorialMoment p k := by
  simp only [factorialDerivativeSeries, factorialMoment]
  apply ENNReal.tsum_le_tsum
  intro n
  exact mul_le_of_le_one_right bot_le
    (pow_le_one₀ bot_le (by simpa using ENNReal.ofReal_le_one.mpr z.property.2))

/-- Klenke 3.2: the `k`th PGF derivative tends from the left to the `k`th descending-factorial
moment.  Both sides use `ℝ≥0∞`, so the theorem also records divergence to `∞`. -/
theorem tendsto_factorialDerivativeSeries (p : PMF ℕ) (k : ℕ) :
    Tendsto (factorialDerivativeSeries p k) (𝓝[<] 1) (𝓝 (factorialMoment p k)) := by
  let S : Set ℝ≥0∞ := factorialDerivativeSeries p k '' Iio 1
  have hsup_le : sSup S ≤ factorialMoment p k := by
    apply sSup_le
    intro y hy
    rcases hy with ⟨z, _hz, rfl⟩
    exact factorialDerivativeSeries_le_factorialMoment p k z
  have hseq_mem (j : ℕ) : factorialDerivativeSeries p k (pgfBoundaryPoint j) ∈ S := by
    refine ⟨pgfBoundaryPoint j, ?_, rfl⟩
    change 1 - (1 / 2 : ℝ) ^ j < 1
    exact sub_lt_self 1 (pow_pos (by norm_num) j)
  have hmoment_le : factorialMoment p k ≤ sSup S := by
    apply le_of_tendsto' (tendsto_factorialDerivativeSeries_boundary_seq p k)
    intro j
    exact le_sSup (hseq_mem j)
  have hsup : sSup S = factorialMoment p k := le_antisymm hsup_le hmoment_le
  rw [← hsup]
  exact (monotone_factorialDerivativeSeries p k).tendsto_nhdsLT 1

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
