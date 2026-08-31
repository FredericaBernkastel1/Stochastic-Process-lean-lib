/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.MaximalInequality.Kolmogorov
public import StochLean.Probability.LimitTheorems.Lindeberg
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.BorelCantelli
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Ordered random series and Kolmogorov's three conditions

The order of a real series is part of the API.  In particular, expectation series use convergence
of ordinary prefix sums and are not replaced by `Summable`, which would impose absolute
convergence over `ℝ`.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Prefix sum over exactly the indices `0, ..., n - 1`. -/
def orderedPartialSum {A : Type*} [AddCommMonoid A] (a : ℕ → A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range n, a k

/-- Convergence of an ordinary ordered series, without an absolute/unconditional strengthening. -/
def OrderedSeriesConverges (a : ℕ → ℝ) : Prop :=
  ∃ s : ℝ, Tendsto (orderedPartialSum a) atTop (𝓝 s)

/-- Changing finitely many terms does not affect convergence of an ordered real series. -/
theorem OrderedSeriesConverges.congr_eventually {a b : ℕ → ℝ}
    (h : OrderedSeriesConverges a) (hab : ∀ᶠ n in atTop, a n = b n) :
    OrderedSeriesConverges b := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hab
  refine ⟨s + (orderedPartialSum b N - orderedPartialSum a N), ?_⟩
  apply (hs.add tendsto_const_nhds).congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [orderedPartialSum]
  rw [← Finset.sum_range_add_sum_Ico _ hn,
    ← Finset.sum_range_add_sum_Ico _ hn]
  have htail : (∑ i ∈ Finset.Ico N n, a i) = ∑ i ∈ Finset.Ico N n, b i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hN i (Finset.mem_Ico.mp hi).1
  rw [htail]
  ring

/-- The terms of a convergent ordered real series tend to zero. -/
theorem OrderedSeriesConverges.tendsto_term_zero {a : ℕ → ℝ}
    (h : OrderedSeriesConverges a) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := h
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  have hd := hs'.sub hs
  simpa [Function.comp_apply, orderedPartialSum, Finset.sum_range_succ] using hd

/-- Ordered random prefix sums converge on one measurable full-measure event. -/
def OrderedRandomSeriesConvergesAE (X : ℕ → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop :=
  ∀ᵐ ω ∂P, ∃ s : ℝ, Tendsto (fun n ↦ orderedPartialSum (fun k ↦ X k ω) n) atTop (𝓝 s)

/-- Klenke's truncation convention includes the boundary `|X n| = K`. -/
noncomputable def threeSeriesTruncation (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if |X n ω| ≤ K then X n ω else 0

/-- Scalar form of the exact three-series truncation.  Keeping it in the public API makes the
measurability and independence transport explicit. -/
noncomputable def threeSeriesScalarTruncation (K x : ℝ) : ℝ :=
  if |x| ≤ K then x else 0

theorem measurable_threeSeriesScalarTruncation (K : ℝ) :
    Measurable (threeSeriesScalarTruncation K) := by
  exact Measurable.ite (by measurability) measurable_id measurable_const

omit [MeasurableSpace Ω] in
theorem threeSeriesTruncation_eq_comp (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) :
    threeSeriesTruncation X K n = threeSeriesScalarTruncation K ∘ X n := by
  rfl

/-- The three source conditions: summable large-jump probabilities, ordered convergence of the
truncated expectation series, and summable truncated variances. -/
def KolmogorovThreeSeriesConditions (X : ℕ → Ω → ℝ) (P : Measure Ω) (K : ℝ) : Prop :=
  (∑' n, P {ω | K < |X n ω|}) < ∞ ∧
    OrderedSeriesConverges (fun n ↦ ∫ ω, threeSeriesTruncation X K n ω ∂P) ∧
    (∑' n, ENNReal.ofReal (variance (threeSeriesTruncation X K n) P)) < ∞

@[simp]
theorem orderedPartialSum_zero {A : Type*} [AddCommMonoid A] (a : ℕ → A) :
    orderedPartialSum a 0 = 0 := by
  simp [orderedPartialSum]

theorem orderedPartialSum_succ {A : Type*} [AddCommMonoid A] (a : ℕ → A) (n : ℕ) :
    orderedPartialSum a (n + 1) = orderedPartialSum a n + a n := by
  simp [orderedPartialSum, Finset.sum_range_succ]

omit [MeasurableSpace Ω] in
@[simp]
theorem threeSeriesTruncation_of_le (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω)
    (h : |X n ω| ≤ K) : threeSeriesTruncation X K n ω = X n ω := by
  simp [threeSeriesTruncation, h]

omit [MeasurableSpace Ω] in
@[simp]
theorem threeSeriesTruncation_of_lt (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) (ω : Ω)
    (h : K < |X n ω|) : threeSeriesTruncation X K n ω = 0 := by
  simp [threeSeriesTruncation, not_le_of_gt h]

omit [MeasurableSpace Ω] in
/-- The large-jump and truncation events partition the natural domain without changing the source
boundary convention. -/
theorem threeSeriesTruncation_eq_indicator (X : ℕ → Ω → ℝ) (K : ℝ) (n : ℕ) :
    threeSeriesTruncation X K n = {ω | |X n ω| ≤ K}.indicator (X n) := by
  funext ω
  by_cases h : |X n ω| ≤ K <;> simp [threeSeriesTruncation, h]

private theorem eLpNorm_two_eq_ofReal_integral_sq_rpow {P : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable (fun ω ↦ (f ω) ^ 2) P) :
    eLpNorm f 2 P = ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [show eLpNorm f 2 P =
      (∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
    congr 2
    funext ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]]
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun ω ↦ sq_nonneg (f ω))]

/-- Klenke Exercise 6.1.4: an independent centered square-integrable sequence whose variances
have finite total sum has almost surely convergent ordered partial sums.  The proof uses the
project's natural-filtration martingale construction and Mathlib's almost-everywhere martingale
convergence theorem. -/
theorem orderedRandomSeriesConvergesAE_of_variance_tsum_lt_top
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hX2 : ∀ n, MemLp (X n) 2 P)
    (hcenter : ∀ n, ∫ ω, X n ω ∂P = 0) (hindep : iIndepFun X P)
    (hvar : (∑' n, ENNReal.ofReal (variance (X n) P)) < ∞) :
    OrderedRandomSeriesConvergesAE X P := by
  let V : ℝ≥0∞ := ∑' n, ENNReal.ofReal (variance (X n) P)
  let R : NNReal := (V ^ (1 / 2 : ℝ)).toNNReal
  have hV : V ≠ ∞ := hvar.ne
  have hR : (R : ℝ≥0∞) = V ^ (1 / 2 : ℝ) := by
    exact ENNReal.coe_toNNReal
      (ENNReal.rpow_ne_top_of_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) hV)
  have hM := martingale_partialSum_succ hXstrong
    (fun n ↦ (hX2 n).integrable (by norm_num)) hcenter hindep
  have hconv : ∀ᵐ ω ∂P, ∃ c : ℝ,
      Tendsto (fun n ↦ partialSum X (n + 1) ω) atTop (𝓝 c) := by
    apply hM.submartingale.exists_ae_tendsto_of_bdd (R := R)
    intro n
    have hsum2 : MemLp (partialSum X (n + 1)) 2 P := memLp_partialSum hX2 (n + 1)
    have hmean : ∫ ω, partialSum X (n + 1) ω ∂P = 0 :=
      integral_partialSum_eq_zero
        (fun i ↦ (hX2 i).integrable (by norm_num)) hcenter (n + 1)
    have hsq : Integrable (fun ω ↦ partialSum X (n + 1) ω ^ 2) P := hsum2.integrable_sq
    calc
      eLpNorm (partialSum X (n + 1)) 1 P ≤ eLpNorm (partialSum X (n + 1)) 2 P :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hsum2.aestronglyMeasurable
      _ = ENNReal.ofReal (variance (partialSum X (n + 1)) P) ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_two_eq_ofReal_integral_sq_rpow hsq,
          ← variance_of_integral_eq_zero hsum2.aemeasurable hmean]
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (n + 1), variance (X i) P) ^
          (1 / 2 : ℝ) := by
        rw [variance_partialSum_eq_sum hX2 hindep]
      _ = (∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (variance (X i) P)) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun i _hi ↦ variance_nonneg (X i) P
      _ ≤ V ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow
        · exact ENNReal.sum_le_tsum (Finset.range (n + 1))
        · norm_num
      _ = (R : ℝ≥0∞) := hR.symm
  filter_upwards [hconv] with ω hω
  obtain ⟨c, hc⟩ := hω
  refine ⟨c, ?_⟩
  have hc' : Tendsto
      (fun n ↦ orderedPartialSum (fun k ↦ X k ω) (n + 1)) atTop (𝓝 c) := by
    simpa only [orderedPartialSum, partialSum, Finset.sum_apply] using hc
  exact (tendsto_add_atTop_iff_nat 1).mp hc'

/-- Almost-sure convergence of an independent ordered series forces the large-jump probability
series to be finite.  This is the second Borel--Cantelli step in Kolmogorov's converse. -/
theorem largeJump_tsum_lt_top_of_orderedRandomSeriesConvergesAE
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hindep : iIndepFun X P)
    (hconv : OrderedRandomSeriesConvergesAE X P) :
    (∑' n, P {ω | K < |X n ω|}) < ∞ := by
  let A : ℕ → Set Ω := fun n ↦ {ω | K < |X n ω|}
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact measurableSet_lt measurable_const (hXstrong n).measurable.abs
  have hAindep : iIndepSet A P := by
    rw [iIndepSet_iff_meas_biInter hAmeas]
    intro s
    simpa only [A, Set.preimage_setOf_eq] using
      (hindep.measure_inter_preimage_eq_mul s
        (sets := fun _ ↦ {x : ℝ | K < |x|})
        (fun _ _ ↦ measurableSet_lt measurable_const measurable_id.abs))
  by_contra hfinite
  have htop : (∑' n, P (A n)) = ∞ :=
    le_antisymm le_top (le_of_not_gt hfinite)
  have hlimsup_one : P (limsup A atTop) = 1 :=
    ProbabilityTheory.measure_limsup_eq_one hAmeas hAindep htop
  have hterm : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    exact OrderedSeriesConverges.tendsto_term_zero hω
  have hlimsup_zero : P (limsup A atTop) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hterm] with ω hω
    rw [mem_limsup_iff_frequently_mem]
    apply not_frequently.mpr
    have hevent : ∀ᶠ n in atTop, |X n ω| < K := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hω K hK
      exact eventually_atTop.2 ⟨N, fun n hn ↦ by simpa [Real.dist_eq] using hN n hn⟩
    filter_upwards [hevent] with n hn
    exact not_lt_of_ge hn.le
  rw [hlimsup_one] at hlimsup_zero
  exact one_ne_zero hlimsup_zero

/-- Klenke's converse variance argument: an independent uniformly bounded ordered series that
converges almost surely has finite total variance.  If the variance sum diverged, normalization by
the cumulative standard deviation would produce a Lindeberg triangular array converging to the
standard Gaussian, while subtraction of the convergent uncentered sums would leave a deterministic
sequence with the same nondegenerate limit. -/
private theorem variance_tsum_lt_top_of_bounded_orderedRandomSeriesConvergesAE
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hYstrong : ∀ n, StronglyMeasurable (Y n)) (hY2 : ∀ n, MemLp (Y n) 2 P)
    (hYbound : ∀ n ω, ‖Y n ω‖ ≤ K) (hYindep : iIndepFun Y P)
    (hYconv : OrderedRandomSeriesConvergesAE Y P) :
    (∑' n, ENNReal.ofReal (variance (Y n) P)) < ∞ := by
  let v : ℕ → ℝ := fun n ↦ variance (Y n) P
  let r : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, v i
  have hv_nonneg : ∀ n, 0 ≤ v n := fun n ↦ variance_nonneg (Y n) P
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n
    exact Finset.sum_nonneg fun i _ ↦ hv_nonneg i
  by_contra hfinite
  have htop : (∑' n, ENNReal.ofReal (v n)) = ∞ := by
    apply le_antisymm le_top
    exact le_of_not_gt hfinite
  have hofReal_r : ∀ n, ENNReal.ofReal (r n) =
      ∑ i ∈ Finset.range n, ENNReal.ofReal (v i) := by
    intro n
    simp only [r]
    rw [ENNReal.ofReal_sum_of_nonneg]
    exact fun i _ ↦ hv_nonneg i
  have hr_top : Tendsto r atTop atTop := by
    apply ENNReal.tendsto_ofReal_nhds_top.mp
    have hsum := ENNReal.tendsto_nat_tsum (fun n ↦ ENNReal.ofReal (v n))
    rw [htop] at hsum
    simpa only [hofReal_r] using hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hr_top.eventually (Ioi_mem_atTop (0 : ℝ)))
  let k : ℕ → ℕ := fun n ↦ n + N + 1
  let σ : ℕ → ℝ := fun n ↦ Real.sqrt (r (k n))
  let m : ℕ → ℝ := fun n ↦ ∫ ω, Y n ω ∂P
  let A : TriangularArray k Ω := fun n j ω ↦ (Y j ω - m j) / σ n
  have hk : HasNonemptyRows k := by
    intro n
    simp [k]
  have hr_pos : ∀ n, 0 < r (k n) := by
    intro n
    exact hN (k n) (by simp [k]; omega)
  have hσ_pos : ∀ n, 0 < σ n := by
    intro n
    exact Real.sqrt_pos.2 (hr_pos n)
  have hr_shift_top : Tendsto (fun n ↦ r (k n)) atTop atTop := by
    have hshift := hr_top.comp (tendsto_add_atTop_nat (N + 1))
    simpa [Function.comp_def, k, Nat.add_assoc] using hshift
  have hσ_top : Tendsto σ atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hr_shift_top
  have hm_bound : ∀ n, |m n| ≤ K := by
    intro n
    simpa only [m, Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ (hYbound n)))
  have hcentered_bound : ∀ n ω, |Y n ω - m n| ≤ 2 * K := by
    intro n ω
    calc
      |Y n ω - m n| ≤ |Y n ω| + |m n| := abs_sub _ _
      _ ≤ K + K := add_le_add (by simpa [Real.norm_eq_abs] using hYbound n ω) (hm_bound n)
      _ = 2 * K := by ring
  have hAmeas : IsMeasurableArray A := by
    intro n j
    exact ((hYstrong j).measurable.sub measurable_const).div measurable_const
  have hA2 : ∀ n j, MemLp (A n j) 2 P := by
    intro n j
    have hsub := (hY2 j).sub (memLp_const (m j))
    simpa only [A, Pi.sub_apply, Function.const_apply, div_eq_mul_inv] using
      hsub.mul_const (σ n)⁻¹
  have hAcenter : IsCenteredArray A P := by
    intro n j
    refine ⟨(hA2 n j).integrable (by norm_num), ?_⟩
    have hYint : Integrable (Y j) P := (hY2 j).integrable (by norm_num)
    simp [A, m, integral_div, integral_sub hYint (integrable_const (m j))]
  have hAindep : IsRowIndependent A P := by
    intro n
    have hrow : iIndepFun (fun j : Fin (k n) ↦ Y j) P :=
      hYindep.precomp Fin.val_injective
    have h := hrow.comp (fun j x ↦ (x - m j) / σ n)
      (fun _ ↦ (measurable_id.sub measurable_const).div measurable_const)
    have hEq : A n = fun j : Fin (k n) ↦ (fun x ↦ (x - m j) / σ n) ∘ Y j := by
      funext j ω
      rfl
    rw [hEq]
    exact h
  have hvarA : ∀ n j, variance (A n j) P = (σ n)⁻¹ ^ 2 * v j := by
    intro n j
    rw [show A n j = fun ω ↦ (σ n)⁻¹ * (Y j ω - m j) by
      funext ω
      simp only [A, div_eq_mul_inv]
      ring]
    rw [variance_const_mul, variance_sub_const (hYstrong j).aestronglyMeasurable]
  have hAnorm : IsNormedArray A P := by
    refine ⟨hA2, ?_⟩
    intro n
    simp_rw [hvarA]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ (σ n)⁻¹ ^ 2 * v j) (k n)]
    rw [← Finset.mul_sum]
    have hσsq : (σ n) ^ 2 = r (k n) := Real.sq_sqrt (hr_nonneg (k n))
    calc
      (σ n)⁻¹ ^ 2 * r (k n) = (σ n)⁻¹ ^ 2 * (σ n) ^ 2 := by rw [hσsq]
      _ = 1 := by field_simp [ne_of_gt (hσ_pos n)]
  have hAunit : SatisfiesUnitLindeberg A P := by
    refine ⟨fun _ ↦ zero_lt_one, ?_⟩
    intro ε hε
    have hεσ : Tendsto (fun n ↦ ε * σ n) atTop atTop :=
      hσ_top.const_mul_atTop hε
    have hevent : ∀ᶠ n in atTop, 2 * K < ε * σ n :=
      hεσ.eventually (Ioi_mem_atTop (2 * K))
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    symm
    simp only [ENNReal.ofReal_one, inv_one, one_mul]
    unfold lindebergNumerator
    apply Finset.sum_eq_zero
    intro j _hj
    have hset : {ω | ε ^ 2 * 1 < (A n j ω) ^ 2} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro ω hω
      have hratio : 2 * K / σ n < ε := (div_lt_iff₀ (hσ_pos n)).2 (by simpa [mul_comm] using hn)
      have hAabs : |A n j ω| ≤ 2 * K / σ n := by
        change |(Y j ω - m j) / σ n| ≤ 2 * K / σ n
        rw [abs_div, abs_of_pos (hσ_pos n)]
        exact div_le_div_of_nonneg_right (hcentered_bound j ω) (hσ_pos n).le
      have habs_le : |A n j ω| ≤ ε := hAabs.trans hratio.le
      have hsq : (A n j ω) ^ 2 ≤ ε ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (A n j ω)) hε.le).2 habs_le
      change ε ^ 2 * 1 < (A n j ω) ^ 2 at hω
      exact (not_lt_of_ge (by simpa only [mul_one] using hsq)) hω
    rw [hset]
    simp
  have hALindeberg : SatisfiesLindeberg A P :=
    (satisfiesLindeberg_iff_unit hAindep hAnorm).2 hAunit
  have hweak := hALindeberg.tendsto_map_triangularRowSum_standardGaussian
    hk hAmeas hAindep hAcenter hAnorm
  have hAdist : TendstoInDistribution (fun n ↦ triangularRowSum A n) atTop
      (fun x : ℝ ↦ x) (fun _ ↦ P) (gaussianReal 0 1) := by
    refine ⟨fun n ↦ (measurable_triangularRowSum hAmeas n).aemeasurable,
      measurable_id.aemeasurable, ?_⟩
    have hrowsum : ∀ n, triangularRowSum A n = fun ω ↦ ∑ j, A n j ω := by
      intro n
      funext ω
      simp [triangularRowSum]
    unfold triangularRowSumLaw at hweak
    simpa [hrowsum, standardGaussianProbabilityMeasure, Measure.map_id] using hweak
  let T : ℕ → Ω → ℝ := fun n ω ↦
    orderedPartialSum (fun j ↦ Y j ω) (k n) / σ n
  have hTstrong : ∀ n, AEStronglyMeasurable (T n) P := by
    intro n
    apply Measurable.aestronglyMeasurable
    exact (Finset.measurable_fun_sum (Finset.range (k n))
      (fun i _ ↦ (hYstrong i).measurable)).div measurable_const
  have hTae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ T n ω) atTop (𝓝 0) := by
    filter_upwards [hYconv] with ω hω
    obtain ⟨y, hy⟩ := hω
    have hyshift : Tendsto
        (fun n ↦ orderedPartialSum (fun j ↦ Y j ω) (k n)) atTop (𝓝 y) := by
      have hshift := hy.comp (tendsto_add_atTop_nat (N + 1))
      simpa [Function.comp_def, k, Nat.add_assoc] using hshift
    exact hyshift.div_atTop hσ_top
  have hTinMeasure : TendstoInMeasure P T atTop (fun _ ↦ (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae hTstrong hTae
  have hnegTinMeasure : TendstoInMeasure P (fun n ω ↦ -T n ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
    apply tendstoInMeasure_of_tendsto_ae
    · exact fun n ↦ (hTstrong n).neg
    · filter_upwards [hTae] with ω hω
      simpa using hω.neg
  have hdetDist := hAdist.add_of_tendstoInMeasure_const hnegTinMeasure
    (fun n ↦ (hTstrong n).neg.aemeasurable)
  let c : ℕ → ℝ := fun n ↦ -orderedPartialSum m (k n) / σ n
  have hdetEq : ∀ n,
      (fun ω ↦ triangularRowSum A n ω + -T n ω) =ᵐ[P] (fun _ ↦ c n) := by
    intro n
    filter_upwards [] with ω
    simp only [triangularRowSum, Finset.sum_apply, A]
    rw [Fin.sum_univ_eq_sum_range
      (fun j ↦ (Y j ω - m j) / σ n) (k n)]
    change (∑ i ∈ Finset.range (k n), (Y i ω - m i) / σ n) -
      (∑ i ∈ Finset.range (k n), Y i ω) / σ n =
      -(∑ i ∈ Finset.range (k n), m i) / σ n
    simp_rw [sub_div]
    rw [Finset.sum_sub_distrib]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hconstDist : TendstoInDistribution (fun n (_ : Ω) ↦ c n) atTop
      (fun x : ℝ ↦ x) (fun _ ↦ P) (gaussianReal 0 1) :=
    TendstoInDistribution.congr hdetEq (ae_of_all _ fun x ↦ by simp) hdetDist
  have hchar := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hconstDist.tendsto) (1 : ℝ)
  have hnorm_one : Tendsto
      (fun n ↦ ‖charFun (P.map (fun _ : Ω ↦ c n)) (1 : ℝ)‖) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [Measure.map_const, measure_univ, one_smul, charFun_dirac]
    simp
  have heq := tendsto_nhds_unique hnorm_one hchar.norm
  have heq' : (1 : ℝ) = ‖charFun (gaussianReal 0 1) (1 : ℝ)‖ := by
    simpa using heq
  have hgauss_lt : ‖charFun (gaussianReal 0 1) (1 : ℝ)‖ < 1 := by
    rw [charFun_gaussianReal]
    norm_num [Complex.norm_exp, Real.exp_lt_one_iff]
  exact (ne_of_lt hgauss_lt) heq'.symm

/-- The sufficient half of **Kolmogorov's three-series theorem**.  It uses the exact closed
truncation event `|X n| ≤ K`, ordinary ordered convergence of the expectation series, and the
finite variance sum. -/
theorem kolmogorovThreeSeries_forward {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hindep : iIndepFun X P)
    (hthree : KolmogorovThreeSeriesConditions X P K) :
    OrderedRandomSeriesConvergesAE X P := by
  let Y : ℕ → Ω → ℝ := threeSeriesTruncation X K
  let m : ℕ → ℝ := fun n ↦ ∫ ω, Y n ω ∂P
  let Z : ℕ → Ω → ℝ := fun n ω ↦ Y n ω - m n
  have hYstrong : ∀ n, StronglyMeasurable (Y n) := by
    intro n
    exact (measurable_threeSeriesScalarTruncation K).comp
      (hXstrong n).measurable |>.stronglyMeasurable
  have hYbound : ∀ n ω, ‖Y n ω‖ ≤ K := by
    intro n ω
    by_cases h : |X n ω| ≤ K
    · simpa [Y, threeSeriesTruncation, h, Real.norm_eq_abs]
    · simp [Y, threeSeriesTruncation, h, hK.le]
  have hY2 : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact MemLp.of_bound (hYstrong n).aestronglyMeasurable K
      (ae_of_all _ (hYbound n))
  have hYindep : iIndepFun Y P := by
    have h := hindep.comp (fun _ ↦ threeSeriesScalarTruncation K)
      (fun _ ↦ measurable_threeSeriesScalarTruncation K)
    have hYX : Y = fun n ↦ threeSeriesScalarTruncation K ∘ X n := by
      funext n ω
      rfl
    rw [hYX]
    exact h
  have hZstrong : ∀ n, StronglyMeasurable (Z n) := by
    intro n
    exact (hYstrong n).sub stronglyMeasurable_const
  have hZ2 : ∀ n, MemLp (Z n) 2 P := by
    intro n
    exact (hY2 n).sub (memLp_const (m n))
  have hZcenter : ∀ n, ∫ ω, Z n ω ∂P = 0 := by
    intro n
    have hYint : Integrable (Y n) P := (hY2 n).integrable (by norm_num)
    simp [Z, m, integral_sub hYint (integrable_const (m n))]
  have hZindep : iIndepFun Z P := by
    have h := hYindep.comp (fun n x ↦ x - m n)
      (fun _ ↦ measurable_id.sub measurable_const)
    have hZY : Z = fun n ↦ (fun x ↦ x - m n) ∘ Y n := by
      funext n ω
      rfl
    rw [hZY]
    exact h
  have hZvar : (∑' n, ENNReal.ofReal (variance (Z n) P)) < ∞ := by
    have hv : ∀ n, variance (Z n) P = variance (Y n) P := by
      intro n
      exact variance_sub_const (hYstrong n).aestronglyMeasurable (m n)
    simpa only [hv, Y, m] using hthree.2.2
  have hZconv : OrderedRandomSeriesConvergesAE Z P :=
    orderedRandomSeriesConvergesAE_of_variance_tsum_lt_top
      hZstrong hZ2 hZcenter hZindep hZvar
  have hmconv : OrderedSeriesConverges m := by
    simpa only [m, Y] using hthree.2.1
  have hYconv : OrderedRandomSeriesConvergesAE Y P := by
    filter_upwards [hZconv] with ω hω
    obtain ⟨z, hz⟩ := hω
    obtain ⟨c, hc⟩ := hmconv
    refine ⟨z + c, ?_⟩
    apply (hz.add hc).congr'
    filter_upwards [] with n
    simp only [orderedPartialSum, Z]
    rw [Finset.sum_sub_distrib]
    ring
  have hlarge : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ {ω | K < |X n ω|} :=
    MeasureTheory.ae_eventually_notMem hthree.1.ne
  filter_upwards [hYconv, hlarge] with ω hω hωlarge
  apply OrderedSeriesConverges.congr_eventually hω
  filter_upwards [hωlarge] with n hn
  simp only [Set.mem_setOf_eq, not_lt] at hn
  exact threeSeriesTruncation_of_le X K n ω hn

/-- The necessary half of **Kolmogorov's three-series theorem**.  The proof first uses the
second Borel--Cantelli lemma to remove the large jumps, then applies the bounded-series variance
lemma to the truncated variables.  Convergence of the deterministic expectation series follows
by subtracting the convergent centered series from the convergent truncated series. -/
theorem kolmogorovThreeSeries_backward {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hindep : iIndepFun X P)
    (hconv : OrderedRandomSeriesConvergesAE X P) :
    KolmogorovThreeSeriesConditions X P K := by
  let Y : ℕ → Ω → ℝ := threeSeriesTruncation X K
  let m : ℕ → ℝ := fun n ↦ ∫ ω, Y n ω ∂P
  let Z : ℕ → Ω → ℝ := fun n ω ↦ Y n ω - m n
  have hYstrong : ∀ n, StronglyMeasurable (Y n) := by
    intro n
    exact (measurable_threeSeriesScalarTruncation K).comp
      (hXstrong n).measurable |>.stronglyMeasurable
  have hYbound : ∀ n ω, ‖Y n ω‖ ≤ K := by
    intro n ω
    by_cases h : |X n ω| ≤ K
    · simpa [Y, threeSeriesTruncation, h, Real.norm_eq_abs]
    · simp [Y, threeSeriesTruncation, h, hK.le]
  have hY2 : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact MemLp.of_bound (hYstrong n).aestronglyMeasurable K
      (ae_of_all _ (hYbound n))
  have hYindep : iIndepFun Y P := by
    have h := hindep.comp (fun _ ↦ threeSeriesScalarTruncation K)
      (fun _ ↦ measurable_threeSeriesScalarTruncation K)
    have hYX : Y = fun n ↦ threeSeriesScalarTruncation K ∘ X n := by
      funext n ω
      rfl
    rw [hYX]
    exact h
  have hlarge : (∑' n, P {ω | K < |X n ω|}) < ∞ :=
    largeJump_tsum_lt_top_of_orderedRandomSeriesConvergesAE
      hK hXstrong hindep hconv
  have hlargeAE : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ {ω | K < |X n ω|} :=
    MeasureTheory.ae_eventually_notMem hlarge.ne
  have hYconv : OrderedRandomSeriesConvergesAE Y P := by
    filter_upwards [hconv, hlargeAE] with ω hω hωlarge
    apply OrderedSeriesConverges.congr_eventually hω
    filter_upwards [hωlarge] with n hn
    simp only [Set.mem_setOf_eq, not_lt] at hn
    exact (threeSeriesTruncation_of_le X K n ω hn).symm
  have hvarY : (∑' n, ENNReal.ofReal (variance (Y n) P)) < ∞ :=
    variance_tsum_lt_top_of_bounded_orderedRandomSeriesConvergesAE
      hK hYstrong hY2 hYbound hYindep hYconv
  have hZstrong : ∀ n, StronglyMeasurable (Z n) := by
    intro n
    exact (hYstrong n).sub stronglyMeasurable_const
  have hZ2 : ∀ n, MemLp (Z n) 2 P := by
    intro n
    exact (hY2 n).sub (memLp_const (m n))
  have hZcenter : ∀ n, ∫ ω, Z n ω ∂P = 0 := by
    intro n
    have hYint : Integrable (Y n) P := (hY2 n).integrable (by norm_num)
    simp [Z, m, integral_sub hYint (integrable_const (m n))]
  have hZindep : iIndepFun Z P := by
    have h := hYindep.comp (fun n x ↦ x - m n)
      (fun _ ↦ measurable_id.sub measurable_const)
    have hZY : Z = fun n ↦ (fun x ↦ x - m n) ∘ Y n := by
      funext n ω
      rfl
    rw [hZY]
    exact h
  have hZvar : (∑' n, ENNReal.ofReal (variance (Z n) P)) < ∞ := by
    have hv : ∀ n, variance (Z n) P = variance (Y n) P := by
      intro n
      exact variance_sub_const (hYstrong n).aestronglyMeasurable (m n)
    simpa only [hv] using hvarY
  have hZconv : OrderedRandomSeriesConvergesAE Z P :=
    orderedRandomSeriesConvergesAE_of_variance_tsum_lt_top
      hZstrong hZ2 hZcenter hZindep hZvar
  have hmconv : OrderedSeriesConverges m := by
    obtain ⟨ω, hYω, hZω⟩ := (hYconv.and hZconv).exists
    obtain ⟨y, hy⟩ := hYω
    obtain ⟨z, hz⟩ := hZω
    refine ⟨y - z, ?_⟩
    apply (hy.sub hz).congr'
    filter_upwards [] with n
    simp only [orderedPartialSum, Z]
    rw [Finset.sum_sub_distrib]
    ring
  refine ⟨hlarge, ?_, ?_⟩
  · simpa only [m, Y] using hmconv
  · simpa only [Y] using hvarY

/-- **Kolmogorov's three-series theorem**, with the truncation boundary, ordered expectation
series, and variance condition fixed by `KolmogorovThreeSeriesConditions`. -/
theorem kolmogorovThreeSeries_iff {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hXstrong : ∀ n, StronglyMeasurable (X n)) (hindep : iIndepFun X P) :
    OrderedRandomSeriesConvergesAE X P ↔ KolmogorovThreeSeriesConditions X P K := by
  constructor
  · exact kolmogorovThreeSeries_backward hK hXstrong hindep
  · exact kolmogorovThreeSeries_forward hK hXstrong hindep

end ProbabilityTheory
