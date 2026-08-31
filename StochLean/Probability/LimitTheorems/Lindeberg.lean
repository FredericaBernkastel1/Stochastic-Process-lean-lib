/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.LimitTheorems.TriangularArray
public import StochLean.Internal.LimitTheorems.LindebergFeller
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

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

private theorem sq_le_rpow_tail {a x r : ℝ} (ha : 0 < a) (hax : a ≤ x) (hr : 2 < r) :
    x ^ 2 ≤ a ^ (2 - r) * x ^ r := by
  have hx : 0 < x := ha.trans_le hax
  have hneg : 2 - r ≤ 0 := sub_nonpos.mpr hr.le
  calc
    x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_two x).symm
    _ = x ^ (r + (2 - r)) := by congr 1 <;> ring
    _ = x ^ r * x ^ (2 - r) := Real.rpow_add hx r (2 - r)
    _ ≤ x ^ r * a ^ (2 - r) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha hax hneg) (Real.rpow_nonneg hx.le r)
    _ = a ^ (2 - r) * x ^ r := mul_comm _ _

private theorem lyapunovScale_identity {ε v r : ℝ} (hε : 0 < ε) (hv : 0 < v) :
    v⁻¹ * (ε * Real.sqrt v) ^ (2 - r) =
      ε ^ (2 - r) * (v ^ (r / 2))⁻¹ := by
  rw [Real.mul_rpow hε.le (Real.sqrt_nonneg v), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hv.le, ← Real.rpow_neg hv.le]
  have hinv : v⁻¹ = v ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
  rw [hinv]
  calc
    v ^ (-1 : ℝ) * (ε ^ (2 - r) * v ^ ((1 / 2 : ℝ) * (2 - r))) =
        ε ^ (2 - r) * (v ^ (-1 : ℝ) * v ^ ((1 / 2 : ℝ) * (2 - r))) := by ring
    _ = ε ^ (2 - r) * v ^ ((-1 : ℝ) + (1 / 2 : ℝ) * (2 - r)) := by
      rw [Real.rpow_add hv]
    _ = ε ^ (2 - r) * v ^ (-(r / 2)) := by congr 2 <;> ring

private theorem setLIntegral_sq_le_rpow {P : Measure Ω} {f : Ω → ℝ}
    (hf : Measurable f) {a r : ℝ} (ha : 0 < a) (hr : 2 < r) :
    (∫⁻ ω in {ω | a ^ 2 < (f ω) ^ 2}, ENNReal.ofReal ((f ω) ^ 2) ∂P) ≤
      ENNReal.ofReal (a ^ (2 - r)) *
        ∫⁻ ω, ENNReal.ofReal (|f ω| ^ r) ∂P := by
  have hr0 : 0 ≤ r := by linarith
  have hpow : Measurable (fun ω ↦ ENNReal.ofReal (|f ω| ^ r)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const hr0).measurable.comp hf.abs)
  calc
    (∫⁻ ω in {ω | a ^ 2 < (f ω) ^ 2}, ENNReal.ofReal ((f ω) ^ 2) ∂P) ≤
        ∫⁻ ω in {ω | a ^ 2 < (f ω) ^ 2},
          ENNReal.ofReal (a ^ (2 - r)) * ENNReal.ofReal (|f ω| ^ r) ∂P := by
      apply setLIntegral_mono (measurable_const.mul hpow)
      intro ω hω
      change ENNReal.ofReal ((f ω) ^ 2) ≤
        ENNReal.ofReal (a ^ (2 - r)) * ENNReal.ofReal (|f ω| ^ r)
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le (2 - r))]
      apply ENNReal.ofReal_le_ofReal
      simpa only [sq_abs] using
        (sq_le_rpow_tail ha
          (le_of_lt ((sq_lt_sq₀ ha.le (abs_nonneg (f ω))).1 (by simpa [sq_abs] using hω))) hr)
    _ = ENNReal.ofReal (a ^ (2 - r)) *
        ∫⁻ ω in {ω | a ^ 2 < (f ω) ^ 2}, ENNReal.ofReal (|f ω| ^ r) ∂P := by
      rw [lintegral_const_mul _ hpow]
    _ ≤ ENNReal.ofReal (a ^ (2 - r)) *
        ∫⁻ ω, ENNReal.ofReal (|f ω| ^ r) ∂P := by
      exact mul_le_mul_of_nonneg_left
        (setLIntegral_le_lintegral {ω | a ^ 2 < (f ω) ^ 2}
          (fun ω ↦ ENNReal.ofReal (|f ω| ^ r))) bot_le

private theorem lindebergNumerator_le_lyapunovNumerator {k : ℕ → ℕ}
    {X : TriangularArray k Ω} {P : Measure Ω} {v : ℕ → ℝ} {r ε : ℝ}
    (hX : IsMeasurableArray X) (hv : ∀ n, 0 < v n) (hr : 2 < r) (hε : 0 < ε) (n : ℕ) :
    lindebergNumerator X P v ε n ≤
      ENNReal.ofReal ((ε * Real.sqrt (v n)) ^ (2 - r)) * lyapunovNumerator X P r n := by
  unfold lindebergNumerator lyapunovNumerator
  have hsqrt : (ε * Real.sqrt (v n)) ^ 2 = ε ^ 2 * v n := by
    rw [mul_pow, Real.sq_sqrt (hv n).le]
  calc
    (∑ j, ∫⁻ ω in {ω | ε ^ 2 * v n < (X n j ω) ^ 2},
        ENNReal.ofReal ((X n j ω) ^ 2) ∂P) ≤
        ∑ j, ENNReal.ofReal ((ε * Real.sqrt (v n)) ^ (2 - r)) *
          ∫⁻ ω, ENNReal.ofReal (|X n j ω| ^ r) ∂P := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [← hsqrt]
      exact setLIntegral_sq_le_rpow (hX n j)
        (mul_pos hε (Real.sqrt_pos.2 (hv n))) hr
    _ = ENNReal.ofReal ((ε * Real.sqrt (v n)) ^ (2 - r)) *
        ∑ j, ∫⁻ ω, ENNReal.ofReal (|X n j ω| ^ r) ∂P := by
      rw [Finset.mul_sum]

/-- Lyapunov's condition at a positive variance scale implies Lindeberg's condition at the same
scale.  No independence or centering assumption is needed for this implication. -/
theorem SatisfiesLyapunovAtScale.satisfiesLindebergAtScale {k : ℕ → ℕ}
    {X : TriangularArray k Ω} {P : Measure Ω} {v : ℕ → ℝ} {r : ℝ}
    (hLyap : SatisfiesLyapunovAtScale X P v r) (hX : IsMeasurableArray X) :
    SatisfiesLindebergAtScale X P v := by
  refine ⟨hLyap.2.1, ?_⟩
  intro ε hε
  let C : ℝ≥0∞ := ENNReal.ofReal (ε ^ (2 - r))
  let g : ℕ → ℝ≥0∞ := fun n ↦
    (ENNReal.ofReal ((v n) ^ (r / 2)))⁻¹ * lyapunovNumerator X P r n
  have hg : Tendsto g atTop (𝓝 0) := hLyap.2.2
  have hcoeff : ∀ n,
      (ENNReal.ofReal (v n))⁻¹ *
          ENNReal.ofReal ((ε * Real.sqrt (v n)) ^ (2 - r)) =
        C * (ENNReal.ofReal ((v n) ^ (r / 2)))⁻¹ := by
    intro n
    dsimp only [C]
    rw [← ENNReal.ofReal_inv_of_pos (hLyap.2.1 n),
      ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (hLyap.2.1 n) (r / 2)),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (hLyap.2.1 n).le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le (2 - r))]
    exact congrArg ENNReal.ofReal (lyapunovScale_identity hε (hLyap.2.1 n))
  have hbound : ∀ n,
      (ENNReal.ofReal (v n))⁻¹ * lindebergNumerator X P v ε n ≤ C * g n := by
    intro n
    calc
      (ENNReal.ofReal (v n))⁻¹ * lindebergNumerator X P v ε n ≤
          (ENNReal.ofReal (v n))⁻¹ *
            (ENNReal.ofReal ((ε * Real.sqrt (v n)) ^ (2 - r)) *
              lyapunovNumerator X P r n) := by
        gcongr
        exact lindebergNumerator_le_lyapunovNumerator hX hLyap.2.1 hLyap.1 hε n
      _ = C * g n := by
        change _ = C * ((ENNReal.ofReal ((v n) ^ (r / 2)))⁻¹ *
          lyapunovNumerator X P r n)
        rw [← mul_assoc, hcoeff n, mul_assoc]
  have hupper : Tendsto (fun n ↦ C * g n) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hg (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ ↦ bot_le) hbound

/-- Klenke's `δ > 0` form of Lyapunov's condition implies Lindeberg's condition at the same
positive scale. -/
theorem SatisfiesLyapunovDeltaAtScale.satisfiesLindebergAtScale {k : ℕ → ℕ}
    {X : TriangularArray k Ω} {P : Measure Ω} {v : ℕ → ℝ} {δ : ℝ}
    (hLyap : SatisfiesLyapunovDeltaAtScale X P v δ) (hX : IsMeasurableArray X) :
    SatisfiesLindebergAtScale X P v :=
  hLyap.2.satisfiesLindebergAtScale hX

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

private theorem internalLindebergSum_one_eq {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hL2 : ∀ n j, MemLp (X n j) 2 P) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    StochLean.Internal.LimitTheorems.LindebergSum P (X n) 1 ε =
      (lindebergNumerator X P (fun _ ↦ 1) ε n).toReal := by
  unfold StochLean.Internal.LimitTheorems.LindebergSum lindebergNumerator
  simp only [one_pow, div_one, one_mul, mul_one]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _hj
    have hset : {ω | ε < |X n j ω|} = {ω | ε ^ 2 < (X n j ω) ^ 2} := by
      ext ω
      simpa only [Set.mem_setOf_eq, sq_abs] using
        (sq_lt_sq₀ hε.le (abs_nonneg (X n j ω))).symm
    rw [hset]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hL2 n j).integrable_sq.integrableOn
      (ae_of_all _ fun ω ↦ sq_nonneg (X n j ω))]
    exact (ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)).symm
  · intro j _hj
    have hset : {ω | ε ^ 2 < (X n j ω) ^ 2} = {ω | ε < |X n j ω|} := by
      ext ω
      simpa only [Set.mem_setOf_eq, sq_abs] using
        sq_lt_sq₀ hε.le (abs_nonneg (X n j ω))
    rw [hset, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hL2 n j).integrable_sq.integrableOn
      (ae_of_all _ fun ω ↦ sq_nonneg (X n j ω))]
    exact ENNReal.ofReal_ne_top

private theorem lindebergNumerator_ne_top {k : ℕ → ℕ} {X : TriangularArray k Ω}
    {P : Measure Ω} (hL2 : ∀ n j, MemLp (X n j) 2 P) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    lindebergNumerator X P (fun _ ↦ 1) ε n ≠ ∞ := by
  unfold lindebergNumerator
  apply ENNReal.sum_ne_top.2
  intro j _hj
  have hset : {ω | ε ^ 2 * 1 < (X n j ω) ^ 2} = {ω | ε < |X n j ω|} := by
    ext ω
    simpa only [Set.mem_setOf_eq, mul_one, sq_abs] using
      sq_lt_sq₀ hε.le (abs_nonneg (X n j ω))
  rw [hset, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hL2 n j).integrable_sq.integrableOn
    (ae_of_all _ fun ω ↦ sq_nonneg (X n j ω))]
  exact ENNReal.ofReal_ne_top

/-- The standard Gaussian regarded as a probability measure, with the weak-convergence topology
kept on the named `ProbabilityMeasure` type. -/
noncomputable def standardGaussianProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨gaussianReal (0 : ℝ) (1 : NNReal), inferInstance⟩

/-- The probability law of row `n` of a measurable triangular array. -/
noncomputable def triangularRowSumLaw {k : ℕ → ℕ} (X : TriangularArray k Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] (hX : IsMeasurableArray X) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨P.map (fun ω ↦ ∑ j, X n j ω),
    Measure.isProbabilityMeasure_map
      (Finset.measurable_sum Finset.univ (fun j _hj ↦ hX n j)).aemeasurable⟩

/-- **Lindeberg--Feller central limit theorem.**  The laws of the row sums of an independent,
centered, variance-normalized triangular array satisfying Lindeberg's condition converge weakly
to the standard Gaussian law. -/
theorem SatisfiesLindeberg.tendsto_map_triangularRowSum_standardGaussian
    {k : ℕ → ℕ} {X : TriangularArray k Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hL : SatisfiesLindeberg X P) (hk : HasNonemptyRows k) (hX : IsMeasurableArray X)
    (hindep : IsRowIndependent X P) (hcenter : IsCenteredArray X P)
    (hnorm : IsNormedArray X P) :
    Tendsto (triangularRowSumLaw X P hX) atTop (𝓝 standardGaussianProbabilityMeasure) := by
  have hunit : SatisfiesUnitLindeberg X P :=
    (satisfiesLindeberg_iff_unit hindep hnorm).mp hL
  have hLint : ∀ ε > 0, Tendsto
      (fun n ↦ StochLean.Internal.LimitTheorems.LindebergSum P (X n) 1 ε)
      atTop (𝓝 0) := by
    intro ε hε
    have hnum : Tendsto (fun n ↦ lindebergNumerator X P (fun _ ↦ 1) ε n)
        atTop (𝓝 0) := by
      simpa [SatisfiesUnitLindeberg, SatisfiesLindebergAtScale] using hunit.2 ε hε
    have hreal : Tendsto
        (fun n ↦ (lindebergNumerator X P (fun _ ↦ 1) ε n).toReal)
        atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_zero_iff
        (fun n ↦ lindebergNumerator_ne_top hnorm.1 hε n)).2 hnum
    simpa only [internalLindebergSum_one_eq hnorm.1 hε] using hreal
  have hvar : ∀ n, ∑ j, ∫ ω, (X n j ω) ^ 2 ∂P = ((1 : ℝ) : ℝ) ^ 2 := by
    intro n
    calc
      ∑ j, ∫ ω, (X n j ω) ^ 2 ∂P = ∑ j, variance (X n j) P := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (variance_of_integral_eq_zero (hX n j).aemeasurable (hcenter n j).2).symm
      _ = 1 := hnorm.2 n
      _ = ((1 : ℝ) : ℝ) ^ 2 := by norm_num
  have hrow : triangularRowSumLaw X P hX = fun n ↦
      (⟨P.map (fun ω ↦ ∑ j, X n j ω),
        Measure.isProbabilityMeasure_map
          (Finset.measurable_sum Finset.univ (fun j _hj ↦ hX n j)).aemeasurable⟩ :
        ProbabilityMeasure ℝ) := by
    funext n
    rfl
  have hgauss : standardGaussianProbabilityMeasure =
      (⟨gaussianReal (0 : ℝ) (1 : NNReal), inferInstance⟩ : ProbabilityMeasure ℝ) := rfl
  rw [hrow, hgauss]
  simpa only [div_one] using
    (StochLean.Internal.LimitTheorems.lindebergFellerRaw
      (μ := P) hk (s := fun _ ↦ 1) (fun _ ↦ zero_lt_one) hX hindep
      (fun n j ↦ (hcenter n j).2) hnorm.1 hvar hLint)

end ProbabilityTheory
