/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Generator.QMatrix
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Uniformization of bounded Q-matrices

The dominating rate is explicit.  The zero-rate branch is `Kernel.id`, so no theorem relies on
division by zero.  For positive rate, the transition measure is assembled from a diagonal atom and
the countable off-diagonal row.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

/-- An explicit nonnegative uniformization rate dominating every exit rate. -/
structure IsUniformizationRate {E : Type*} (q : E → E → ℝ) (Λ : ℝ) : Prop where
  nonneg : 0 ≤ Λ
  dominates : ∀ x, exitRate q x ≤ Λ

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Positive-rate uniformization row as a measure. -/
noncomputable def positiveUniformizationMeasure
    (q : E → E → ℝ) (Λ : ℝ) (x : E) : Measure E :=
  ENNReal.ofReal (1 - exitRate q x / Λ) • Measure.dirac x +
    Measure.sum (fun y : {y : E // y ≠ x} =>
      ENNReal.ofReal (q x y / Λ) • Measure.dirac (y : E))

/-- For a positive dominating rate, each constructed row has total mass one. -/
theorem positiveUniformizationMeasure_apply_univ
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hΛpos : 0 < Λ) (x : E) :
    positiveUniformizationMeasure q Λ x Set.univ = 1 := by
  have hdiag : 0 ≤ 1 - exitRate q x / Λ := by
    rw [sub_nonneg]
    exact (div_le_one hΛpos).mpr (hΛ.dominates x)
  have hoff : ∀ y : {y : E // y ≠ x}, 0 ≤ q x y / Λ := fun y =>
    div_nonneg (hq.offDiag_nonneg x y y.property.symm) hΛpos.le
  have hsum : Summable (fun y : {y : E // y ≠ x} => q x y / Λ) :=
    hq.summable_div_exitBound x Λ
  have hterm (y : {y : E // y ≠ x}) :
      (ENNReal.ofReal (q x y / Λ) • Measure.dirac (y : E)) Set.univ =
        ENNReal.ofReal (q x y / Λ) := by
    rw [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ]
    simp
  rw [positiveUniformizationMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hoff hsum, tsum_div_const,
    ← hq.exitRate_eq_tsum x, ← ENNReal.ofReal_add hdiag (div_nonneg (hq.exitRate_nonneg x) hΛpos.le)]
  convert ENNReal.ofReal_one using 1
  ring

/-- The diagonal singleton mass in the positive uniformization row. -/
theorem positiveUniformizationMeasure_apply_self
    (q : E → E → ℝ) (Λ : ℝ) (x : E) :
    positiveUniformizationMeasure q Λ x {x} =
      ENNReal.ofReal (1 - exitRate q x / Λ) := by
  rw [positiveUniformizationMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton x),
    Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [smul_eq_mul]
  have hzero :
      (∑' y : {y : E // y ≠ x},
        (ENNReal.ofReal (q x y / Λ) • Measure.dirac (y : E)) {x}) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro y
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
    simp [y.property]
  rw [hzero, add_zero]
  simp

/-- Every off-diagonal singleton mass is the corresponding rate divided by the positive
uniformization rate. -/
theorem positiveUniformizationMeasure_apply_of_ne
    (q : E → E → ℝ) (Λ : ℝ) {x y : E} (hxy : x ≠ y) :
    positiveUniformizationMeasure q Λ x {y} = ENNReal.ofReal (q x y / Λ) := by
  rw [positiveUniformizationMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
    Measure.sum_apply _ (measurableSet_singleton y)]
  simp only [smul_eq_mul]
  rw [Set.indicator_of_notMem (by simpa using hxy), mul_zero, zero_add]
  let y' : {z : E // z ≠ x} := ⟨y, Ne.symm hxy⟩
  refine (tsum_eq_single y' ?_).trans ?_
  · intro z hzy
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
    have hval : (z : E) ≠ y := by
      intro hz
      apply hzy
      apply Subtype.ext
      exact hz
    simp [hval]
  · rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
    simp [y']

/-- A zero dominating rate forces every entry of the Q-matrix to vanish. -/
theorem IsUniformizationRate.eq_zero_of_zero
    {q : E → E → ℝ} (hq : IsQMatrix q) (hΛ : IsUniformizationRate q 0) :
    q = fun _ _ => 0 := by
  funext x y
  have hexit : exitRate q x = 0 :=
    le_antisymm (by simpa using hΛ.dominates x) (hq.exitRate_nonneg x)
  by_cases hxy : x = y
  · subst y
    simpa [exitRate] using congrArg Neg.neg hexit
  · have hnonneg : 0 ≤ q x y := hq.offDiag_nonneg x y hxy
    have hle : q x y ≤ ∑' z : {z : E // z ≠ x}, q x z := by
      let z : {z : E // z ≠ x} := ⟨y, Ne.symm hxy⟩
      exact (hq.summable_offDiag x).le_tsum z fun w _ =>
        hq.offDiag_nonneg x w w.property.symm
    rw [← hq.exitRate_eq_tsum x, hexit] at hle
    exact le_antisymm hle hnonneg

/-- Uniformization kernel with a mandatory safe zero-rate branch. -/
noncomputable def uniformizationKernel (q : E → E → ℝ) (Λ : ℝ) : Kernel E E :=
  if Λ = 0 then Kernel.id
  else Kernel.ofFunOfCountable (positiveUniformizationMeasure q Λ)

/-- The safe branch is definitionally the identity kernel. -/
theorem uniformizationKernel_zero (q : E → E → ℝ) :
    uniformizationKernel q 0 = Kernel.id := by
  simp [uniformizationKernel]

/-- A Q-matrix and a dominating rate produce a Markov uniformization kernel. -/
theorem isMarkovKernel_uniformizationKernel
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) : IsMarkovKernel (uniformizationKernel q Λ) := by
  by_cases hz : Λ = 0
  · rw [uniformizationKernel, if_pos hz]
    infer_instance
  · rw [uniformizationKernel, if_neg hz]
    refine ⟨fun x => ⟨?_⟩⟩
    exact positiveUniformizationMeasure_apply_univ hq hΛ (lt_of_le_of_ne hΛ.nonneg (Ne.symm hz)) x

/-- Diagonal transition probabilities of the positive-rate uniformization kernel. -/
theorem transitionProbability_uniformizationKernel_self_of_pos
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hΛpos : 0 < Λ) (x : E) :
    transitionProbability (uniformizationKernel q Λ) x {x} =
      1 + q x x / Λ := by
  rw [uniformizationKernel, if_neg hΛpos.ne']
  change (positiveUniformizationMeasure q Λ x {x}).toReal = _
  rw [positiveUniformizationMeasure_apply_self]
  have hdiag : 0 ≤ 1 - exitRate q x / Λ :=
    sub_nonneg.mpr ((div_le_one hΛpos).mpr (hΛ.dominates x))
  rw [ENNReal.toReal_ofReal hdiag]
  simp only [exitRate]
  ring

/-- Off-diagonal transition probabilities of the positive-rate uniformization kernel. -/
theorem transitionProbability_uniformizationKernel_of_ne_of_pos
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hΛpos : 0 < Λ) {x y : E} (hxy : x ≠ y) :
    transitionProbability (uniformizationKernel q Λ) x {y} = q x y / Λ := by
  rw [uniformizationKernel, if_neg hΛpos.ne']
  change (positiveUniformizationMeasure q Λ x {y}).toReal = _
  rw [positiveUniformizationMeasure_apply_of_ne q Λ hxy, ENNReal.toReal_ofReal]
  exact div_nonneg (hq.offDiag_nonneg x y hxy) hΛpos.le

/-- The one-step uniformization kernel has infinitesimal generator `q` after multiplication by
the dominating rate. -/
theorem uniformizationKernel_generator_identity
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (x y : E) :
    Λ * (transitionProbability (uniformizationKernel q Λ) x {y} -
      transitionProbability Kernel.id x {y}) = q x y := by
  by_cases hzero : Λ = 0
  · subst Λ
    have hqzero := hΛ.eq_zero_of_zero hq
    rw [hqzero]
    simp
  · have hΛpos : 0 < Λ := lt_of_le_of_ne hΛ.nonneg (Ne.symm hzero)
    by_cases hxy : x = y
    · subst y
      rw [transitionProbability_uniformizationKernel_self_of_pos hq hΛ hΛpos]
      rw [transitionProbability, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_singleton x)]
      simp
      field_simp
    · rw [transitionProbability_uniformizationKernel_of_ne_of_pos hq hΛ hΛpos hxy]
      rw [transitionProbability, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_singleton y)]
      simp [hxy]
      field_simp

/-- Scalar multiplication of every row of a kernel on a countable source space. -/
noncomputable def scaleKernel (c : ℝ≥0∞) (κ : Kernel E E) : Kernel E E :=
  Kernel.ofFunOfCountable fun x => c • κ x

@[simp]
theorem scaleKernel_apply (c : ℝ≥0∞) (κ : Kernel E E) (x : E) :
    scaleKernel c κ x = c • κ x :=
  rfl

/-- Scaling both kernels multiplies the two scalar weights under composition. -/
theorem scaleKernel_comp_scaleKernel
    (c d : ℝ≥0∞) (κ η : Kernel E E) :
    scaleKernel c κ ∘ₖ scaleKernel d η = scaleKernel (c * d) (κ ∘ₖ η) := by
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  simp only [scaleKernel_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  rw [lintegral_const_mul c (κ.measurable_coe hA)]
  rw [Kernel.comp_apply' _ _ _ hA]
  ring

/-- The scalar used in the uniformization mixture is the singleton mass of the corresponding
Poisson law. -/
noncomputable def uniformizationPoissonRate (Λ : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (Λ * (t : ℝ))

theorem coe_uniformizationPoissonRate (Λ : ℝ) (t : ℝ≥0) (hΛ : 0 ≤ Λ) :
    (uniformizationPoissonRate Λ t : ℝ) = Λ * t := by
  rw [uniformizationPoissonRate, Real.coe_toNNReal]
  exact mul_nonneg hΛ t.coe_nonneg

theorem uniformizationWeight_eq_poissonMeasure
    (Λ : ℝ) (t : ℝ≥0) (hΛ : 0 ≤ Λ) (n : ℕ) :
    ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) =
      poissonMeasure (uniformizationPoissonRate Λ t) {n} := by
  rw [poissonMeasure_singleton, coe_uniformizationPoissonRate Λ t hΛ]
  congr 1
  ring

/-- Cauchy convolution of the two Poisson weight families.  Stating the identity for an arbitrary
nonnegative test sequence makes the semigroup proof independent of a particular state or event. -/
theorem uniformizationWeights_convolution
    (Λ : ℝ) (s t : ℝ≥0) (hΛ : 0 ≤ Λ) (f : ℕ → ℝ≥0∞) :
    (∑' n : ℕ,
      ∑' m : ℕ,
        ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) *
          ENNReal.ofReal (Real.exp (-Λ * s) * (Λ * s) ^ m / m.factorial) * f (n + m)) =
      ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-Λ * (s + t)) * (Λ * (s + t)) ^ k / k.factorial) *
          f k := by
  let rt : ℝ≥0 := uniformizationPoissonRate Λ t
  let rs : ℝ≥0 := uniformizationPoissonRate Λ s
  let rst : ℝ≥0 := uniformizationPoissonRate Λ (s + t)
  have hrate : rt + rs = rst := by
    ext
    simp only [rt, rs, rst, coe_uniformizationPoissonRate Λ t hΛ,
      coe_uniformizationPoissonRate Λ s hΛ,
      coe_uniformizationPoissonRate Λ (s + t) hΛ, NNReal.coe_add]
    ring
  have hf : Measurable f := measurable_of_countable f
  calc
    (∑' n : ℕ,
      ∑' m : ℕ,
        ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) *
          ENNReal.ofReal (Real.exp (-Λ * s) * (Λ * s) ^ m / m.factorial) * f (n + m)) =
        ∫⁻ n, ∫⁻ m, f (n + m) ∂poissonMeasure rs ∂poissonMeasure rt := by
          rw [lintegral_countable']
          apply tsum_congr
          intro n
          rw [lintegral_countable']
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro m
          rw [← uniformizationWeight_eq_poissonMeasure Λ t hΛ n,
            ← uniformizationWeight_eq_poissonMeasure Λ s hΛ m]
          ring
    _ = ∫⁻ k, f k ∂(poissonMeasure rt ∗ poissonMeasure rs) := by
      exact (Measure.lintegral_conv hf).symm
    _ = ∫⁻ k, f k ∂poissonMeasure rst := by
      rw [poissonMeasure_conv_poissonMeasure, hrate]
    _ = ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-Λ * (s + t)) * (Λ * (s + t)) ^ k / k.factorial) *
          f k := by
      rw [lintegral_countable']
      apply tsum_congr
      intro k
      have hw : poissonMeasure rst {k} =
          ENNReal.ofReal
            (Real.exp (-Λ * (s + t)) * (Λ * (s + t)) ^ k / k.factorial) := by
        simp only [rst]
        rw [poissonMeasure_singleton,
          coe_uniformizationPoissonRate Λ (s + t) hΛ]
        congr 1
        rw [show Real.exp (-(Λ * (↑(s + t) : ℝ))) =
            Real.exp (-(Λ * (s : ℝ)) - Λ * (t : ℝ)) by
          congr 1
          push_cast
          ring]
        push_cast
        ring
      rw [hw, mul_comm]

/-- Differentiation at zero of a Poisson-weighted bounded scalar series. -/
theorem hasDerivAt_poissonWeightedSeries_zero
    (Λ : ℝ) (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) :
    HasDerivAt
      (fun z : ℝ => Real.exp (-Λ * z) *
        ∑' n : ℕ, (Λ * z) ^ n / n.factorial * a n)
      (Λ * (a 1 - a 0)) 0 := by
  let g : ℕ → ℝ → ℝ := fun n z => (Λ * z) ^ n / n.factorial * a n
  let g' : ℕ → ℝ → ℝ
    | 0, _ => 0
    | n + 1, z => Λ * (Λ * z) ^ n / n.factorial * a (n + 1)
  let u : ℕ → ℝ
    | 0 => 0
    | n + 1 => |Λ| * |Λ| ^ n / n.factorial
  have hu : Summable u := by
    rw [← summable_nat_add_iff (f := u) 1]
    refine ((Real.summable_pow_div_factorial |Λ|).mul_left |Λ|).congr ?_
    intro n
    simp only [u]
    ring
  have hg (n : ℕ) (z : ℝ) : HasDerivAt (g n) (g' n z) z := by
    cases n with
    | zero =>
        simpa [g, g'] using (hasDerivAt_const (x := z) (c := a 0))
    | succ n =>
        have hbase : HasDerivAt (fun w : ℝ => Λ * w) Λ z :=
          hasDerivAt_const_mul Λ
        have hpow := (hbase.pow (n + 1)).div_const (n + 1).factorial |>.mul_const (a (n + 1))
        refine (hpow.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_deriv ?_
        · simp only [g, Pi.pow_apply]
        · simp only [g', Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
          field_simp
  have hbound (n : ℕ) (z : ℝ) (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
      ‖g' n z‖ ≤ u n := by
    cases n with
    | zero => simp [g', u]
    | succ n =>
        have hzabs : |z| ≤ 1 := abs_le.mpr ⟨le_of_lt hz.1, le_of_lt hz.2⟩
        rw [Real.norm_eq_abs]
        simp only [g', u, abs_mul, abs_div, abs_pow]
        have hfactorial : (0 : ℝ) ≤ n.factorial := by positivity
        rw [abs_of_nonneg hfactorial]
        calc
          |Λ| * (|Λ| * |z|) ^ n / n.factorial * |a (n + 1)| ≤
              |Λ| * (|Λ| * 1) ^ n / n.factorial * 1 := by
                gcongr
                exact ha (n + 1)
          _ = |Λ| * |Λ| ^ n / n.factorial := by ring
  have hg0 : Summable fun n : ℕ => g n 0 := by
    apply summable_of_hasFiniteSupport
    refine (Set.finite_singleton 0).subset ?_
    intro n hn
    simp only [Set.mem_singleton_iff]
    by_contra hn0
    apply hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp [g]
  have hinner : HasDerivAt (fun z : ℝ => ∑' n : ℕ, g n z) (∑' n : ℕ, g' n 0) 0 :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
      (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun n z _ => hg n z) hbound (by norm_num) hg0 (by norm_num)
  have hsum0 : (∑' n : ℕ, g n 0) = a 0 := by
    rw [tsum_eq_single 0]
    · simp [g]
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [g]
  have hsumDeriv : (∑' n : ℕ, g' n 0) = Λ * a 1 := by
    rw [tsum_eq_single 1]
    · simp [g']
    · intro n hn
      cases n with
      | zero => simp [g']
      | succ n =>
          have hn0 : n ≠ 0 := by
            intro hz
            apply hn
            simp [hz]
          simp [g', hn0]
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-Λ * z)) (-Λ) 0 := by
    have h := (Real.hasDerivAt_exp (-Λ * 0)).comp 0 (hasDerivAt_const_mul (-Λ))
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun z => by simp [Function.comp_def]
  have hproduct := hexp.mul hinner
  rw [hsum0, hsumDeriv] at hproduct
  have hderiv :
      -Λ * a 0 + Real.exp (-Λ * 0) * (Λ * a 1) = Λ * (a 1 - a 0) := by
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  exact (hproduct.congr_deriv hderiv).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply, g])

/-- Poisson mixture of powers of the uniformization kernel. -/
noncomputable def uniformizedSemigroup (q : E → E → ℝ) (Λ : ℝ) (t : ℝ≥0) : Kernel E E :=
  Kernel.sum fun n : ℕ =>
    scaleKernel
      (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial))
      ((uniformizationKernel q Λ) ^ n)

/-- Singleton transition probabilities of the uniformized family are the corresponding
Poisson-weighted real series. -/
theorem transitionProbability_uniformizedSemigroup_eq_tsum
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (t : ℝ≥0) (x y : E) :
    transitionProbability (uniformizedSemigroup q Λ t) x {y} =
      ∑' n : ℕ, (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) *
        transitionProbability ((uniformizationKernel q Λ) ^ n) x {y} := by
  let P := uniformizationKernel q Λ
  letI : IsMarkovKernel P := isMarkovKernel_uniformizationKernel hq hΛ
  have hΛ0 : 0 ≤ Λ := hΛ.nonneg
  unfold transitionProbability uniformizedSemigroup
  rw [Kernel.sum_apply' _ x (measurableSet_singleton y)]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro n
    rw [scaleKernel_apply, Measure.smul_apply]
    simp only [smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal]
    positivity
  · intro n
    letI : IsMarkovKernel (P ^ n) := isMarkovKernel_pow P n
    rw [scaleKernel_apply, Measure.smul_apply]
    simp only [smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- The Poisson weights used by uniformization have total mass one. -/
theorem uniformizationWeights_tsum_eq_one (Λ : ℝ) (t : ℝ≥0) (hΛ : 0 ≤ Λ) :
    ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) = 1 := by
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial := by
    intro n
    positivity
  have hsummable :
      Summable (fun n : ℕ => Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) := by
    simpa only [neg_mul, mul_div_assoc] using
      (Real.summable_pow_div_factorial (Λ * (t : ℝ))).mul_left
        (Real.exp (-Λ * (t : ℝ)))
  have hexpseries :
      ∑' n : ℕ, (Λ * (t : ℝ)) ^ n / n.factorial = Real.exp (Λ * (t : ℝ)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact
      (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (Λ * (t : ℝ))).symm
  have hsumreal :
      ∑' n : ℕ, Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial = 1 := by
    simp_rw [neg_mul, mul_div_assoc]
    rw [tsum_mul_left, hexpseries, ← Real.exp_add]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable, hsumreal, ENNReal.ofReal_one]

/-- Uniformization produces a Markov kernel at every time. -/
theorem isMarkovKernel_uniformizedSemigroup
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) (t : ℝ≥0) :
    IsMarkovKernel (uniformizedSemigroup q Λ t) := by
  let P := uniformizationKernel q Λ
  letI : IsMarkovKernel P := isMarkovKernel_uniformizationKernel hq hΛ
  refine ⟨fun x => ⟨?_⟩⟩
  rw [uniformizedSemigroup, Kernel.sum_apply' _ x MeasurableSet.univ]
  calc
    ∑' n : ℕ,
        (scaleKernel
          (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial))
          ((uniformizationKernel q Λ) ^ n) x) Set.univ =
        ∑' n : ℕ,
          ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) := by
      apply tsum_congr
      intro n
      letI : IsMarkovKernel (P ^ n) := isMarkovKernel_pow P n
      change
        (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) •
          (P ^ n) x) Set.univ = _
      rw [Measure.smul_apply, measure_univ]
      simp
    _ = 1 := uniformizationWeights_tsum_eq_one Λ t hΛ.nonneg

/-- The Poisson mixture satisfies Chapman--Kolmogorov in Mathlib's kernel-composition
orientation. -/
theorem uniformizedSemigroup_add
    (q : E → E → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ) (s t : ℝ≥0) :
    uniformizedSemigroup q Λ (s + t) =
      uniformizedSemigroup q Λ t ∘ₖ uniformizedSemigroup q Λ s := by
  let P := uniformizationKernel q Λ
  rw [uniformizedSemigroup, uniformizedSemigroup, uniformizedSemigroup,
    Kernel.comp_sum_left]
  simp_rw [Kernel.comp_sum_right]
  ext x A hA
  rw [Kernel.sum_apply' _ x hA, Kernel.sum_apply' _ x hA]
  simp_rw [Kernel.sum_apply' _ x hA, scaleKernel_comp_scaleKernel,
    ← Kernel.pow_add, scaleKernel_apply, Measure.smul_apply, smul_eq_mul]
  change
    (∑' k : ℕ,
      ENNReal.ofReal
          (Real.exp (-Λ * (s + t)) * (Λ * (s + t)) ^ k / k.factorial) *
        (P ^ k) x A) =
      ∑' n : ℕ,
        ∑' m : ℕ,
          (ENNReal.ofReal
              (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) *
            ENNReal.ofReal
              (Real.exp (-Λ * s) * (Λ * s) ^ m / m.factorial)) *
            (P ^ (n + m)) x A
  rw [uniformizationWeights_convolution Λ s t hΛ (fun k => (P ^ k) x A)]

/-- The zero-rate Poisson mixture is the identity kernel at every time. -/
theorem uniformizedSemigroup_zero_rate (q : E → E → ℝ) (t : ℝ≥0) :
    uniformizedSemigroup q 0 t = Kernel.id := by
  ext x A hA
  rw [uniformizedSemigroup, Kernel.sum_apply' _ x hA, Kernel.id_apply]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    simp [scaleKernel, Kernel.ofFunOfCountable, hn, hA]
  · simp only [scaleKernel, Kernel.ofFunOfCountable, neg_zero, zero_mul, NNReal.smul_def,
      Real.exp_zero, zero_pow, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      one_mul, ENNReal.ofReal_one, one_smul]
    change ((1 : Kernel E E) x) A = (Measure.dirac x) A
    rfl

/-- At time zero the Poisson mixture is the identity kernel, for every rate. -/
theorem uniformizedSemigroup_zero_time (q : E → E → ℝ) (Λ : ℝ) :
    uniformizedSemigroup q Λ 0 = Kernel.id := by
  ext x A hA
  rw [uniformizedSemigroup, Kernel.sum_apply' _ x hA, Kernel.id_apply]
  refine (tsum_eq_single 0 ?_).trans ?_
  · intro n hn
    simp [scaleKernel, Kernel.ofFunOfCountable, hn]
  · simp only [scaleKernel, Kernel.ofFunOfCountable, NNReal.coe_zero, mul_zero, neg_zero,
      Real.exp_zero, zero_pow, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      ENNReal.ofReal_one, one_smul]
    change ((1 : Kernel E E) x) A = (Measure.dirac x) A
    rfl

/-- A bounded Q-matrix and any explicit dominating rate produce a Markov semigroup. -/
theorem isMarkovSemigroup_uniformizedSemigroup
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) :
    IsMarkovSemigroup (uniformizedSemigroup q Λ) where
  zero := uniformizedSemigroup_zero_time q Λ
  isMarkovKernel := isMarkovKernel_uniformizedSemigroup hq hΛ
  add := uniformizedSemigroup_add q Λ hΛ.nonneg

/-- The right derivative at zero of the uniformized semigroup is its prescribed Q-matrix. -/
theorem hasQMatrix_uniformizedSemigroup
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) :
    HasQMatrix (uniformizedSemigroup q Λ) q := by
  intro x y
  let P := uniformizationKernel q Λ
  letI : IsMarkovKernel P := isMarkovKernel_uniformizationKernel hq hΛ
  let a : ℕ → ℝ := fun n => transitionProbability (P ^ n) x {y}
  have ha : ∀ n, |a n| ≤ 1 := by
    intro n
    letI : IsMarkovKernel (P ^ n) := isMarkovKernel_pow P n
    change |transitionProbability (P ^ n) x {y}| ≤ 1
    rw [transitionProbability]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
    calc
      (P ^ n) x {y} ≤ (P ^ n) x Set.univ := measure_mono (Set.subset_univ {y})
      _ = 1 := measure_univ
  have hgen : Λ * (a 1 - a 0) = q x y := by
    change Λ * (transitionProbability (P ^ 1) x {y} -
      transitionProbability (P ^ 0) x {y}) = q x y
    rw [pow_one, pow_zero]
    change Λ * (transitionProbability (uniformizationKernel q Λ) x {y} -
      transitionProbability Kernel.id x {y}) = q x y
    exact uniformizationKernel_generator_identity hq hΛ x y
  have hd := (hasDerivAt_poissonWeightedSeries_zero Λ a ha).hasDerivWithinAt
    (s := Set.Ici 0)
  refine (hd.congr_deriv hgen).congr_of_mem ?_ (by simp)
  intro z hz
  rw [transitionProbability_uniformizedSemigroup_eq_tsum hq hΛ]
  rw [Real.coe_toNNReal z hz]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [a, P]
  ring

/-- The zero Q-rate branch forms the identity Markov semigroup. -/
theorem isMarkovSemigroup_uniformizedSemigroup_zero_rate (q : E → E → ℝ) :
    IsMarkovSemigroup (uniformizedSemigroup q 0) where
  zero := uniformizedSemigroup_zero_time q 0
  isMarkovKernel t := by
    rw [uniformizedSemigroup_zero_rate]
    infer_instance
  add s t := by
    rw [uniformizedSemigroup_zero_rate, uniformizedSemigroup_zero_rate,
      uniformizedSemigroup_zero_rate, Kernel.comp_id]

end ProbabilityTheory
