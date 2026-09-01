/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Moments.Variance

/-!
# Bounded-support infinitely divisible laws

An infinitely divisible real probability law supported by a bounded interval is a point mass.
The proof follows Klenke's variance argument.  Support points add under convolution, so the
support diameter of an `n`-th convolution root is at most `1 / n` times the original diameter.
Popoviciu's variance bound and variance additivity then force the original variance to vanish.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

/-- The sum of support points belongs to the support of the convolution. -/
theorem add_mem_support_conv
    {μ ν : ProbabilityMeasure ℝ} {x y : ℝ}
    (hx : x ∈ (μ : Measure ℝ).support) (hy : y ∈ (ν : Measure ℝ).support) :
    x + y ∈ (μ.conv ν : Measure ℝ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hballU⟩ := Metric.mem_nhds_iff.mp hU
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hμball : 0 < (μ : Measure ℝ) (Metric.ball x δ) :=
    (Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hδ)
  have hνball : 0 < (ν : Measure ℝ) (Metric.ball y δ) :=
    (Measure.mem_support_iff_forall y).mp hy _ (Metric.ball_mem_nhds y hδ)
  have hrect : Metric.ball x δ ×ˢ Metric.ball y δ ⊆
      (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Metric.ball (x + y) ε := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    change dist (u + v) (x + y) < ε
    calc
      dist (u + v) (x + y) ≤ dist u x + dist v y := dist_add_add_le _ _ _ _
      _ < δ + δ := add_lt_add hu hv
      _ = ε := by dsimp [δ]; ring
  have hconvBall : 0 < ((μ : Measure ℝ) ∗ (ν : Measure ℝ))
      (Metric.ball (x + y) ε) := by
    unfold Measure.conv
    rw [Measure.map_apply (f := fun p : ℝ × ℝ => p.1 + p.2)
      (measurable_fst.add measurable_snd) measurableSet_ball]
    calc
      0 < (μ : Measure ℝ) (Metric.ball x δ) *
          (ν : Measure ℝ) (Metric.ball y δ) :=
        ENNReal.mul_pos hμball.ne' hνball.ne'
      _ = ((μ : Measure ℝ).prod (ν : Measure ℝ))
          (Metric.ball x δ ×ˢ Metric.ball y δ) := (Measure.prod_prod _ _).symm
      _ ≤ ((μ : Measure ℝ).prod (ν : Measure ℝ))
          ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Metric.ball (x + y) ε) :=
        measure_mono hrect
  rw [ProbabilityMeasure.coe_conv]
  exact hconvBall.trans_le (measure_mono hballU)

/-- Repeated addition of a support point remains in the support of the corresponding convolution
power. -/
theorem nat_mul_mem_support_convPow
    {ρ : ProbabilityMeasure ℝ} {x : ℝ}
    (hx : x ∈ (ρ : Measure ℝ).support) (n : ℕ) :
    (n : ℝ) * x ∈ (ρ.convPow n : Measure ℝ).support := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, ProbabilityMeasure.convPow_zero,
        ProbabilityMeasure.coe_pointMass]
      rw [Measure.mem_support_iff_forall]
      intro U hU
      rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
      norm_num
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ, ProbabilityMeasure.coe_conv]
      have h := add_mem_support_conv ih hx
      rw [ProbabilityMeasure.coe_conv] at h
      simpa only [Nat.cast_succ, add_mul, one_mul] using h

/-- Square integrability is preserved by convolution of real probability laws. -/
theorem memLp_id_conv {μ ν : ProbabilityMeasure ℝ}
    (hμ : MemLp id 2 (μ : Measure ℝ)) (hν : MemLp id 2 (ν : Measure ℝ)) :
    MemLp id 2 (μ.conv ν : Measure ℝ) := by
  rw [ProbabilityMeasure.coe_conv]
  unfold Measure.conv
  rw [memLp_map_measure_iff (f := fun p : ℝ × ℝ => p.1 + p.2) (g := id) (by fun_prop)
    (measurable_fst.add measurable_snd).aemeasurable]
  change MemLp (fun p : ℝ × ℝ => p.1 + p.2) 2
    ((μ : Measure ℝ).prod (ν : Measure ℝ))
  exact (hμ.comp_fst (ν : Measure ℝ)).add (hν.comp_snd (μ : Measure ℝ))

/-- Variance is additive under convolution of square-integrable real probability laws. -/
theorem variance_id_conv {μ ν : ProbabilityMeasure ℝ}
    (hμ : MemLp id 2 (μ : Measure ℝ)) (hν : MemLp id 2 (ν : Measure ℝ)) :
    Var[id; (μ.conv ν : Measure ℝ)] =
      Var[id; (μ : Measure ℝ)] + Var[id; (ν : Measure ℝ)] := by
  rw [ProbabilityMeasure.coe_conv]
  unfold Measure.conv
  rw [variance_id_map (X := fun p : ℝ × ℝ => p.1 + p.2)
    (measurable_fst.add measurable_snd).aemeasurable]
  simpa only [id_eq] using ProbabilityTheory.variance_add_prod hμ hν

/-- Every convolution power of a square-integrable law is square-integrable. -/
theorem memLp_id_convPow {ρ : ProbabilityMeasure ℝ}
    (hρ : MemLp id 2 (ρ : Measure ℝ)) (n : ℕ) :
    MemLp id 2 (ρ.convPow n : Measure ℝ) := by
  induction n with
  | zero =>
      simp only [ProbabilityMeasure.convPow_zero, ProbabilityMeasure.coe_pointMass]
      apply memLp_of_bounded (a := 0) (b := 0) (μ := Measure.dirac 0)
      · rw [ae_dirac_eq]
        simp
      · fun_prop
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ]
      exact memLp_id_conv ih hρ

/-- Variance of a convolution power is the power times the original variance. -/
theorem variance_id_convPow {ρ : ProbabilityMeasure ℝ}
    (hρ : MemLp id 2 (ρ : Measure ℝ)) (n : ℕ) :
    Var[id; (ρ.convPow n : Measure ℝ)] =
      (n : ℝ) * Var[id; (ρ : Measure ℝ)] := by
  induction n with
  | zero => simp [ProbabilityMeasure.coe_pointMass]
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ,
        variance_id_conv (memLp_id_convPow hρ n) hρ, ih]
      push_cast
      ring

/-- Exercise 16.1.1: an infinitely divisible real probability law carried by a bounded interval
is a Dirac law. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible.eq_pointMass_of_boundedSupport
    {μ : ProbabilityMeasure ℝ} (hID : μ.IsInfinitelyDivisible)
    {a b : ℝ} (hbound : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Set.Icc a b) :
    ∃ c : ℝ, μ = ProbabilityMeasure.pointMass c := by
  obtain ⟨z, hz⟩ := hbound.exists
  have hab : a ≤ b := hz.1.trans hz.2
  have hμsupport : (μ : Measure ℝ).support ⊆ Set.Icc a b :=
    Measure.support_subset_of_isClosed isClosed_Icc hbound
  have hμLp : MemLp id 2 (μ : Measure ℝ) :=
    memLp_of_bounded hbound (by fun_prop) 2
  have hvarBound (n : ℕ) :
      Var[id; (μ : Measure ℝ)] ≤ (b - a) ^ 2 / ((n + 1 : ℕ) : ℝ) := by
    let m : ℕ := n + 1
    have hm : 0 < m := Nat.succ_pos n
    obtain ⟨ρ, hρpow⟩ := hID m hm
    obtain ⟨x₀, hx₀⟩ := Measure.nonempty_support
      (μ := (ρ : Measure ℝ)) (by
        intro hzero
        have hu := congrArg (fun ξ : Measure ℝ => ξ Set.univ) hzero
        simp at hu)
    have hρsupport : (ρ : Measure ℝ).support ⊆
        Set.Icc (x₀ - (b - a) / (m : ℝ)) (x₀ + (b - a) / (m : ℝ)) := by
      intro x hx
      have hnx : (m : ℝ) * x ∈ (μ : Measure ℝ).support := by
        have h := nat_mul_mem_support_convPow hx m
        rw [hρpow] at h
        exact h
      have hnx₀ : (m : ℝ) * x₀ ∈ (μ : Measure ℝ).support := by
        have h := nat_mul_mem_support_convPow hx₀ m
        rw [hρpow] at h
        exact h
      have hxIcc := hμsupport hnx
      have hx₀Icc := hμsupport hnx₀
      have hmR : 0 < (m : ℝ) := by positivity
      have hl : x₀ - x ≤ (b - a) / (m : ℝ) := by
        apply (le_div_iff₀ hmR).2
        calc
          (x₀ - x) * (m : ℝ) = (m : ℝ) * x₀ - (m : ℝ) * x := by ring
          _ ≤ b - a := sub_le_sub hx₀Icc.2 hxIcc.1
      have hu : x - x₀ ≤ (b - a) / (m : ℝ) := by
        apply (le_div_iff₀ hmR).2
        calc
          (x - x₀) * (m : ℝ) = (m : ℝ) * x - (m : ℝ) * x₀ := by ring
          _ ≤ b - a := sub_le_sub hxIcc.2 hx₀Icc.1
      constructor <;> linarith
    have hρbound : ∀ᵐ x ∂(ρ : Measure ℝ),
        x ∈ Set.Icc (x₀ - (b - a) / (m : ℝ))
          (x₀ + (b - a) / (m : ℝ)) := by
      filter_upwards [Measure.support_mem_ae (μ := (ρ : Measure ℝ))] with x hx
      exact hρsupport hx
    have hρLp : MemLp id 2 (ρ : Measure ℝ) :=
      memLp_of_bounded hρbound (by fun_prop) 2
    have hρvar := ProbabilityTheory.variance_le_sq_of_bounded hρbound (by fun_prop)
    have hρvar' : Var[id; (ρ : Measure ℝ)] ≤
        (((x₀ + (b - a) / (m : ℝ)) -
          (x₀ - (b - a) / (m : ℝ))) / 2) ^ 2 := by
      change Var[(fun x : ℝ => x); (ρ : Measure ℝ)] ≤ _
      exact hρvar
    have hvarEq := variance_id_convPow hρLp m
    rw [hρpow] at hvarEq
    have hmR : 0 < (m : ℝ) := by positivity
    calc
      Var[id; (μ : Measure ℝ)] =
          (m : ℝ) * Var[id; (ρ : Measure ℝ)] := hvarEq
      _ ≤ (m : ℝ) *
          (((x₀ + (b - a) / (m : ℝ)) -
            (x₀ - (b - a) / (m : ℝ))) / 2) ^ 2 := by gcongr
      _ = (b - a) ^ 2 / (m : ℝ) := by field_simp; ring
      _ = (b - a) ^ 2 / ((n + 1 : ℕ) : ℝ) := by rfl
  have htendsto : Tendsto (fun n : ℕ => (b - a) ^ 2 / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat ((b - a) ^ 2)).comp
        (tendsto_add_atTop_nat 1)
  have hvarNonpos : Var[id; (μ : Measure ℝ)] ≤ 0 :=
    ge_of_tendsto' htendsto hvarBound
  have hvarZero : Var[id; (μ : Measure ℝ)] = 0 :=
    le_antisymm hvarNonpos (ProbabilityTheory.variance_nonneg id (μ : Measure ℝ))
  let c : ℝ := ∫ x, x ∂(μ : Measure ℝ)
  refine ⟨c, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  have hae : (fun x : ℝ => x) =ᵐ[(μ : Measure ℝ)] (fun _ => c) := by
    filter_upwards [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hμLp hvarZero]
      with x hx
    simpa [c] using hx
  calc
    (μ : Measure ℝ) = (μ : Measure ℝ).map (fun x : ℝ => x) := by simp
    _ = (μ : Measure ℝ).map (fun _ : ℝ => c) := Measure.map_congr hae
    _ = Measure.dirac c := by simp [Measure.map_const]
    _ = (ProbabilityMeasure.pointMass c : Measure ℝ) := rfl

end ProbabilityTheory
