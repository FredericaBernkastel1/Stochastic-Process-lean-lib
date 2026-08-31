/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Multivariate central limit theorem

The proof is a thin bridge through the canonical scalar i.i.d. central limit theorem and the
canonical characteristic-function form of the Cramér--Wold device.  In particular, this module
does not introduce another notion of weak convergence, characteristic function, or Gaussian law.
-/

@[expose] public section

open Filter MeasureTheory Matrix WithLp
open scoped RealInnerProductSpace Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized prefix sum of a vector-valued sequence. -/
noncomputable def normalizedVectorPartialSum
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  (Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, X j ω

/-- **Multivariate i.i.d. central limit theorem.**  Scalar projections are sent through Mathlib's
one-dimensional CLT, and Lévy continuity closes the vector-valued law.  The covariance is allowed
to be singular: only positive semidefiniteness is assumed. -/
theorem tendstoInDistribution_normalizedVectorPartialSum
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (hX2 : MemLp (X 0) 2 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : ∀ t : EuclideanSpace ℝ ι,
      Var[fun ω ↦ ⟪t, X 0 ω⟫; P] = t ⬝ᵥ S *ᵥ t)
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) :
    TendstoInDistribution (normalizedVectorPartialSum X) atTop id (fun _ ↦ P)
      (multivariateGaussian 0 S) := by
  refine ⟨fun n ↦ ?_, measurable_id.aemeasurable, ?_⟩
  · change AEMeasurable
      (fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P
    exact (Finset.aemeasurable_fun_sum (Finset.range n)
      fun i _ ↦ (hident i).aemeasurable_fst).const_smul (Real.sqrt n)⁻¹
  · apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    let Xt : ℕ → Ω → ℝ := fun n ω ↦ ⟪t, X n ω⟫
    have hXt2 : MemLp (Xt 0) 2 P := hX2.const_inner t
    have hXtmean : ∫ ω, Xt 0 ω ∂P = 0 := by
      rw [show Xt 0 = fun ω ↦ ⟪t, X 0 ω⟫ from rfl,
        integral_inner (hX2.integrable (by norm_num)), hmean]
      simp
    have hXtindep : iIndepFun Xt P := by
      exact hindep.comp (fun _ x ↦ ⟪t, x⟫) (fun _ ↦ by fun_prop)
    have hXtident : ∀ n, IdentDistrib (Xt n) (Xt 0) P P := by
      intro n
      change IdentDistrib ((fun x ↦ ⟪t, x⟫) ∘ X n)
        ((fun x ↦ ⟪t, x⟫) ∘ X 0) P P
      exact (hident n).comp (u := fun x ↦ ⟪t, x⟫) (by fun_prop)
    let q : NNReal := (variance (Xt 0) P).toNNReal
    have hY : HasLaw (fun x : ℝ ↦ x) (gaussianReal 0 q) (gaussianReal 0 q) := by
      refine ⟨measurable_id.aemeasurable, ?_⟩
      simp
    have hscalar := tendstoInDistribution_inv_sqrt_mul_sum_sub
      (P := P) (P' := gaussianReal 0 q) (X := Xt) (Y := fun x : ℝ ↦ x)
      hY hXt2 hXtindep hXtident
    have hchar :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hscalar.tendsto) (1 : ℝ)
    have hcf (n : ℕ) :
        charFun (P.map (normalizedVectorPartialSum X n)) t =
          charFun (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
            (∑ j ∈ Finset.range n, Xt j ω - n * ∫ ω, Xt 0 ω ∂P))) 1 := by
      change charFun (P.map (fun ω ↦ (Real.sqrt n)⁻¹ •
        ∑ i ∈ Finset.range n, X i ω)) t = _
      have hvecMeas : AEMeasurable
          (fun ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P := by
        apply AEMeasurable.congr
          ((Finset.aemeasurable_fun_sum (Finset.range n)
            fun i _ ↦ (hident i).aemeasurable_fst).const_smul (Real.sqrt n)⁻¹)
        exact ae_of_all _ fun _ ↦ rfl
      rw [charFun_apply, charFun_apply,
        integral_map hvecMeas (Measurable.aestronglyMeasurable (by fun_prop)),
        integral_map (hscalar.forall_aemeasurable n)
          (Measurable.aestronglyMeasurable (by fun_prop))]
      apply integral_congr_ae
      filter_upwards [] with ω
      congr 2
      rw [inner_smul_left, sum_inner]
      have hs : (∑ i ∈ Finset.range n, ⟪X i ω, t⟫) =
          ∑ i ∈ Finset.range n, ⟪t, X i ω⟫ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact real_inner_comm _ _
      rw [hs]
      simp only [Xt, hXtmean, mul_zero, sub_zero, RCLike.inner_apply, conj_trivial,
        one_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    have htarget : charFun (multivariateGaussian 0 S) t =
        charFun (gaussianReal 0 q) 1 := by
      have hq : 0 ≤ t ⬝ᵥ S *ᵥ t := by
        simpa using hS.dotProduct_mulVec_nonneg t
      have hv : variance (Xt 0) P = t ⬝ᵥ S *ᵥ t := by
        simpa only [Xt] using hvar t
      simp [q, hv, charFun_multivariateGaussian hS, charFun_gaussianReal,
        Real.toNNReal, max_eq_left hq]
    have hchar' : Tendsto
        (fun n : ℕ ↦ charFun (P.map (fun ω ↦ (Real.sqrt n)⁻¹ *
          (∑ j ∈ Finset.range n, Xt j ω - n * ∫ ω, Xt 0 ω ∂P))) 1)
        atTop (𝓝 (charFun (gaussianReal 0 q) 1)) := by
      simpa only [ProbabilityMeasure.coe_mk, hY.map_eq] using hchar
    have hplain : Tendsto
        (fun n ↦ charFun (P.map (normalizedVectorPartialSum X n)) t) atTop
        (𝓝 (charFun (multivariateGaussian 0 S) t)) := by
      convert hchar' using 1
      · funext n
        exact hcf n
      · exact congrArg 𝓝 htarget
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hplain

end ProbabilityTheory
