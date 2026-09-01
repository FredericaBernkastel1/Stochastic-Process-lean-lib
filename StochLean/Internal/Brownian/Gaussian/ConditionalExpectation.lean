/-
Copyright (c) 2026 Raphael Coelho and StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, StochLean contributors
-/
module

public import Mathlib

/-!
# Conditional expectation of a bivariate Gaussian

This project-owned implementation was adapted from
`formal-applied-math/formal-mathfin`, commit
`784a8311f75a1519a23717856df9982bd6a9a370`, file
`MathFin/Foundations/BivariateGaussian.lean` (Apache-2.0).  Its namespace and API are intentionally
StochLean-owned and it has no dependency on that external package.
-/

@[expose] public section

namespace ProbabilityTheory.GaussianConditioning

open MeasureTheory

/-- Hypotheses for the bivariate-Gaussian conditional-expectation formula. -/
structure Hypotheses {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (μX μY σX σY ρ : ℝ) : Prop where
  σX_pos : 0 < σX
  σY_pos : 0 < σY
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  joint_gaussian : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P
  mean_X : ∫ ω, X ω ∂P = μX
  mean_Y : ∫ ω, Y ω ∂P = μY
  variance_Y : Var[Y; P] = σY ^ 2
  covariance_XY : cov[X, Y; P] = ρ * σX * σY

namespace Hypotheses

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ} {μX μY σX σY ρ : ℝ}

private noncomputable def linearShift (β : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ - β • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] private lemma linearShift_apply (β : ℝ) (p : ℝ × ℝ) :
    linearShift β p = (p.1 - β * p.2, p.2) := by
  simp [linearShift]

/-- For a jointly Gaussian pair, the conditional expectation is the affine regression on the
second coordinate. -/
theorem conditionalExpectation
    (h : Hypotheses P X Y μX μY σX σY ρ) :
    (P[X | MeasurableSpace.comap Y inferInstance])
      =ᵐ[P] fun ω ↦ μX + (ρ * σX / σY) * (Y ω - μY) := by
  set β : ℝ := ρ * σX / σY with hβ
  set Xhat : Ω → ℝ := fun ω ↦ μX + β * (Y ω - μY)
  have hY_le : MeasurableSpace.comap Y inferInstance ≤ mΩ := by
    rintro s ⟨t, ht, rfl⟩
    exact h.measurable_Y ht
  have hY_strong : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Y :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hXhat_strong : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] Xhat := by
    refine StronglyMeasurable.add stronglyMeasurable_const ?_
    refine StronglyMeasurable.const_mul ?_ β
    exact hY_strong.sub stronglyMeasurable_const
  have hX_int : Integrable X P := h.joint_gaussian.fst.integrable
  have hY_int : Integrable Y P := h.joint_gaussian.snd.integrable
  have hXhat_int : Integrable Xhat P := by
    refine Integrable.add (integrable_const _) ?_
    exact (hY_int.sub (integrable_const _)).const_mul β
  have hcond_Xhat : P[Xhat | MeasurableSpace.comap Y inferInstance] = Xhat :=
    condExp_of_stronglyMeasurable hY_le hXhat_strong hXhat_int
  have hpair :
      (fun ω ↦ (X ω - β * Y ω, Y ω)) = linearShift β ∘ (fun ω ↦ (X ω, Y ω)) := by
    funext ω
    simp [Function.comp]
  have hjoint_diff : HasGaussianLaw (fun ω ↦ (X ω - β * Y ω, Y ω)) P := by
    rw [hpair]
    exact h.joint_gaussian.map_of_measurable (linearShift β)
      (linearShift β).continuous.measurable
  have hcov_zero : cov[fun ω ↦ X ω - β * Y ω, Y; P] = 0 := by
    have hX_two : MemLp X 2 P := h.joint_gaussian.fst.memLp_two
    have hY_two : MemLp Y 2 P := h.joint_gaussian.snd.memLp_two
    have hβY_two : MemLp (fun ω ↦ β * Y ω) 2 P := hY_two.const_mul β
    rw [show (fun ω ↦ X ω - β * Y ω) = (fun ω ↦ X ω) - (fun ω ↦ β * Y ω)
      from rfl]
    rw [covariance_sub_left hX_two hβY_two hY_two]
    rw [show (fun ω ↦ β * Y ω) = β • Y from by
      funext ω
      simp [Pi.smul_apply, smul_eq_mul]]
    rw [covariance_smul_left, h.covariance_XY,
      show cov[Y, Y; P] = Var[Y; P] from covariance_self hY_two.aemeasurable,
      h.variance_Y]
    have hσY : σY ≠ 0 := ne_of_gt h.σY_pos
    rw [hβ]
    field_simp
    ring
  have hindep : IndepFun (fun ω ↦ X ω - β * Y ω) Y P :=
    hjoint_diff.indepFun_of_covariance_eq_zero hcov_zero
  have hdiff_meas : Measurable (fun ω ↦ X ω - β * Y ω) :=
    h.measurable_X.sub (h.measurable_Y.const_mul β)
  have hdiff_strong :
      StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ)]
        (fun ω ↦ X ω - β * Y ω) :=
    (Measurable.of_comap_le le_rfl).stronglyMeasurable
  have hdiff_le :
      MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ) ≤ mΩ :=
    hdiff_meas.comap_le
  have hindep_sigma :
      Indep (MeasurableSpace.comap (fun ω ↦ X ω - β * Y ω) (borel ℝ))
        (MeasurableSpace.comap Y inferInstance) P :=
    (IndepFun_iff_Indep _ _ _).mp hindep
  have hmean_diff : ∫ ω, X ω - β * Y ω ∂P = μX - β * μY := by
    rw [integral_sub hX_int (hY_int.const_mul β), integral_const_mul, h.mean_X, h.mean_Y]
  have hdiff_int : Integrable (fun ω ↦ X ω - β * Y ω) P :=
    hX_int.sub (hY_int.const_mul β)
  have hcond_diff :
      P[fun ω ↦ X ω - β * Y ω | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] fun _ ↦ μX - β * μY := by
    have hcond := condExp_indep_eq hdiff_le hY_le hdiff_strong hindep_sigma
    rw [hmean_diff] at hcond
    exact hcond
  have hdecomp :
      (X : Ω → ℝ) = Xhat + (fun ω ↦ X ω - β * Y ω - (μX - β * μY)) := by
    funext ω
    show X ω = (μX + β * (Y ω - μY)) + (X ω - β * Y ω - (μX - β * μY))
    ring
  have hsplit :
      P[X | MeasurableSpace.comap Y inferInstance]
        =ᵐ[P] (P[Xhat | MeasurableSpace.comap Y inferInstance]) +
          (P[fun ω ↦ X ω - β * Y ω - (μX - β * μY) |
            MeasurableSpace.comap Y inferInstance]) := by
    conv_lhs => rw [hdecomp]
    exact condExp_add hXhat_int (hdiff_int.sub (integrable_const _)) _
  have hcentered :
      P[fun ω ↦ X ω - β * Y ω - (μX - β * μY) |
        MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have hsub :
        P[fun ω ↦ X ω - β * Y ω - (μX - β * μY) |
          MeasurableSpace.comap Y inferInstance] =ᵐ[P]
          (P[fun ω ↦ X ω - β * Y ω | MeasurableSpace.comap Y inferInstance]) -
            P[fun _ : Ω ↦ μX - β * μY | MeasurableSpace.comap Y inferInstance] :=
      condExp_sub hdiff_int (integrable_const _) _
    have hconst :
        P[fun _ : Ω ↦ μX - β * μY | MeasurableSpace.comap Y inferInstance] =
          fun _ ↦ μX - β * μY := condExp_const hY_le (μX - β * μY)
    filter_upwards [hsub, hcond_diff] with ω hω₁ hω₂
    rw [hω₁, Pi.sub_apply, hω₂, hconst]
    ring
  refine hsplit.trans ?_
  filter_upwards [hcentered] with ω hω
  simp only [Pi.add_apply]
  rw [hω, hcond_Xhat]
  show (μX + β * (Y ω - μY)) + 0 = μX + (ρ * σX / σY) * (Y ω - μY)
  rw [hβ]
  ring

end Hypotheses

section ConditionalLaw

open scoped NNReal

/-- The kernel obtained by adding centered noise with law `μ` to the affine mean `a * x`. -/
noncomputable def affineNoiseKernel (a : ℝ) (μ : Measure ℝ) : Kernel ℝ ℝ :=
  (Kernel.id.prod (Kernel.const ℝ μ)).map (fun p ↦ a * p.1 + p.2)

theorem affineNoiseKernel_gaussian_apply (a x : ℝ) (v : ℝ≥0) :
    affineNoiseKernel a (gaussianReal 0 v) x = gaussianReal (a * x) v := by
  rw [affineNoiseKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def] using
    gaussianReal_map_const_add (μ := 0) (v := v) (a * x)

/-- The kernel obtained by translating a fixed noise law by a measurable state function. -/
noncomputable def translateNoiseKernel {A : Type*} [MeasurableSpace A]
    (g : A → ℝ) (μ : Measure ℝ) : Kernel A ℝ :=
  (Kernel.id.prod (Kernel.const A μ)).map (fun p ↦ g p.1 + p.2)

theorem translateNoiseKernel_apply {A : Type*} [MeasurableSpace A]
    (g : A → ℝ) (hg : Measurable g) (μ : Measure ℝ) [SFinite μ] (x : A) :
    translateNoiseKernel g μ x = μ.map (fun z ↦ g x + z) := by
  rw [translateNoiseKernel]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Attaching an independent constant kernel to the identity coordinate is the image of the
ordinary product measure under coordinate duplication. -/
theorem compProd_id_prod_const {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure C) [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.id.prod (Kernel.const A ν)) =
      (μ.prod ν).map (fun p : A × C ↦ (p.1, (p.1, p.2))) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.map_apply (by fun_prop) hs]
  rw [Measure.prod_apply ((by fun_prop : Measurable
    (fun p : A × C ↦ (p.1, (p.1, p.2)))) hs)]
  congr with x
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

/-- If `R` is independent of `Y`, then conditionally on `Y = y`, the affine sum `a*Y + R`
has the law of `a*y + R`.  This is a regular-conditional-distribution statement, not merely a
conditional-mean identity. -/
theorem condDistrib_affine_of_indepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {R Y : Ω → ℝ} (hR : Measurable R) (hY : Measurable Y)
    (hRY : IndepFun R Y P) (a : ℝ) :
    condDistrib (fun ω ↦ a * Y ω + R ω) Y P =ᵐ[P.map Y]
      affineNoiseKernel a (P.map R) := by
  let Z : Ω → ℝ × ℝ := fun ω ↦ (Y ω, R ω)
  let κPair : Kernel ℝ (ℝ × ℝ) :=
    Kernel.id.prod (Kernel.const ℝ (P.map R))
  have hprod : P.map Z = (P.map Y).prod (P.map R) := by
    exact hRY.symm.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable
  have hjoint : P.map (fun ω ↦ (Y ω, Z ω)) = P.map Y ⊗ₘ κPair := by
    calc
      P.map (fun ω ↦ (Y ω, Z ω)) =
          (P.map Z).map (fun p : ℝ × ℝ ↦ (p.1, (p.1, p.2))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = ((P.map Y).prod (P.map R)).map
          (fun p : ℝ × ℝ ↦ (p.1, (p.1, p.2))) := by rw [hprod]
      _ = P.map Y ⊗ₘ κPair := by
        exact (compProd_id_prod_const (P.map Y) (P.map R)).symm
  have hpair : condDistrib Z Y P =ᵐ[P.map Y] κPair :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY (by fun_prop) hjoint
  have hmap := condDistrib_comp (mβ := borel ℝ) (Y := Z) (μ := P) Y
    (by fun_prop : AEMeasurable Z P)
    (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ a * p.1 + p.2))
  filter_upwards [hmap, hpair] with y hy hpair_y
  change (condDistrib ((fun p : ℝ × ℝ ↦ a * p.1 + p.2) ∘ Z) Y P) y =
    (κPair.map (fun p : ℝ × ℝ ↦ a * p.1 + p.2)) y
  rw [hy, Kernel.map_apply _ (by fun_prop), hpair_y]
  rw [Kernel.map_apply _ (by fun_prop)]

/-- If `R` is independent of a state variable `Y`, the conditional law of `g(Y)+R` given the
entire state `Y` is the translate of the fixed noise law by `g(Y)`. -/
theorem condDistrib_add_state_of_indepFun
    {A Ω : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : Ω → ℝ} {Y : Ω → A} (hR : Measurable R) (hY : Measurable Y)
    (hRY : IndepFun R Y P) (g : A → ℝ) (hg : Measurable g) :
    condDistrib (fun ω ↦ g (Y ω) + R ω) Y P =ᵐ[P.map Y]
      translateNoiseKernel g (P.map R) := by
  let Z : Ω → A × ℝ := fun ω ↦ (Y ω, R ω)
  let f : A × ℝ → ℝ := fun p ↦ g p.1 + p.2
  have hf : Measurable f := hg.comp measurable_fst |>.add measurable_snd
  let κPair : Kernel A (A × ℝ) :=
    Kernel.id.prod (Kernel.const A (P.map R))
  have hprod : P.map Z = (P.map Y).prod (P.map R) := by
    exact hRY.symm.map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable
  have hjoint : P.map (fun ω ↦ (Y ω, Z ω)) = P.map Y ⊗ₘ κPair := by
    calc
      P.map (fun ω ↦ (Y ω, Z ω)) =
          (P.map Z).map (fun p : A × ℝ ↦ (p.1, (p.1, p.2))) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = ((P.map Y).prod (P.map R)).map
          (fun p : A × ℝ ↦ (p.1, (p.1, p.2))) := by rw [hprod]
      _ = P.map Y ⊗ₘ κPair := by
        exact (compProd_id_prod_const (P.map Y) (P.map R)).symm
  have hpair : condDistrib Z Y P =ᵐ[P.map Y] κPair :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY (by fun_prop) hjoint
  have hmap := condDistrib_comp (mβ := ‹MeasurableSpace A›) (Y := Z) (μ := P) Y
    (by fun_prop : AEMeasurable Z P) (f := f) hf
  filter_upwards [hmap, hpair] with y hy hpair_y
  change (condDistrib (f ∘ Z) Y P) y = (κPair.map f) y
  rw [hy, Kernel.map_apply _ hf, hpair_y]
  rw [Kernel.map_apply _ hf]

end ConditionalLaw

end ProbabilityTheory.GaussianConditioning
