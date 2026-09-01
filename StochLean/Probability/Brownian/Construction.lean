/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

/- The Brownian Kolmogorov--Chentsov proof was adapted from RemyDegenne/brownian-motion
at commit 314f04a34ff75e18fd383917ae7fe7d77beb1b6f (Apache-2.0). -/

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import StochLean.MeasureTheory.Constructions.KolmogorovExtension
public import StochLean.Probability.Process.Regularity.KolmogorovChentsov

import StochLean.Internal.Brownian.Gaussian.Moment

/-!
# Continuous Brownian representatives

This module applies StochLean's generic Kolmogorov--Chentsov theorem to the canonical Mathlib
predicate `ProbabilityTheory.IsPreBrownianReal`. It selects one measurable modification with
every path locally Hoelder of all exponents strictly below `1 / 2`.
-/

@[expose] public section

open MeasureTheory NNReal Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {X : ℝ≥0 → Ω → ℝ}

namespace ProbabilityTheory

lemma IsPreBrownianReal.isAEKolmogorovProcess {n : ℕ} (hn : 0 < n) (h : IsPreBrownianReal X P) :
    IsAEKolmogorovProcess X P (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  let Y t ω := (h.aemeasurable t).mk (X t) ω
  have hXY t := (h.aemeasurable t).ae_eq_mk
  have hY := h.congr hXY
  refine ⟨Y, ?_, ?_⟩
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    refine Measurable.prodMk (h.aemeasurable s).measurable_mk (h.aemeasurable t).measurable_mk
  rotate_left
  · positivity
  · positivity
  · exact fun t ↦ (h.aemeasurable t).ae_eq_mk
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((Y s - Y t) ω) ∂_ = _
  rw [(hY.hasLaw_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (nndist _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    congr
    rw [pow_mul, NNReal.sq_sqrt]
    simp only [val_eq_coe, NNReal.coe_pow, coe_nndist, dist_nonneg, ENNReal.ofReal_pow]
    congr
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity

/-- If `X` is a pre-Brownian process then there exists a modification of `X` which is measurable
and locally β-Hölder for `0 < β < 1/2` (and thus continuous). See `IsPreBrownianReal.mk`. -/
lemma IsPreBrownianReal.exists_continuous_modification (h : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  haveI := h.isGaussianProcess.isProbabilityMeasure
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ h.isAEKolmogorovProcess (by positivity : 0 < n + 2))
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)

/-- If `h : IsPreBrownianReal X P`, then `h.mk X` is a continuous modification of `X`. -/
protected noncomputable def IsPreBrownianReal.mk (X) (h : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
  h.exists_continuous_modification.choose

lemma IsPreBrownianReal.memHolder_mk (h : IsPreBrownianReal X P) (ω : Ω) (t : ℝ≥0) (β : ℝ≥0)
    (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (h.mk X · ω) U := by
  convert h.exists_continuous_modification.choose_spec.2.2 ω t β hβ_pos ?_
  · rfl
  suffices ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) = 2⁻¹ by rw [this]; norm_cast
  refine iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_
  · calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by
      simp only [Nat.cast_add, Nat.cast_ofNat]; field_simp; ring
    _ ≤ 2⁻¹ * 1 := by grw [mul_div_assoc, (div_le_one₀ (by positivity)).2]; linarith
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_ofNat, Function.comp_apply, Nat.cast_one]
      field_simp
      ring
    rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    exact (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _

@[fun_prop]
lemma IsPreBrownianReal.measurable_mk (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) :=
  h.exists_continuous_modification.choose_spec.1 t

lemma IsPreBrownianReal.mk_ae_eq (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    h.mk X t =ᵐ[P] X t :=
  h.exists_continuous_modification.choose_spec.2.1 t

lemma IsPreBrownianReal.continuous_mk (h : IsPreBrownianReal X P) (ω : Ω) :
    Continuous (h.mk X · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := h.memHolder_mk ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem

lemma IsPreBrownianReal.isBrownianReal_mk (h : IsPreBrownianReal X P) :
    IsBrownianReal (h.mk X) P where
  toIsPreBrownianReal := h.congr fun _ ↦ (h.mk_ae_eq _).symm
  cont := ae_of_all _ h.continuous_mk

lemma IsBrownianReal.mk_ae_forall_eq (h : IsBrownianReal X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (h.toIsPreBrownianReal.mk) t ω = X t ω := by
  apply indistinguishable_of_modification _ h.cont h.toIsPreBrownianReal.mk_ae_eq
  exact .of_forall h.toIsPreBrownianReal.continuous_mk

lemma IsBrownianReal.aemeasurable (h : IsBrownianReal X P) :
    AEMeasurable (fun ω t ↦ X t ω) P := by
  refine ⟨Function.swap h.toIsPreBrownianReal.mk, by measurability, ?_⟩
  exact h.mk_ae_forall_eq.mono <| fun _ ↦ by aesop

namespace BrownianReal

private instance projectiveFamily.instIsProbabilityMeasure (I : Finset ℝ≥0) :
    IsProbabilityMeasure (projectiveFamily I) := by
  infer_instance

private instance projectiveFamily.instIsFiniteMeasure (I : Finset ℝ≥0) :
    IsFiniteMeasure (projectiveFamily I) := by
  infer_instance

set_option maxHeartbeats 400000 in
-- Elaborating the concrete dependent Brownian projective family needs more than the default.
theorem existsUnique_preBrownianLimit :
    ∃! μ : Measure (ℝ≥0 → ℝ), IsProjectiveLimit μ projectiveFamily :=
  existsUnique_isProjectiveLimit_of_standardBorel
    (ι := ℝ≥0) (α := fun _ ↦ ℝ) projectiveFamily
      isProjectiveMeasureFamily_projectiveFamily

/-- The canonical pre-Brownian probability measure obtained by applying StochLean's
standard-Borel Kolmogorov extension theorem to Mathlib's Brownian finite-dimensional family. -/
noncomputable def preBrownianMeasure : Measure (ℝ≥0 → ℝ) :=
  Classical.choose existsUnique_preBrownianLimit

private theorem isProjectiveLimit_preBrownianMeasure :
    IsProjectiveLimit preBrownianMeasure projectiveFamily := by
  change IsProjectiveLimit (Classical.choose existsUnique_preBrownianLimit) projectiveFamily
  exact Classical.choose_spec existsUnique_preBrownianLimit |>.1

instance : IsProbabilityMeasure preBrownianMeasure :=
  isProjectiveLimit_preBrownianMeasure.isProbabilityMeasure

/-- Coordinate evaluation on the canonical pre-Brownian sample space. -/
def preBrownianCoordinate : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t

@[fun_prop]
theorem measurable_preBrownianCoordinate (t : ℝ≥0) :
    Measurable (preBrownianCoordinate t) := by
  exact measurable_pi_apply t

theorem isPreBrownianReal_preBrownianCoordinate :
    IsPreBrownianReal preBrownianCoordinate preBrownianMeasure where
  hasLaw I := by
    change HasLaw I.restrict (projectiveFamily I) preBrownianMeasure
    refine ⟨(Finset.measurable_restrict I).aemeasurable, ?_⟩
    exact isProjectiveLimit_preBrownianMeasure I

/-- The canonical everywhere-continuous Brownian coordinate process selected by
Kolmogorov--Chentsov. -/
noncomputable def brownianCoordinate : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  isPreBrownianReal_preBrownianCoordinate.mk preBrownianCoordinate

@[fun_prop]
theorem measurable_brownianCoordinate (t : ℝ≥0) :
    Measurable (brownianCoordinate t) :=
  isPreBrownianReal_preBrownianCoordinate.measurable_mk t

theorem brownianCoordinate_ae_eq_preBrownianCoordinate (t : ℝ≥0) :
    brownianCoordinate t =ᵐ[preBrownianMeasure] preBrownianCoordinate t :=
  isPreBrownianReal_preBrownianCoordinate.mk_ae_eq t

theorem continuous_brownianCoordinate (ω : ℝ≥0 → ℝ) :
    Continuous (brownianCoordinate · ω) :=
  isPreBrownianReal_preBrownianCoordinate.continuous_mk ω

theorem isBrownianReal_brownianCoordinate :
    IsBrownianReal brownianCoordinate preBrownianMeasure :=
  isPreBrownianReal_preBrownianCoordinate.isBrownianReal_mk

theorem memHolder_brownianCoordinate (ω : ℝ≥0 → ℝ) (t : ℝ≥0) (β : ℝ≥0)
    (hβ : 0 < β) (hβhalf : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (brownianCoordinate · ω) U :=
  isPreBrownianReal_preBrownianCoordinate.memHolder_mk ω t β hβ hβhalf

end BrownianReal

end ProbabilityTheory
