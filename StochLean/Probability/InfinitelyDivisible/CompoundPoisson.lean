/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import StochLean.Probability.InfinitelyDivisible.Basic

/-!
# Compound Poisson laws

The construction is a genuine probability mixture: draw a Poisson count and then use the
corresponding convolution power of the jump law.  The zero-rate branch is proved explicitly and
does not depend on division by the intensity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp [Measure.dirac_apply']

namespace CompoundPoisson

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

theorem measurable_convPow (μ : ProbabilityMeasure G) :
    Measurable (fun n : ℕ ↦ (ProbabilityMeasure.convPow μ n : Measure G)) :=
  measurable_of_countable _

/-- The compound Poisson law of intensity `r` and jump law `μ`. -/
noncomputable def law (r : ℝ≥0) (μ : ProbabilityMeasure G) : ProbabilityMeasure G := by
  let f : ℕ → Measure G := fun n ↦ ProbabilityMeasure.convPow μ n
  refine ⟨(poissonMeasure r).bind f, ?_⟩
  apply isProbabilityMeasure_bind (measurable_convPow μ).aemeasurable
  exact ae_of_all _ fun n ↦ inferInstance

@[simp, norm_cast]
theorem coe_law (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ((law r μ : ProbabilityMeasure G) : Measure G) =
      (poissonMeasure r).bind (fun n ↦ ProbabilityMeasure.convPow μ n) :=
  rfl

/-- Zero intensity gives the Dirac law at the additive identity for every jump law. -/
@[simp]
theorem law_zero (μ : ProbabilityMeasure G) :
    law 0 μ = ProbabilityMeasure.pointMass (G := G) 0 := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [coe_law, poissonMeasure_zero,
    Measure.dirac_bind (measurable_convPow μ) 0]
  rfl

/-- The measurable-set formula for a compound Poisson mixture. -/
theorem law_apply (r : ℝ≥0) (μ : ProbabilityMeasure G) {s : Set G}
    (hs : MeasurableSet s) :
    ((law r μ : ProbabilityMeasure G) : Measure G) s =
      ∫⁻ n, (ProbabilityMeasure.convPow μ n : Measure G) s ∂poissonMeasure r := by
  rw [coe_law, Measure.bind_apply hs (measurable_convPow μ).aemeasurable]

section CharacteristicFunction

/-- Characteristic functions turn convolution powers into ordinary powers. -/
theorem charFun_convPow (μ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (ProbabilityMeasure.convPow μ n : Measure ℝ) t =
      charFun (μ : Measure ℝ) t ^ n := by
  induction n with
  | zero => simp [ProbabilityMeasure.convPow_zero, ProbabilityMeasure.pointMass]
  | succ n ih =>
      rw [ProbabilityMeasure.convPow_succ, ProbabilityMeasure.coe_conv, charFun_conv, ih,
        pow_succ]

/-- The characteristic function of the rate/jump-law presentation of a compound Poisson law. -/
theorem charFun_law (r : ℝ≥0) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (law r μ : Measure ℝ) t =
      Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
  rw [charFun_apply, coe_law, poissonMeasure]
  rw [Measure.bind_sum]
  · rw [integral_sum_measure]
    · have hcoeff (n : ℕ) :
          (ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)).toReal =
            Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial :=
        ENNReal.toReal_ofReal (by positivity)
      simp_rw [Measure.bind_smul, Measure.dirac_bind (measurable_convPow μ),
        MeasureTheory.integral_smul_measure, hcoeff, ← charFun_apply, charFun_convPow]
      change (∑' n : ℕ,
          ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial : ℝ) : ℂ) *
            charFun (μ : Measure ℝ) t ^ n) = _
      calc
        ∑' n : ℕ,
            ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial : ℝ) : ℂ) *
              charFun (μ : Measure ℝ) t ^ n =
            (Real.exp (-r) : ℂ) *
              ∑' n : ℕ, (((r : ℂ) * charFun (μ : Measure ℝ) t) ^ n /
                n.factorial) := by
          rw [← tsum_mul_left]
          congr 1
          funext n
          push_cast
          rw [mul_pow]
          ring
        _ = (Real.exp (-r) : ℂ) *
            Complex.exp ((r : ℂ) * charFun (μ : Measure ℝ) t) := by
          rw [(NormedSpace.expSeries_div_hasSum_exp
            ((r : ℂ) * charFun (μ : Measure ℝ) t)).tsum_eq, ← Complex.exp_eq_exp_ℂ]
        _ = Complex.exp ((r : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          push_cast
          congr 1
          ring
    · letI : IsFiniteMeasure
          (Measure.sum fun i =>
            (fun n => (ProbabilityMeasure.convPow μ n : Measure ℝ)) ∘ₘ
              (ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ i / i.factorial) •
                Measure.dirac i)) := by
        rw [← Measure.bind_sum]
        · rw [← poissonMeasure, ← coe_law]
          infer_instance
        · exact (measurable_convPow μ).aemeasurable
      exact (integrable_const (1 : ℂ)).mono (by fun_prop) <|
        ae_of_all _ fun x => by
          rw [Complex.norm_exp]
          simp [mul_comm]
  · exact (measurable_convPow μ).aemeasurable

end CharacteristicFunction

/-- Compound Poisson laws with a common jump law form a convolution semigroup in the intensity. -/
theorem law_add (r s : ℝ≥0) (μ : ProbabilityMeasure G) :
    law (r + s) μ = ProbabilityMeasure.conv (law r μ) (law s μ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (poissonMeasure (r + s)).bind (fun n ↦ ProbabilityMeasure.convPow μ n) =
    ((law r μ : ProbabilityMeasure G) : Measure G) ∗
      ((law s μ : ProbabilityMeasure G) : Measure G)
  rw [← poissonMeasure_conv_poissonMeasure]
  apply Measure.ext_of_lintegral _
  intro f hf
  have hF (m : Measure ℕ) :
      AEMeasurable (fun n : ℕ ↦ (ProbabilityMeasure.convPow μ n : Measure G)) m :=
    (measurable_convPow μ).aemeasurable
  have hright : Measurable (fun x : G ↦
      ∫⁻ y, f (x + y) ∂((law s μ : ProbabilityMeasure G) : Measure G)) := by
    fun_prop
  calc
    ∫⁻ z, f z ∂(Measure.bind (poissonMeasure r ∗ poissonMeasure s)
        (fun n ↦ ProbabilityMeasure.convPow μ n)) =
        ∫⁻ n, ∫⁻ z, f z ∂(ProbabilityMeasure.convPow μ n : Measure G)
          ∂(poissonMeasure r ∗ poissonMeasure s) :=
      Measure.lintegral_bind (hF _) hf.aemeasurable
    _ = ∫⁻ n, ∫⁻ m, ∫⁻ z, f z
          ∂(ProbabilityMeasure.convPow μ (n + m) : Measure G)
          ∂poissonMeasure s ∂poissonMeasure r := by
      rw [Measure.lintegral_conv (measurable_of_countable _)]
    _ = ∫⁻ n, ∫⁻ m, ∫⁻ x, ∫⁻ y, f (x + y)
          ∂(ProbabilityMeasure.convPow μ m : Measure G)
          ∂(ProbabilityMeasure.convPow μ n : Measure G)
          ∂poissonMeasure s ∂poissonMeasure r := by
      refine MeasureTheory.lintegral_congr fun n ↦ ?_
      refine MeasureTheory.lintegral_congr fun m ↦ ?_
      rw [ProbabilityMeasure.convPow_add, ProbabilityMeasure.coe_conv,
        Measure.lintegral_conv hf]
    _ = ∫⁻ x, ∫⁻ y, f (x + y)
          ∂((law s μ : ProbabilityMeasure G) : Measure G)
          ∂((law r μ : ProbabilityMeasure G) : Measure G) := by
      symm
      rw [coe_law, Measure.lintegral_bind (hF _) hright.aemeasurable]
      refine MeasureTheory.lintegral_congr fun n ↦ ?_
      rw [coe_law]
      have hbind (x : G) :
          ∫⁻ y, f (x + y) ∂(Measure.bind (poissonMeasure s)
              (fun m ↦ ProbabilityMeasure.convPow μ m)) =
            ∫⁻ m, ∫⁻ y, f (x + y)
              ∂(ProbabilityMeasure.convPow μ m : Measure G) ∂poissonMeasure s :=
        Measure.lintegral_bind (hF _) (by fun_prop)
      simp_rw [hbind]
      apply MeasureTheory.lintegral_lintegral_swap
      have hjoint : Measurable (Function.uncurry (fun (x : G) (m : ℕ) ↦
          ∫⁻ y, f (x + y) ∂(ProbabilityMeasure.convPow μ m : Measure G))) := by
        apply measurable_from_prod_countable_left
        intro m
        have hxy : Measurable (fun p : G × G ↦ f (p.1 + p.2)) := by fun_prop
        simpa [Function.uncurry] using
          (hxy.lintegral_prod_right' (ν := (ProbabilityMeasure.convPow μ m : Measure G)))
      exact hjoint.aemeasurable
    _ = ∫⁻ z, f z ∂(((law r μ : ProbabilityMeasure G) : Measure G) ∗
          ((law s μ : ProbabilityMeasure G) : Measure G)) :=
      (Measure.lintegral_conv hf).symm

theorem isConvolutionSemigroup (μ : ProbabilityMeasure G) :
    IsConvolutionSemigroup (fun r ↦ law r μ) :=
  fun r s ↦ law_add r s μ

/-- Every compound Poisson law is infinitely divisible, including the zero-intensity law. -/
theorem isInfinitelyDivisible (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ProbabilityMeasure.IsInfinitelyDivisible (law r μ) :=
  (isConvolutionSemigroup μ).isInfinitelyDivisible r

/-- The compound Poisson law parameterized by its finite jump-intensity measure.

The zero measure is handled before normalization, so this definition never uses division by a
zero total mass as mathematics. -/
noncomputable def ofFiniteMeasure (ν : FiniteMeasure G) : ProbabilityMeasure G := by
  classical
  exact if hν : ν = 0 then ProbabilityMeasure.pointMass 0 else law ν.mass ν.normalize

@[simp]
theorem ofFiniteMeasure_zero :
    ofFiniteMeasure (0 : FiniteMeasure G) = ProbabilityMeasure.pointMass (G := G) 0 := by
  simp [ofFiniteMeasure]

theorem ofFiniteMeasure_eq_of_ne_zero {ν : FiniteMeasure G} (hν : ν ≠ 0) :
    ofFiniteMeasure ν = law ν.mass ν.normalize := by
  simp [ofFiniteMeasure, hν]

/-- The rate/jump-law presentation is recovered from the finite intensity `r • μ`. -/
theorem ofFiniteMeasure_smul_probability (r : ℝ≥0) (μ : ProbabilityMeasure G) :
    ofFiniteMeasure (r • μ.toFiniteMeasure) = law r μ := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hmass : (r • μ.toFiniteMeasure).mass = r := by
      change (r • μ.toFiniteMeasure) Set.univ = r
      rw [FiniteMeasure.smul_apply]
      simp
    have hν : r • μ.toFiniteMeasure ≠ 0 :=
      (FiniteMeasure.mass_nonzero_iff (r • μ.toFiniteMeasure)).mp (by simpa [hmass] using hr)
    rw [ofFiniteMeasure_eq_of_ne_zero hν]
    rw [hmass]
    congr 1
    apply ProbabilityMeasure.eq_of_forall_apply_eq
    intro s hs
    rw [(r • μ.toFiniteMeasure).normalize_eq_of_nonzero hν s]
    rw [hmass, FiniteMeasure.smul_apply]
    simp [hr]

end CompoundPoisson

end ProbabilityTheory
