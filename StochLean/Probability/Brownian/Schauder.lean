/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.PathProperties

/-!
# Dyadic Schauder approximation of Brownian paths

The finite polygonal approximants in this file are the special dyadic Schauder approximants on
`[0,1]`.  Their almost-sure uniform convergence is proved from Brownian path continuity and is
kept separate from the generic Hilbert-basis expansion, which converges only in `L²`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace ProbabilityTheory

/-- Left endpoint of the dyadic cell containing `t`. -/
noncomputable def dyadicLeftTime (n : ℕ) (t : NNReal) : NNReal :=
  (Nat.floor (((2 ^ n : ℕ) : NNReal) * t) : NNReal) / (2 ^ n : ℕ)

theorem dyadicLeftTime_le (n : ℕ) (t : NNReal) : dyadicLeftTime n t ≤ t := by
  have hp : (0 : NNReal) < (2 ^ n : ℕ) := by positivity
  apply (div_le_iff₀ hp).2
  simpa only [dyadicLeftTime, mul_comm] using
    (Nat.floor_le (show (0 : NNReal) ≤ ((2 ^ n : ℕ) : NNReal) * t from bot_le))

theorem lt_dyadicLeftTime_add (n : ℕ) (t : NNReal) :
    t < dyadicLeftTime n t + ((2 : NNReal)⁻¹) ^ n := by
  have hp : (0 : NNReal) < (2 ^ n : ℕ) := by positivity
  have h := Nat.lt_floor_add_one (((2 ^ n : ℕ) : NNReal) * t)
  have hdiv : t < ((Nat.floor (((2 ^ n : ℕ) : NNReal) * t) : NNReal) + 1) /
      (2 ^ n : ℕ) := by
    apply (lt_div_iff₀ hp).2
    simpa only [mul_comm] using h
  simpa only [dyadicLeftTime, add_div, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
    one_div, inv_pow] using hdiv

theorem dist_dyadicLeftTime_le (n : ℕ) (t : NNReal) :
    dist (dyadicLeftTime n t) t ≤ (((2 : NNReal)⁻¹) ^ n : NNReal) := by
  rw [NNReal.dist_eq, abs_of_nonpos]
  · have hsub : t - dyadicLeftTime n t ≤ ((2 : NNReal)⁻¹) ^ n := by
      rw [tsub_le_iff_right]
      simpa only [add_comm] using (lt_dyadicLeftTime_add n t).le
    rw [neg_sub, ← NNReal.coe_sub (dyadicLeftTime_le n t)]
    exact_mod_cast hsub
  · exact sub_nonpos.mpr (by exact_mod_cast dyadicLeftTime_le n t)

/-- Dyadic left-endpoint approximation.  Its polygonal Schauder refinement has the same mesh
control; this step version isolates the compact-uniform convergence argument. -/
noncomputable def dyadicPathApproximation (f : NNReal → ℝ) (n : ℕ) (t : NNReal) : ℝ :=
  f (dyadicLeftTime n t)

theorem tendstoUniformlyOn_dyadicPathApproximation {f : NNReal → ℝ} (hf : Continuous f) :
    TendstoUniformlyOn (dyadicPathApproximation f) f atTop (Icc (0 : NNReal) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huc : UniformContinuousOn f (Icc (0 : NNReal) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.1 huc) ε hε
  have hmesh : Tendsto (fun n : ℕ => ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ))
      atTop (nhds 0) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by positivity) (by norm_num))
  have hevent : ∀ᶠ n : ℕ in atTop, ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) < δ :=
    (tendsto_order.1 hmesh).2 δ hδ
  filter_upwards [hevent] with n hn t ht
  rw [dist_comm]
  change dist (f (dyadicLeftTime n t)) (f t) < ε
  apply hcontrol (dyadicLeftTime n t)
  · constructor
    · exact bot_le
    · exact (dyadicLeftTime_le n t).trans ht.2
  · exact ht
  · exact (dist_dyadicLeftTime_le n t).trans_lt hn

theorem IsBrownianReal.ae_tendstoUniformlyOn_dyadicPathApproximation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (dyadicPathApproximation (B · ω)) (B · ω)
      atTop (Icc (0 : NNReal) 1) := by
  filter_upwards [hB.cont] with ω hω
  exact tendstoUniformlyOn_dyadicPathApproximation hω

/-- Right endpoint of the dyadic cell, clipped at one. -/
noncomputable def dyadicRightTime (n : ℕ) (t : NNReal) : NNReal :=
  min 1 (dyadicLeftTime n t + ((2 : NNReal)⁻¹) ^ n)

theorem dyadicLeftTime_le_rightTime (n : ℕ) {t : NNReal} (ht : t ≤ 1) :
    dyadicLeftTime n t ≤ dyadicRightTime n t := by
  rw [dyadicRightTime, le_min_iff]
  exact ⟨(dyadicLeftTime_le n t).trans ht, by simp⟩

theorem le_dyadicRightTime (n : ℕ) {t : NNReal} (ht : t ≤ 1) :
    t ≤ dyadicRightTime n t := by
  rw [dyadicRightTime, le_min_iff]
  exact ⟨ht, (lt_dyadicLeftTime_add n t).le⟩

theorem dist_dyadicRightTime_le (n : ℕ) {t : NNReal} (ht : t ≤ 1) :
    dist (dyadicRightTime n t) t ≤ (((2 : NNReal)⁻¹) ^ n : NNReal) := by
  have htr := le_dyadicRightTime n ht
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast htr))]
  have hr : dyadicRightTime n t ≤ dyadicLeftTime n t + ((2 : NNReal)⁻¹) ^ n :=
    min_le_right _ _
  have hsub : dyadicRightTime n t - t ≤ ((2 : NNReal)⁻¹) ^ n := by
    rw [tsub_le_iff_right]
    simpa only [add_comm] using
      hr.trans (add_le_add_left (dyadicLeftTime_le n t) _)
  rw [← NNReal.coe_sub htr]
  exact_mod_cast hsub

/-- Barycentric coordinate of `t` in its clipped dyadic cell. -/
noncomputable def dyadicWeight (n : ℕ) (t : NNReal) : ℝ :=
  if dyadicRightTime n t = dyadicLeftTime n t then 0 else
    (((t - dyadicLeftTime n t) / (dyadicRightTime n t - dyadicLeftTime n t) : NNReal) : ℝ)

theorem dyadicWeight_nonneg (n : ℕ) (t : NNReal) : 0 ≤ dyadicWeight n t := by
  rw [dyadicWeight]
  split_ifs
  · exact le_rfl
  · positivity

theorem dyadicWeight_le_one (n : ℕ) {t : NNReal} (ht : t ≤ 1) :
    dyadicWeight n t ≤ 1 := by
  rw [dyadicWeight]
  split_ifs with heq
  · norm_num
  · exact_mod_cast (div_le_one (tsub_pos_iff_lt.mpr
      ((dyadicLeftTime_le_rightTime n ht).lt_of_ne (Ne.symm heq)))).2
        (tsub_le_tsub_right (le_dyadicRightTime n ht) _)

/-- Polygonal interpolation on the dyadic grid.  These are the canonical finite Schauder
approximants; unlike a generic Hilbert-basis expansion, they converge uniformly pathwise for
every continuous path. -/
noncomputable def dyadicSchauderApproximation (f : NNReal → ℝ) (n : ℕ) (t : NNReal) : ℝ :=
  (1 - dyadicWeight n t) * f (dyadicLeftTime n t) +
    dyadicWeight n t * f (dyadicRightTime n t)

theorem dist_dyadicSchauderApproximation_lt {f : NNReal → ℝ} {ε : ℝ}
    {n : ℕ} {t : NNReal} (ht : t ≤ 1)
    (hleft : dist (f (dyadicLeftTime n t)) (f t) < ε)
    (hright : dist (f (dyadicRightTime n t)) (f t) < ε) :
    dist (dyadicSchauderApproximation f n t) (f t) < ε := by
  let w := dyadicWeight n t
  have hw0 : 0 ≤ w := dyadicWeight_nonneg n t
  have hw1 : w ≤ 1 := dyadicWeight_le_one n ht
  have h1w : 0 ≤ 1 - w := sub_nonneg.mpr hw1
  rw [Real.dist_eq] at hleft hright ⊢
  have hmax : max |f (dyadicLeftTime n t) - f t|
      |f (dyadicRightTime n t) - f t| < ε := max_lt hleft hright
  change |(1 - w) * f (dyadicLeftTime n t) + w * f (dyadicRightTime n t) - f t| < ε
  calc
    |(1 - w) * f (dyadicLeftTime n t) + w * f (dyadicRightTime n t) - f t| =
        |(1 - w) * (f (dyadicLeftTime n t) - f t) +
          w * (f (dyadicRightTime n t) - f t)| := by ring_nf
    _ ≤ |(1 - w) * (f (dyadicLeftTime n t) - f t)| +
        |w * (f (dyadicRightTime n t) - f t)| := abs_add_le _ _
    _ = (1 - w) * |f (dyadicLeftTime n t) - f t| +
        w * |f (dyadicRightTime n t) - f t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1w, abs_of_nonneg hw0]
    _ ≤ max |f (dyadicLeftTime n t) - f t|
        |f (dyadicRightTime n t) - f t| := by
      calc
        _ ≤ (1 - w) * max |f (dyadicLeftTime n t) - f t|
              |f (dyadicRightTime n t) - f t| +
            w * max |f (dyadicLeftTime n t) - f t|
              |f (dyadicRightTime n t) - f t| := by
          gcongr <;> simp
        _ = _ := by ring
    _ < ε := hmax

theorem tendstoUniformlyOn_dyadicSchauderApproximation {f : NNReal → ℝ} (hf : Continuous f) :
    TendstoUniformlyOn (dyadicSchauderApproximation f) f atTop (Icc (0 : NNReal) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huc : UniformContinuousOn f (Icc (0 : NNReal) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.1 huc) ε hε
  have hmesh : Tendsto (fun n : ℕ => ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ))
      atTop (nhds 0) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by positivity) (by norm_num))
  have hevent : ∀ᶠ n : ℕ in atTop, ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) < δ :=
    (tendsto_order.1 hmesh).2 δ hδ
  filter_upwards [hevent] with n hn t ht
  rw [dist_comm]
  apply dist_dyadicSchauderApproximation_lt ht.2
  · apply hcontrol (dyadicLeftTime n t)
    · exact ⟨bot_le, (dyadicLeftTime_le n t).trans ht.2⟩
    · exact ht
    · exact (dist_dyadicLeftTime_le n t).trans_lt hn
  · apply hcontrol (dyadicRightTime n t)
    · exact ⟨bot_le, min_le_left _ _⟩
    · exact ht
    · exact (dist_dyadicRightTime_le n ht.2).trans_lt hn

theorem IsBrownianReal.ae_tendstoUniformlyOn_dyadicSchauderApproximation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (dyadicSchauderApproximation (B · ω)) (B · ω)
      atTop (Icc (0 : NNReal) 1) := by
  filter_upwards [hB.cont] with ω hω
  exact tendstoUniformlyOn_dyadicSchauderApproximation hω

end ProbabilityTheory
