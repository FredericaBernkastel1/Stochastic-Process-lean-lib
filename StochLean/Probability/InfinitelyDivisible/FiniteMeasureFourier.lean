/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine

/-!
# Fourier continuity for finite measures

The usual Lévy continuity theorem is stated for probability measures.  Converse
Lévy--Khintchine arguments naturally produce finite weighted measures, so this module supplies the
corresponding finite-measure bridge by separating total mass from the normalized probability law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

theorem charFun_finiteMeasure_normalize {ν : FiniteMeasure ℝ} (hν : ν ≠ 0) (t : ℝ) :
    charFun (ν.normalize : Measure ℝ) t =
      ((ν.mass : ℝ)⁻¹ : ℂ) * charFun (ν : Measure ℝ) t := by
  rw [charFun_apply_real, ν.toMeasure_normalize_eq_of_nonzero hν,
    show (ν.mass⁻¹ • (ν : Measure ℝ)) =
      (((ν.mass⁻¹ : NNReal) : ENNReal) • (ν : Measure ℝ)) by rfl,
    integral_smul_measure]
  rw [ENNReal.coe_toReal, charFun_apply_real]
  simp only [Complex.real_smul]
  push_cast
  norm_num

/-- Finite-measure form of Lévy's continuity theorem.  Pointwise Fourier convergence and
continuity at zero determine a finite limiting measure, provided the total masses converge. -/
theorem exists_finiteMeasure_of_tendsto_charFun
    {ν : ℕ → FiniteMeasure ℝ} {φ : ℝ → ℂ} {m : NNReal}
    (hφ : ContinuousAt φ 0)
    (hmass : Tendsto (fun n => (ν n).mass) atTop (𝓝 m))
    (hchar : ∀ t, Tendsto (fun n => charFun (ν n : Measure ℝ) t) atTop (𝓝 (φ t))) :
    ∃ ν₀ : FiniteMeasure ℝ,
      (∀ t, charFun (ν₀ : Measure ℝ) t = φ t) ∧ Tendsto ν atTop (𝓝 ν₀) := by
  by_cases hm : m = 0
  · subst m
    have hνzero : Tendsto ν atTop (𝓝 0) :=
      FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
    have hφzero : φ = 0 := by
      funext t
      apply norm_eq_zero.mp
      apply le_antisymm
      · have hnorm := continuous_norm.continuousAt.tendsto.comp (hchar t)
        change Tendsto (fun n => ‖charFun (ν n : Measure ℝ) t‖) atTop
          (𝓝 ‖φ t‖) at hnorm
        have hmassReal : Tendsto (fun n => NNReal.toReal (ν n).mass) atTop (𝓝 0) := by
          have h := NNReal.continuous_coe.continuousAt.tendsto.comp hmass
          change Tendsto (fun n => NNReal.toReal (ν n).mass) atTop
            (𝓝 (NNReal.toReal 0)) at h
          simpa only [NNReal.coe_zero] using h
        apply le_of_tendsto_of_tendsto' hnorm hmassReal
        intro n
        change ‖charFun (ν n : Measure ℝ) t‖ ≤ NNReal.toReal (ν n).mass
        rw [← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass,
          ← Measure.real_def]
        exact norm_charFun_le t
      · exact norm_nonneg _
    refine ⟨0, ?_, hνzero⟩
    intro t
    rw [hφzero]
    simp
  · have hmpos : 0 < m := (pos_iff_ne_zero.mpr hm)
    have heventuallyNonzero : ∀ᶠ n : ℕ in atTop, ν n ≠ 0 := by
      have hmassPos : ∀ᶠ n : ℕ in atTop, 0 < (ν n).mass :=
        hmass.eventually (eventually_gt_nhds hmpos)
      exact hmassPos.mono fun n hn =>
        (FiniteMeasure.mass_nonzero_iff (ν n)).mp hn.ne'
    have hmassComplex :
        Tendsto (fun n => (((ν n).mass : ℝ) : ℂ)) atTop (𝓝 (((m : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (NNReal.continuous_coe.continuousAt.tendsto.comp hmass)
    have hnormChar (t : ℝ) :
        Tendsto (fun n => charFun ((ν n).normalize : Measure ℝ) t) atTop
          (𝓝 ((((m : ℝ) : ℂ)⁻¹) * φ t)) := by
      have hprod := (hmassComplex.inv₀ (by exact_mod_cast hm)).mul (hchar t)
      apply hprod.congr'
      filter_upwards [heventuallyNonzero] with n hn
      exact (charFun_finiteMeasure_normalize hn t).symm
    have htarget : ContinuousAt (fun t => ((((m : ℝ) : ℂ)⁻¹) * φ t)) 0 :=
      continuousAt_const.mul hφ
    obtain ⟨p, hpchar, hpnorm⟩ :=
      exists_probabilityMeasure_of_tendsto_charFun htarget hnormChar
    let ν₀ : FiniteMeasure ℝ := m • p.toFiniteMeasure
    have hν₀mass : ν₀.mass = m := by
      change (m • p.toFiniteMeasure) Set.univ = m
      rw [FiniteMeasure.smul_apply]
      simp
    have hν₀ne : ν₀ ≠ 0 :=
      (FiniteMeasure.mass_nonzero_iff ν₀).mp (hν₀mass.trans_ne hm)
    have hν₀normalize : ν₀.normalize = p := by
      apply ProbabilityMeasure.toMeasure_injective
      rw [ν₀.toMeasure_normalize_eq_of_nonzero hν₀ne]
      change (((ν₀.mass⁻¹ : NNReal) : ENNReal) • (ν₀ : Measure ℝ)) = (p : Measure ℝ)
      rw [hν₀mass]
      change (((m⁻¹ : NNReal) : ENNReal) •
        (((m : NNReal) : ENNReal) • (p : Measure ℝ))) = (p : Measure ℝ)
      rw [← smul_assoc]
      change ((((m⁻¹ : NNReal) : ENNReal) * ((m : NNReal) : ENNReal)) •
        (p : Measure ℝ)) = (p : Measure ℝ)
      rw [ENNReal.coe_inv hm]
      rw [ENNReal.inv_mul_cancel]
      · simp
      · exact_mod_cast hm
      · simp
    have hν₀char (t : ℝ) : charFun (ν₀ : Measure ℝ) t = φ t := by
      have hself := ν₀.self_eq_mass_smul_normalize
      rw [hν₀mass, hν₀normalize] at hself
      have hmeasure : (ν₀ : Measure ℝ) =
          (((m : NNReal) : ENNReal) • (p : Measure ℝ)) := by
        exact congrArg FiniteMeasure.toMeasure hself
      rw [hmeasure, charFun_apply_real, integral_smul_measure,
        ENNReal.coe_toReal, ← charFun_apply_real, hpchar]
      simp only [Complex.real_smul]
      have hmC : (((m : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hm
      field_simp
    refine ⟨ν₀, hν₀char, ?_⟩
    apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
    · simpa [hν₀normalize] using hpnorm
    · simpa [hν₀mass] using hmass

/-- Mass-free convenience form: convergence at frequency zero recovers the limiting total mass
automatically. -/
theorem exists_finiteMeasure_of_tendsto_charFun'
    {ν : ℕ → FiniteMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : ContinuousAt φ 0)
    (hchar : ∀ t, Tendsto (fun n => charFun (ν n : Measure ℝ) t) atTop (𝓝 (φ t))) :
    ∃ ν₀ : FiniteMeasure ℝ,
      (∀ t, charFun (ν₀ : Measure ℝ) t = φ t) ∧ Tendsto ν atTop (𝓝 ν₀) := by
  have hmassReal : Tendsto (fun n => ((ν n).mass : ℝ)) atTop (𝓝 (φ 0).re) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp (hchar 0)
    change Tendsto (fun n => (charFun (ν n : Measure ℝ) 0).re) atTop
      (𝓝 (φ 0).re) at hre
    convert hre using 1
    funext n
    rw [charFun_zero, Measure.real_def, ← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal]
    simp
  have hnonneg : 0 ≤ (φ 0).re :=
    ge_of_tendsto' hmassReal fun n => (ν n).mass.2
  let m : NNReal := ⟨(φ 0).re, hnonneg⟩
  have hmass : Tendsto (fun n => (ν n).mass) atTop (𝓝 m) := by
    apply NNReal.tendsto_coe.mp
    change Tendsto (fun n => ((ν n).mass : ℝ)) atTop (𝓝 (φ 0).re)
    exact hmassReal
  exact exists_finiteMeasure_of_tendsto_charFun hφ hmass hchar

end ProbabilityTheory
