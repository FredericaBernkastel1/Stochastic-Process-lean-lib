/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Martingale.Convergence

/-!
# Optional sampling for uniformly integrable martingales

This file separates deterministic boundedness from almost-sure finiteness.  Values at an
unbounded stopping time are obtained as almost-sure limits of the bounded truncations
`τ ∧ n`; no value assigned by `WithTop.untopA` on `{τ = ∞}` is used mathematically.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace Martingale

variable {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ}

private lemma ae_eq_of_two_tendsto_eLpNorm_one
    {u : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) μ) (ha : MemLp a 1 μ) (hb : MemLp b 1 μ)
    (hua : Tendsto (fun n => eLpNorm (u n - a) 1 μ) atTop (nhds 0))
    (hub : Tendsto (fun n => eLpNorm (u n - b) 1 μ) atTop (nhds 0)) :
    a =ᵐ[μ] b := by
  have hau : Tendsto (fun n => eLpNorm (a - u n) 1 μ) atTop (nhds 0) :=
    hua.congr' (Eventually.of_forall fun n => by
      rw [← eLpNorm_neg]
      congr 1
      ext ω
      simp)
  have hadd : Tendsto
      (fun n => eLpNorm (a - u n) 1 μ + eLpNorm (u n - b) 1 μ)
      atTop (nhds 0) := by
    simpa only [zero_add] using hau.add hub
  have hle : ∀ n, eLpNorm (a - b) 1 μ ≤
      eLpNorm (a - u n) 1 μ + eLpNorm (u n - b) 1 μ := by
    intro n
    calc
      eLpNorm (a - b) 1 μ = eLpNorm ((a - u n) + (u n - b)) 1 μ := by
        congr 1
        ext ω
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      _ ≤ eLpNorm (a - u n) 1 μ + eLpNorm (u n - b) 1 μ :=
        eLpNorm_add_le (ha.1.sub (hu n)) ((hu n).sub hb.1) le_rfl
  have hzero : eLpNorm (a - b) 1 μ = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hadd hle
    · exact zero_le
  rw [← sub_ae_eq_zero]
  exact (eLpNorm_eq_zero_iff (ha.1.sub hb.1) one_ne_zero).mp hzero

private lemma stoppedValue_min_const_tendsto
    {τ : Ω → WithTop ℕ} (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => stoppedValue f (fun ω => min (τ ω) (n : WithTop ℕ)) ω)
      atTop (nhds (stoppedValue f τ ω)) := by
  filter_upwards [hτ_finite] with ω hω
  lift τ ω to ℕ using hω with k hk
  refine tendsto_atTop_of_eventually_const (i₀ := k) ?_
  intro n hn
  simp only [stoppedValue]
  rw [← hk]
  have hkn : (k : WithTop ℕ) ≤ (n : WithTop ℕ) := by exact_mod_cast hn
  apply congrArg (fun j : ℕ => f j ω)
  exact congrArg WithTop.untopA (min_eq_left hkn)

/-- The values of a uniformly integrable martingale at an arbitrary family of almost-surely
finite stopping times are uniformly integrable.  This is Klenke Lemma 10.20 in a family form.

The stopping times may be unbounded and the index type need not be countable. -/
theorem uniformIntegrable_stoppedValue [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    {ι : Type*} (hf : Martingale f 𝓕 μ) (hUI : UniformIntegrable f 1 μ)
    {τ : ι → Ω → WithTop ℕ} (hτ : ∀ i, IsStoppingTime 𝓕 (τ i))
    (hτ_finite : ∀ i, ∀ᵐ ω ∂μ, τ i ω ≠ ⊤) :
    UniformIntegrable (fun i => stoppedValue f (τ i)) 1 μ := by
  let g : Ω → ℝ := 𝓕.limitProcess f μ
  obtain ⟨C, hC⟩ := hUI.2.2
  have hg : Integrable g μ :=
    (hf.submartingale.memLp_limitProcess hC).integrable le_rfl
  let ρ : ι × ℕ → Ω → WithTop ℕ :=
    fun z ω => min (τ z.1 ω) (z.2 : WithTop ℕ)
  have hρ : ∀ z, IsStoppingTime 𝓕 (ρ z) := fun z =>
    (hτ z.1).min_const z.2
  have hρ_le : ∀ z ω, ρ z ω ≤ (z.2 : WithTop ℕ) := fun z ω => min_le_right _ _
  have hbounded : ∀ z : ι × ℕ,
      stoppedValue f (ρ z) =ᵐ[μ] μ[g | (hρ z).measurableSpace] := by
    intro z
    have hstop := hf.stoppedValue_ae_eq_condExp_of_le_const
      (hρ z) (hρ_le z)
    have hfn := hf.ae_eq_condExp_limitProcess hUI z.2
    refine hstop.trans ((condExp_congr_ae hfn).trans ?_)
    exact condExp_condExp_of_le
      ((hρ z).measurableSpace_le_of_le_const (hρ_le z)) (𝓕.le z.2)
  have hcond : UniformIntegrable
      (fun z : ι × ℕ => μ[g | (hρ z).measurableSpace]) 1 μ :=
    hg.uniformIntegrable_condExp fun z => (hρ z).measurableSpace_le
  have hboundedUI : UniformIntegrable (fun z : ι × ℕ => stoppedValue f (ρ z)) 1 μ :=
    hcond.ae_eq fun z => (hbounded z).symm
  let L := {u : Ω → ℝ | ∃ s : ℕ → ι × ℕ,
    ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedValue f (ρ (s n)) ω) atTop (nhds (u ω))}
  have hlimits : UniformIntegrable (fun u : L => u.1) 1 μ := by
    simpa only [L] using hboundedUI.uniformIntegrable_of_ae_tendsto atTop
  let e : ι → L := fun i => ⟨stoppedValue f (τ i),
    ⟨fun n => (i, n), by
      simpa only [ρ] using stoppedValue_min_const_tendsto (f := f) (hτ_finite i)⟩⟩
  refine ⟨fun i => hlimits.1 (e i), ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hlimits.2.1 hε
    exact ⟨δ, hδ, fun i => hbound (e i)⟩
  · obtain ⟨C, hC⟩ := hlimits.2.2
    exact ⟨C, fun i => hC (e i)⟩

/-- A UI martingale evaluated at an almost-surely finite stopping time is integrable. -/
theorem integrable_stoppedValue_of_uniformIntegrable
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hf : Martingale f 𝓕 μ) (hUI : UniformIntegrable f 1 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝓕 τ)
    (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue f τ) μ := by
  have h := hf.uniformIntegrable_stoppedValue hUI
    (ι := Unit) (τ := fun _ => τ) (fun _ => hτ) (fun _ => hτ_finite)
  exact memLp_one_iff_integrable.mp (h.memLp ())

/-- Optional sampling for UI martingales at almost-surely finite, not necessarily bounded,
stopping times.  This is the unbounded layer of Klenke Theorem 10.21.

The hypotheses `σ ≤ τ` and almost-sure finiteness are used before passing from the bounded
identities for `τ ∧ n` to the limit. -/
theorem stoppedValue_ae_eq_condExp_of_ae_finite
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hf : Martingale f 𝓕 μ) (hUI : UniformIntegrable f 1 μ)
    {σ τ : Ω → WithTop ℕ} (hσ : IsStoppingTime 𝓕 σ)
    (hτ : IsStoppingTime 𝓕 τ) (hστ : σ ≤ τ)
    (hσ_finite : ∀ᵐ ω ∂μ, σ ω ≠ ⊤) (hτ_finite : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ | hσ.measurableSpace] := by
  let τn : ℕ → Ω → WithTop ℕ :=
    fun n ω => min (τ ω) (n : WithTop ℕ)
  let ρ : ℕ → Ω → WithTop ℕ :=
    fun n ω => min (σ ω) (τn n ω)
  have hτn : ∀ n, IsStoppingTime 𝓕 (τn n) := fun n => hτ.min_const n
  have hρ : ∀ n, IsStoppingTime 𝓕 (ρ n) := fun n => hσ.min (hτn n)
  have hτn_le : ∀ n ω, τn n ω ≤ (n : WithTop ℕ) :=
    fun n ω => min_le_right _ _
  have hτn_finite : ∀ n, ∀ᵐ ω ∂μ, τn n ω ≠ ⊤ := fun n =>
    ae_of_all μ fun ω htop => by simpa [htop] using hτn_le n ω
  have hρ_finite : ∀ n, ∀ᵐ ω ∂μ, ρ n ω ≠ ⊤ := fun n =>
    ae_of_all μ fun ω htop => by
      have hle : ρ n ω ≤ (n : WithTop ℕ) :=
        (min_le_right _ _).trans (hτn_le n ω)
      simp [htop] at hle
  have hτnUI : UniformIntegrable (fun n => stoppedValue f (τn n)) 1 μ :=
    hf.uniformIntegrable_stoppedValue hUI hτn hτn_finite
  have hρUI : UniformIntegrable (fun n => stoppedValue f (ρ n)) 1 μ :=
    hf.uniformIntegrable_stoppedValue hUI hρ hρ_finite
  have hτ_int := hf.integrable_stoppedValue_of_uniformIntegrable hUI hτ hτ_finite
  have hσ_int := hf.integrable_stoppedValue_of_uniformIntegrable hUI hσ hσ_finite
  have hτ_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedValue f (τn n) ω)
      atTop (nhds (stoppedValue f τ ω)) := by
    simpa only [τn] using stoppedValue_min_const_tendsto (f := f) hτ_finite
  have hρ_eq : ∀ n, ρ n = fun ω => min (σ ω) (n : WithTop ℕ) := by
    intro n
    funext ω
    simp only [ρ, τn]
    rw [← min_assoc, min_eq_left (hστ ω)]
  have hρ_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedValue f (ρ n) ω)
      atTop (nhds (stoppedValue f σ ω)) := by
    simpa only [hρ_eq] using stoppedValue_min_const_tendsto (f := f) hσ_finite
  have hτ_L1 : Tendsto
      (fun n => eLpNorm (stoppedValue f (τn n) - stoppedValue f τ) 1 μ)
      atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hτnUI.1
      (memLp_one_iff_integrable.2 hτ_int) hτnUI.2.1 hτ_ae
  have hρ_L1 : Tendsto
      (fun n => eLpNorm (stoppedValue f (ρ n) - stoppedValue f σ) 1 μ)
      atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hρUI.1
      (memLp_one_iff_integrable.2 hσ_int) hρUI.2.1 hρ_ae
  have hbounded : ∀ n, stoppedValue f (ρ n) =ᵐ[μ]
      μ[stoppedValue f (τn n) | hσ.measurableSpace] := by
    intro n
    exact hf.stoppedValue_min_ae_eq_condExp (hτn n) hσ (hτn_le n)
  have hcond_le : ∀ n,
      eLpNorm
          (μ[stoppedValue f (τn n) | hσ.measurableSpace] -
            μ[stoppedValue f τ | hσ.measurableSpace]) 1 μ ≤
        eLpNorm (stoppedValue f (τn n) - stoppedValue f τ) 1 μ := by
    intro n
    calc
      eLpNorm
          (μ[stoppedValue f (τn n) | hσ.measurableSpace] -
            μ[stoppedValue f τ | hσ.measurableSpace]) 1 μ =
          eLpNorm (μ[stoppedValue f (τn n) - stoppedValue f τ |
            hσ.measurableSpace]) 1 μ := by
              apply eLpNorm_congr_ae
              exact (condExp_sub
                (memLp_one_iff_integrable.mp (hτnUI.memLp n)) hτ_int _).symm
      _ ≤ eLpNorm (stoppedValue f (τn n) - stoppedValue f τ) 1 μ :=
        eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hcond_L1 : Tendsto
      (fun n => eLpNorm
        (μ[stoppedValue f (τn n) | hσ.measurableSpace] -
          μ[stoppedValue f τ | hσ.measurableSpace]) 1 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hτ_L1
      (fun _ => zero_le) hcond_le
  have hρ_cond_L1 : Tendsto
      (fun n => eLpNorm
        (stoppedValue f (ρ n) - μ[stoppedValue f τ | hσ.measurableSpace]) 1 μ)
      atTop (nhds 0) := by
    apply hcond_L1.congr'
    filter_upwards [] with n
    exact eLpNorm_congr_ae (((hbounded n).sub Filter.EventuallyEq.rfl).symm)
  exact ae_eq_of_two_tendsto_eLpNorm_one hρUI.1
    (memLp_one_iff_integrable.2 hσ_int) (memLp_one_iff_integrable.2 integrable_condExp)
    hρ_L1 hρ_cond_L1

end Martingale

end MeasureTheory
