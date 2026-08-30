/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Martingale.Adapters
public import StochLean.Probability.Martingale.DiscreteIntegral
public import StochLean.Probability.Martingale.Convergence.QuadraticVariation
public import StochLean.Probability.Martingale.Inequalities.DoobLp
public import StochLean.Probability.Martingale.OptionalSampling.UniformIntegrable
public import StochLean.Probability.Martingale.Representation.Binary

/-!
# Semantic regressions for discrete martingale calculus

The examples in this file deliberately exercise the public theorem boundaries.  In particular,
predictability uses the `n+1`/`n` convention, the named integral has the expected recursion,
stopping accepts a genuinely `WithTop`-valued time, and the sharp Doob layer retains `1 < p`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory

/- Predictability exposes exactly the next-integrand/current-information convention. -/
example {Ω E : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
    {𝓕 : Filtration ℕ mΩ} {H : ℕ → Ω → E} :
    IsStronglyPredictable 𝓕 H ↔ StronglyMeasurable[𝓕 0] (H 0) ∧
      ∀ n, StronglyMeasurable[𝓕 n] (H (n + 1)) :=
  IsStronglyPredictable.iff_measurable_add_one

/- The named integral is zero initially and has Klenke's one-step increment. -/
example {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (H : ℕ → Ω → ℝ) (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral H X 0 = 0 ∧
      discreteStochasticIntegral H X (n + 1) =
        discreteStochasticIntegral H X n + H (n + 1) • (X (n + 1) - X n) :=
  ⟨discreteStochasticIntegral_zero H X, discreteStochasticIntegral_succ H X n⟩

/- The constant-one transform is the increment from the true initial value, not a totalized
replacement for it. -/
example {Ω E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : ℕ → Ω → E) (n : ℕ) :
    discreteStochasticIntegral (fun _ _ => (1 : ℝ)) X n = X n - X 0 :=
  discreteStochasticIntegral_one X n

/- Stopped bracket compatibility permits an infinite stopping time; it never evaluates `M_∞`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {τ : Ω → ℕ∞}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hMtwo : ∀ n, MemLp (M n) 2 μ)
    (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    predictableQuadraticVariation (stoppedProcess M τ) 𝓕 μ n =ᵐ[μ]
      stoppedProcess (predictableQuadraticVariation M 𝓕 μ) τ n :=
  hM.predictableQuadraticVariation_stoppedProcess_ae_eq hMtwo hτ n

/- The public sharp Doob maximal inequality cannot be called at `p = 1`: positivity is explicit
in its signature and the standard conjugate constant is retained. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} [IsFiniteMeasure μ]
    (hf : Martingale f 𝓕 μ) (p : ℝ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖f k ω‖)) (.ofReal p) μ ≤
      ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (.ofReal p) μ :=
  hf.eLpNorm_norm_runMax_le hp n

/- Klenke 11.14 uses the predictable bracket and concludes pathwise convergence on the event
where that bracket stays finite; it is not a disguised uniform deterministic bound. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {M : ℕ → Ω → ℝ} {𝒜 : Filtration ℕ mΩ}
    [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ 𝒜]
    (hM : Martingale M 𝒜 μ) (hMtwo : ∀ n, MemLp (M n) 2 μ)
    (hfinite : ∀ᵐ ω ∂μ, ∃ C : ℝ, ∀ n,
      predictableQuadraticVariation M 𝒜 μ n ω ≤ C) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n ↦ M n ω) atTop (nhds c) :=
  hM.ae_tendsto_of_predictableQuadraticVariation_bdd hMtwo hfinite

/- Binary representation consumes structural splitting data; it is not an unrestricted theorem
for arbitrary multi-valued information increments. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hbin : BinarySplittingData M 𝓕) :
    IsStronglyPredictable 𝓕 hbin.coefficient ∧
      ∀ n, M n = M 0 + discreteStochasticIntegral hbin.coefficient hbin.innovation n :=
  ⟨hbin.coefficient_isStronglyPredictable, hbin.representation⟩

end MeasureTheory
