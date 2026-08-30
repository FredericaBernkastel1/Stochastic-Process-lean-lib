/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.InitialCoupling
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Total-variation convergence to equilibrium

Coalescent couplings are mixed over arbitrary initial distributions.  Dominated convergence turns
pointwise coalescence into convergence of the mixed mismatch probability.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

noncomputable section

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem mixedCoalescentCouplingAt_mismatch_apply
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ π : Measure E) (n : ℕ) :
    couplingMismatch (mixedCoalescentCouplingAt κ μ π n) =
      ∫⁻ p, couplingMismatch (coalescentCouplingKernelAt κ n p) ∂(μ.prod π) := by
  change (coalescentCouplingKernelAt κ n ∘ₘ (μ.prod π))
      {z : E × E | z.1 ≠ z.2} = _
  have hneq : MeasurableSet {z : E × E | z.1 ≠ z.2} := by
    simpa only [Set.compl_ofPred] using measurableSet_pairDiagonal.compl
  rw [Measure.bind_apply hneq (coalescentCouplingKernelAt κ n).aemeasurable]
  rfl

theorem tendsto_mixedCoalescentCouplingAt_mismatch_zero
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ π : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) :
    Tendsto (fun n => couplingMismatch (mixedCoalescentCouplingAt κ μ π n))
      atTop (nhds 0) := by
  let ρ := μ.prod π
  let F : ℕ → E × E → ℝ≥0∞ := fun n p =>
    couplingMismatch (coalescentCouplingKernelAt κ n p)
  have hmeas : ∀ n, Measurable (F n) := fun _ => measurable_of_countable _
  have hbound : ∀ n, ∀ᵐ p ∂ρ, F n p ≤ (1 : ℝ≥0∞) := fun n =>
    Filter.Eventually.of_forall fun p => by
      change (coalescentCouplingKernelAt κ n p) {z | z.1 ≠ z.2} ≤ 1
      exact prob_le_one
  have hfin : (∫⁻ _p, (1 : ℝ≥0∞) ∂ρ) ≠ ∞ := by simp [ρ]
  have hlim : ∀ᵐ p ∂ρ, Tendsto (fun n => F n p) atTop (nhds 0) :=
    Filter.Eventually.of_forall fun p =>
      tendsto_coalescentCouplingKernelAt_mismatch_zero κ π hπ hirr haper p
  have hdct := tendsto_lintegral_filter_of_dominated_convergence
    (μ := ρ) (fun _ => (1 : ℝ≥0∞))
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall hbound) hfin hlim
  have hzero : (∫⁻ _p, (0 : ℝ≥0∞) ∂ρ) = 0 := by simp
  rw [hzero] at hdct
  dsimp only [F, ρ] at hdct
  exact hdct.congr' (Filter.Eventually.of_forall fun n =>
    (mixedCoalescentCouplingAt_mismatch_apply κ μ π n).symm)

/-- Klenke's convergence-to-equilibrium implication for every initial probability measure. -/
theorem Kernel.fullTotalVariationDistance_comp_pow_tendsto_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ π : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) :
    Tendsto
      (fun n => fullTotalVariationDistance (((κ ^ n : Kernel E E)) ∘ₘ μ) π)
      atTop (nhds 0) := by
  have hbound (n : ℕ) :
      fullTotalVariationDistance (((κ ^ n : Kernel E E)) ∘ₘ μ) π ≤
        2 * couplingMismatch (mixedCoalescentCouplingAt κ μ π n) := by
    calc
      fullTotalVariationDistance (((κ ^ n : Kernel E E)) ∘ₘ μ) π =
          fullTotalVariationDistance (((κ ^ n : Kernel E E)) ∘ₘ μ)
            (((κ ^ n : Kernel E E)) ∘ₘ π) := by rw [(hπ.pow n).def]
      _ ≤ 2 * couplingMismatch (mixedCoalescentCouplingAt κ μ π n) :=
        (mixedCoalescentCouplingAt_isCoupling κ μ π n).fullTotalVariationDistance_le_two_mul_mismatch
  have hupper : Tendsto
      (fun n => 2 * couplingMismatch (mixedCoalescentCouplingAt κ μ π n))
      atTop (nhds 0) := by
    have h := tendsto_mixedCoalescentCouplingAt_mismatch_zero
      κ μ π hπ hirr haper
    simpa only [two_mul, zero_add] using h.add h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound

/-- Point-mass specialization of convergence to the invariant probability. -/
theorem Kernel.fullTotalVariationDistance_pow_tendsto_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (x : E) :
    Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π)
      atTop (nhds 0) := by
  have h := κ.fullTotalVariationDistance_comp_pow_tendsto_invariantProbability
    (Measure.dirac x) π hπ hirr haper
  have hdirac (n : ℕ) : (κ ^ n : Kernel E E) ∘ₘ Measure.dirac x = (κ ^ n) x := by
    exact Measure.dirac_bind (κ ^ n).measurable x
  simpa only [hdirac] using h

/-- If the `n`-step return mass vanishes, the invariant singleton mass is a lower bound for
Klenke's full total-variation distance. -/
theorem Kernel.invariantSingleton_le_fullTotalVariationDistance_of_pow_apply_eq_zero
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π] (x : E) (n : ℕ)
    (hz : (κ ^ n) x {x} = 0) :
    π {x} ≤ fullTotalVariationDistance ((κ ^ n) x) π := by
  have hfinite : π {x} ≠ ∞ := measure_ne_top π {x}
  calc
    π {x} = ENNReal.ofReal |((κ ^ n) x).real {x} - π.real {x}| := by
      simp only [Measure.real, hz, ENNReal.toReal_zero, zero_sub, abs_neg,
        abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite]
    _ ≤ eventTotalVariationDistance ((κ ^ n) x) π :=
      eventDistance_le_eventTotalVariationDistance _ _ (MeasurableSet.singleton x)
    _ ≤ fullTotalVariationDistance ((κ ^ n) x) π :=
      eventTotalVariationDistance_le_fullTotalVariationDistance _ _

/-- Total-variation convergence to a full-support invariant probability forces every sufficiently
large time to be a positive return time. -/
theorem Kernel.eventually_transitionTimes_self_of_tendsto_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (x : E)
    (hconv : Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop, n ∈ κ.transitionTimes x x := by
  have hπx : 0 < π {x} := invariantProbability_singleton_pos hπ hirr x
  have hsmall : ∀ᶠ n in atTop,
      fullTotalVariationDistance ((κ ^ n) x) π < π {x} :=
    (tendsto_order.1 hconv).2 _ hπx
  filter_upwards [hsmall] with n hn
  rw [Kernel.transitionTimes, Set.mem_ofPred_eq]
  by_contra hnot
  have hz : (κ ^ n) x {x} = 0 := bot_unique (not_lt.mp hnot)
  exact (not_lt_of_ge
    (κ.invariantSingleton_le_fullTotalVariationDistance_of_pow_apply_eq_zero π x n hz)) hn

/-- The converse direction in Klenke's Theorem 18.13: convergence from one state implies that
state has period one. -/
theorem Kernel.aperiodicAt_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (x : E)
    (hconv : Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π)
      atTop (nhds 0)) :
    κ.AperiodicAt x := by
  have hev := κ.eventually_transitionTimes_self_of_tendsto_invariantProbability
    π hπ hirr x hconv
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hdN : κ.period x ∣ N := Nat.setGcd_dvd_of_mem (hN N le_rfl)
  have hdN1 : κ.period x ∣ N + 1 :=
    Nat.setGcd_dvd_of_mem (hN (N + 1) (Nat.le_succ N))
  have hd1 : κ.period x ∣ 1 := (Nat.dvd_add_iff_right hdN).2 (by
    simpa only [add_comm] using hdN1)
  exact Nat.eq_one_of_dvd_one hd1

/-- In an irreducible chain, convergence from one state implies global aperiodicity. -/
theorem Kernel.isAperiodic_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (x : E)
    (hconv : Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π)
      atTop (nhds 0)) :
    κ.IsAperiodic := by
  have hx := κ.aperiodicAt_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
    π hπ hirr x hconv
  rw [Kernel.isIrreducible_count_iff_forall_canReach] at hirr
  intro y
  unfold Kernel.AperiodicAt at hx ⊢
  rw [← κ.period_eq_of_communicates (hirr x y) (hirr y x)]
  exact hx

/-- Total-variation convergence to `π` from every point mass. -/
def Kernel.TVConvergesFromEveryState (κ : Kernel E E) (π : Measure E) : Prop :=
  ∀ x, Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π) atTop (nhds 0)

/-- Total-variation convergence to `π` from at least one point mass. -/
def Kernel.TVConvergesFromSomeState (κ : Kernel E E) (π : Measure E) : Prop :=
  ∃ x, Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) π) atTop (nhds 0)

/-- Total-variation convergence to `π` after evolving every initial probability measure. -/
def Kernel.TVConvergesFromEveryInitialProbability
    (κ : Kernel E E) (π : Measure E) : Prop :=
  ∀ (μ : Measure E), IsProbabilityMeasure μ →
    Tendsto (fun n => fullTotalVariationDistance (((κ ^ n : Kernel E E)) ∘ₘ μ) π)
      atTop (nhds 0)

/-- Aperiodicity is equivalent to total-variation convergence from every state. -/
theorem Kernel.isAperiodic_iff_TVConvergesFromEveryState
    [Nonempty E] (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    κ.IsAperiodic ↔ κ.TVConvergesFromEveryState π := by
  constructor
  · intro haper x
    exact κ.fullTotalVariationDistance_pow_tendsto_invariantProbability
      π hπ hirr haper x
  · intro hall
    exact κ.isAperiodic_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
      π hπ hirr (Classical.choice inferInstance) (hall _)

/-- Aperiodicity is equivalent to total-variation convergence from some state. -/
theorem Kernel.isAperiodic_iff_TVConvergesFromSomeState
    [Nonempty E] (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    κ.IsAperiodic ↔ κ.TVConvergesFromSomeState π := by
  constructor
  · intro haper
    exact ⟨Classical.choice inferInstance,
      κ.fullTotalVariationDistance_pow_tendsto_invariantProbability
        π hπ hirr haper (Classical.choice inferInstance)⟩
  · rintro ⟨x, hx⟩
    exact κ.isAperiodic_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
      π hπ hirr x hx

/-- Aperiodicity is equivalent to convergence after evolving every initial probability. -/
theorem Kernel.isAperiodic_iff_TVConvergesFromEveryInitialProbability
    [Nonempty E] (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    κ.IsAperiodic ↔ κ.TVConvergesFromEveryInitialProbability π := by
  constructor
  · intro haper μ hμ
    letI : IsProbabilityMeasure μ := hμ
    exact κ.fullTotalVariationDistance_comp_pow_tendsto_invariantProbability
      μ π hπ hirr haper
  · intro hall
    let x : E := Classical.choice inferInstance
    have h := hall (Measure.dirac x) inferInstance
    have hdirac (n : ℕ) : (κ ^ n : Kernel E E) ∘ₘ Measure.dirac x = (κ ^ n) x := by
      exact Measure.dirac_bind (κ ^ n).measurable x
    apply κ.isAperiodic_of_fullTotalVariationDistance_pow_tendsto_invariantProbability
      π hπ hirr x
    simpa only [hdirac] using h

/-- Klenke's Theorem 18.13, retaining all four equivalent formulations. -/
theorem Kernel.klenke_18_13
    [Nonempty E] (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    (κ.IsAperiodic ↔ κ.TVConvergesFromEveryState π) ∧
    (κ.TVConvergesFromEveryState π ↔ κ.TVConvergesFromSomeState π) ∧
    (κ.TVConvergesFromSomeState π ↔ κ.TVConvergesFromEveryInitialProbability π) := by
  have hevery := κ.isAperiodic_iff_TVConvergesFromEveryState π hπ hirr
  have hsome := κ.isAperiodic_iff_TVConvergesFromSomeState π hπ hirr
  have hinitial := κ.isAperiodic_iff_TVConvergesFromEveryInitialProbability π hπ hirr
  exact ⟨hevery, hevery.symm.trans hsome, hsome.symm.trans hinitial⟩

end

end ProbabilityTheory
