/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Convergence

/-!
# Coalescent couplings for initial distributions

The finite-time coalescent path coupling is packaged as a Markov kernel on pairs of starting
states.  Its marginals are the corresponding powers of the original transition kernel.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

noncomputable section

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The time-`n` coupling kernel obtained from the independent coalescent path law. -/
noncomputable def coalescentCouplingKernelAt
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) : Kernel (E × E) (E × E) :=
  Kernel.ofFunOfCountable fun p =>
    pathCouplingAt (independentCoalescentPathLaw κ p.1 p.2) n

instance coalescentCouplingKernelAt.instIsMarkovKernel
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (coalescentCouplingKernelAt κ n) := by
  refine ⟨fun p => ?_⟩
  change IsProbabilityMeasure
    (pathCouplingAt (independentCoalescentPathLaw κ p.1 p.2) n)
  infer_instance

theorem coalescentCouplingKernelAt_map_fst
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    (coalescentCouplingKernelAt κ n).map Prod.fst =
      (κ ^ n).comap Prod.fst measurable_fst := by
  apply Kernel.ext
  intro p
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  have hc := isCoupling_pathCouplingAt
    (independentCoalescentPathLaw_isMarkovPathCoupling κ p.1 p.2) n
  change Measure.map Prod.fst
      (pathCouplingAt (independentCoalescentPathLaw κ p.1 p.2) n) = _
  rw [hc.fst, markovChainLaw_map_apply]

theorem coalescentCouplingKernelAt_map_snd
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    (coalescentCouplingKernelAt κ n).map Prod.snd =
      (κ ^ n).comap Prod.snd measurable_snd := by
  apply Kernel.ext
  intro p
  rw [Kernel.map_apply _ measurable_snd, Kernel.comap_apply]
  have hc := isCoupling_pathCouplingAt
    (independentCoalescentPathLaw_isMarkovPathCoupling κ p.1 p.2) n
  change Measure.map Prod.snd
      (pathCouplingAt (independentCoalescentPathLaw κ p.1 p.2) n) = _
  rw [hc.snd, markovChainLaw_map_apply]

/-- Mix the coalescent coupling over two initial distributions. -/
noncomputable def mixedCoalescentCouplingAt
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ ν : Measure E) (n : ℕ) : Measure (E × E) :=
  coalescentCouplingKernelAt κ n ∘ₘ (μ.prod ν)

instance mixedCoalescentCouplingAt.instIsProbabilityMeasure
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (mixedCoalescentCouplingAt κ μ ν n) := by
  unfold mixedCoalescentCouplingAt
  infer_instance

theorem mixedCoalescentCouplingAt_isCoupling
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    IsCoupling (mixedCoalescentCouplingAt κ μ ν n)
      (((κ ^ n : Kernel E E)) ∘ₘ μ) (((κ ^ n : Kernel E E)) ∘ₘ ν) := by
  constructor
  · rw [mixedCoalescentCouplingAt, Measure.map_comp,
      coalescentCouplingKernelAt_map_fst]
    rw [← Kernel.comp_deterministic_eq_comap (κ ^ n) measurable_fst,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
      Measure.map_fst_prod, measure_univ, one_smul]
    exact measurable_fst
  · rw [mixedCoalescentCouplingAt, Measure.map_comp,
      coalescentCouplingKernelAt_map_snd]
    rw [← Kernel.comp_deterministic_eq_comap (κ ^ n) measurable_snd,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
      Measure.map_snd_prod, measure_univ, one_smul]
    exact measurable_snd

theorem tendsto_coalescentCouplingKernelAt_mismatch_zero
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (p : E × E) :
    Tendsto (fun n => couplingMismatch (coalescentCouplingKernelAt κ n p))
      atTop (nhds 0) := by
  have hsuccess : IsSuccessfulPathCoupling
      (independentCoalescentPathLaw κ p.1 p.2) := by
    rw [successful_independentCoalescentPathLaw_iff_coalescenceTime_finite]
    simpa only [coalescenceTime_lt_top_iff] using
      independentCoalescent_pairPathHitsDiagonal_eq_one
        κ π hπ hirr haper p.1 p.2
  have hupper : Tendsto
      (fun n => independentCoalescentPathLaw κ p.1 p.2 (mismatchTail n))
      atTop (nhds 0) := by
    simpa only [IsSuccessfulPathCoupling, mismatchTail] using hsuccess
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) (fun n => by
      exact couplingMismatch_pathCouplingAt_le_tail
        (independentCoalescentPathLaw κ p.1 p.2) n)

end

end ProbabilityTheory
