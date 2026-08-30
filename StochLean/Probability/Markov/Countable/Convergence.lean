/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Coupling.TotalVariation
public import StochLean.Probability.Markov.Countable.Klenke

/-!
# Successful path couplings and total-variation convergence

The result is first stated for the actual one-time marginals of the coupled path laws.  It therefore
does not hide a transition-marginal premise; the canonical-chain specialization only needs the
separate Ionescu--Tulcea marginal bridge.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Paths that disagree at some time at or after `n`. -/
def mismatchTail (n : ℕ) : Set ((ℕ → E) × (ℕ → E)) :=
  {p | ∃ k ≥ n, p.1 k ≠ p.2 k}

theorem measurableSet_mismatchTail (n : ℕ) : MeasurableSet (mismatchTail (E := E) n) := by
  have hrepr : mismatchTail (E := E) n =
      ⋃ k : ℕ, ⋃ (_ : n ≤ k), {p | p.1 k ≠ p.2 k} := by
    ext p
    simp [mismatchTail]
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro _
  have hp : Measurable (fun p : (ℕ → E) × (ℕ → E) => (p.1 k, p.2 k)) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)
  have hneq : MeasurableSet {p : E × E | p.1 ≠ p.2} := by
    simpa only [Set.compl_ofPred] using measurableSet_pairDiagonal.compl
  exact hp hneq

theorem measurableSet_eventuallyEqualPaths :
    MeasurableSet
      {p : (ℕ → E) × (ℕ → E) | ∃ n, ∀ k ≥ n, p.1 k = p.2 k} := by
  have hrepr :
      {p : (ℕ → E) × (ℕ → E) | ∃ n, ∀ k ≥ n, p.1 k = p.2 k} =
        (⋂ n, mismatchTail (E := E) n)ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, mismatchTail]
    push Not
    rfl
  rw [hrepr]
  exact (MeasurableSet.iInter (measurableSet_mismatchTail (E := E))).compl

theorem antitone_mismatchTail : Antitone (mismatchTail (E := E)) := by
  intro m n hmn p hp
  obtain ⟨k, hnk, hk⟩ := hp
  exact ⟨k, hmn.trans hnk, hk⟩

/-- On a probability path space, the tail-probability criterion is equivalent to almost-sure
eventual equality. -/
theorem successfulPathCoupling_iff_eventuallyEqualAE
    (γ : Measure ((ℕ → E) × (ℕ → E))) [IsProbabilityMeasure γ] :
    IsSuccessfulPathCoupling γ ↔ EventuallyEqualAE γ := by
  have hsets : (⋂ n, mismatchTail (E := E) n) =
      {p | ¬ ∃ n, ∀ k ≥ n, p.1 k = p.2 k} := by
    ext p
    simp only [Set.mem_iInter, mismatchTail, Set.mem_ofPred_eq]
    push Not
    rfl
  have hcont : Tendsto (γ ∘ mismatchTail (E := E)) atTop
      (𝓝 (γ (⋂ n, mismatchTail (E := E) n))) := by
    exact tendsto_measure_iInter_atTop
      (μ := γ) (fun n => (measurableSet_mismatchTail (E := E) n).nullMeasurableSet)
      antitone_mismatchTail ⟨0, by finiteness⟩
  constructor
  · intro hsuccess
    rw [EventuallyEqualAE, ae_iff]
    rw [← hsets]
    have hs : Tendsto (γ ∘ mismatchTail (E := E)) atTop (𝓝 0) := by
      simpa only [IsSuccessfulPathCoupling, mismatchTail, Function.comp_def] using hsuccess
    exact tendsto_nhds_unique hcont hs
  · intro heventual
    have hzero : γ (⋂ n, mismatchTail (E := E) n) = 0 := by
      rw [hsets]
      exact ae_iff.mp heventual
    rw [hzero] at hcont
    simpa only [IsSuccessfulPathCoupling, mismatchTail, Function.comp_def] using hcont

/-- For the semantic independent coalescent, Klenke's successful-coupling criterion is exactly
almost-sure finiteness of the ordinary time-zero hitting time of the diagonal. -/
theorem successful_independentCoalescentPathLaw_iff_coalescenceTime_finite
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    IsSuccessfulPathCoupling (independentCoalescentPathLaw κ x y) ↔
      markovChainLaw (independentCoalescentKernel κ) (x, y)
        {z | coalescenceTime z < (⊤ : WithTop ℕ)} = 1 := by
  rw [successfulPathCoupling_iff_eventuallyEqualAE]
  rw [EventuallyEqualAE, independentCoalescentPathLaw]
  rw [ae_map_iff measurable_splitPairPath.aemeasurable
    measurableSet_eventuallyEqualPaths]
  change (∀ᵐ z ∂markovChainLaw (independentCoalescentKernel κ) (x, y),
      PairPathEventuallyDiagonal z) ↔ _
  have habs := independentCoalescent_eventuallyDiagonal_iff_hits_ae κ x y
  have hae :
      (∀ᵐ z ∂markovChainLaw (independentCoalescentKernel κ) (x, y),
          PairPathEventuallyDiagonal z) ↔
        ∀ᵐ z ∂markovChainLaw (independentCoalescentKernel κ) (x, y),
          PairPathHitsDiagonal z := by
    constructor
    · intro h
      filter_upwards [h, habs] with z hz hiff
      exact hiff.mp hz
    · intro h
      filter_upwards [h, habs] with z hz hiff
      exact hiff.mpr hz
  rw [hae]
  rw [ae_iff_measure_eq measurableSet_pairPathHitsDiagonal.nullMeasurableSet,
    measure_univ]
  have hset : {z : ℕ → E × E | PairPathHitsDiagonal z} =
      {z | coalescenceTime z < (⊤ : WithTop ℕ)} := by
    ext z
    exact (coalescenceTime_lt_top_iff z).symm
  rw [hset]

/-- Push a path coupling forward to the pair of coordinates at time `n`. -/
noncomputable def pathCouplingAt (γ : Measure ((ℕ → E) × (ℕ → E))) (n : ℕ) :
    Measure (E × E) :=
  Measure.map (fun p => (p.1 n, p.2 n)) γ

/-- The coordinate pushforward is a coupling of the two one-time marginal laws. -/
theorem isCoupling_pathCouplingAt
    {γ : Measure ((ℕ → E) × (ℕ → E))} {μ ν : Measure (ℕ → E)}
    (hγ : IsCoupling γ μ ν) (n : ℕ) :
    IsCoupling (pathCouplingAt γ n)
      (Measure.map (fun z : ℕ → E => z n) μ)
      (Measure.map (fun z : ℕ → E => z n) ν) := by
  have hpair : Measurable (fun p : (ℕ → E) × (ℕ → E) => (p.1 n, p.2 n)) :=
    (measurable_pi_apply n).comp measurable_fst |>.prodMk
      ((measurable_pi_apply n).comp measurable_snd)
  constructor
  · rw [pathCouplingAt, Measure.map_map measurable_fst hpair]
    change Measure.map ((fun z : ℕ → E => z n) ∘ Prod.fst) γ = _
    rw [← Measure.map_map (measurable_pi_apply n) measurable_fst, hγ.fst]
  · rw [pathCouplingAt, Measure.map_map measurable_snd hpair]
    change Measure.map ((fun z : ℕ → E => z n) ∘ Prod.snd) γ = _
    rw [← Measure.map_map (measurable_pi_apply n) measurable_snd, hγ.snd]

instance pathCouplingAt.instIsProbabilityMeasure
    (γ : Measure ((ℕ → E) × (ℕ → E))) [IsProbabilityMeasure γ] (n : ℕ) :
    IsProbabilityMeasure (pathCouplingAt γ n) := by
  unfold pathCouplingAt
  exact Measure.isProbabilityMeasure_map
    (((measurable_pi_apply n).comp measurable_fst).prodMk
      ((measurable_pi_apply n).comp measurable_snd)).aemeasurable

/-- A coordinate mismatch is contained in the successful-coupling tail event beginning there. -/
theorem couplingMismatch_pathCouplingAt_le_tail
    (γ : Measure ((ℕ → E) × (ℕ → E))) (n : ℕ) :
    couplingMismatch (pathCouplingAt γ n) ≤ γ (mismatchTail (E := E) n) := by
  have hpair : Measurable (fun p : (ℕ → E) × (ℕ → E) => (p.1 n, p.2 n)) :=
    (measurable_pi_apply n).comp measurable_fst |>.prodMk
      ((measurable_pi_apply n).comp measurable_snd)
  have hneq : MeasurableSet {p : E × E | p.1 ≠ p.2} := by
    simpa only [Set.compl_ofPred] using measurableSet_pairDiagonal.compl
  rw [couplingMismatch, pathCouplingAt, Measure.map_apply hpair hneq]
  apply measure_mono
  intro p hp
  exact ⟨n, le_rfl, hp⟩

/-- A successful coupling forces full total variation of its one-time marginals to zero.  The
factor `2` is the corrected full-TV normalization. -/
theorem fullTotalVariationDistance_pathMarginals_tendsto_zero
    {γ : Measure ((ℕ → E) × (ℕ → E))} [IsProbabilityMeasure γ]
    {μ ν : Measure (ℕ → E)} (hγ : IsCoupling γ μ ν)
    (hsuccess : IsSuccessfulPathCoupling γ) :
    Tendsto
      (fun n => fullTotalVariationDistance
        (Measure.map (fun z : ℕ → E => z n) μ)
        (Measure.map (fun z : ℕ → E => z n) ν))
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      fullTotalVariationDistance
          (Measure.map (fun z : ℕ → E => z n) μ)
          (Measure.map (fun z : ℕ → E => z n) ν) ≤
        2 * γ (mismatchTail (E := E) n) := by
    exact ((isCoupling_pathCouplingAt hγ n).fullTotalVariationDistance_le_two_mul_mismatch).trans
      (by gcongr; exact couplingMismatch_pathCouplingAt_le_tail γ n)
  have hupper : Tendsto (fun n => 2 * γ (mismatchTail (E := E) n)) atTop (𝓝 0) := by
    simpa only [IsSuccessfulPathCoupling, mismatchTail, two_mul, zero_add] using
      hsuccess.add hsuccess
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound

/-- Canonical-chain specialization: a successful path coupling forces the transition powers from
its two starting states to converge in full total variation. -/
theorem fullTotalVariationDistance_kernelPowers_tendsto_zero
    {κ : Kernel E E} [IsMarkovKernel κ] {x y : E}
    {γ : Measure ((ℕ → E) × (ℕ → E))} [IsProbabilityMeasure γ]
    (hγ : IsMarkovPathCoupling κ x y γ)
    (hsuccess : IsSuccessfulPathCoupling γ) :
    Tendsto
      (fun n => fullTotalVariationDistance ((κ ^ n) x) ((κ ^ n) y))
      atTop (nhds 0) := by
  have h := fullTotalVariationDistance_pathMarginals_tendsto_zero
    (E := E) hγ hsuccess
  simpa only [markovChainLaw_map_apply] using h

/-- Existential pair-level form of the successful-coupling convergence theorem. -/
theorem HasSuccessfulCouplingFrom.tendsto_fullTotalVariationDistance_kernelPowers
    {κ : Kernel E E} [IsMarkovKernel κ] {x y : E}
    (h : HasSuccessfulCouplingFrom κ x y) :
    Tendsto
      (fun n => fullTotalVariationDistance ((κ ^ n) x) ((κ ^ n) y))
      atTop (nhds 0) := by
  obtain ⟨γ, hγ, hsuccess⟩ := h
  letI : IsProbabilityMeasure γ := ⟨hγ.measure_univ⟩
  exact fullTotalVariationDistance_kernelPowers_tendsto_zero hγ hsuccess

/-- Global successful coupling gives pairwise full-total-variation convergence of all transition
rows. -/
theorem HasSuccessfulCouplings.tendsto_fullTotalVariationDistance_kernelPowers
    {κ : Kernel E E} [IsMarkovKernel κ] (h : HasSuccessfulCouplings κ) (x y : E) :
    Tendsto
      (fun n => fullTotalVariationDistance ((κ ^ n) x) ((κ ^ n) y))
      atTop (nhds 0) :=
  (h x y).tendsto_fullTotalVariationDistance_kernelPowers

/-- Klenke's successful coupling theorem for irreducible aperiodic chains carrying an invariant
probability measure. -/
theorem Kernel.hasSuccessfulCouplings_of_irreducible_aperiodic_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) :
    HasSuccessfulCouplings κ := by
  intro x y
  refine ⟨independentCoalescentPathLaw κ x y,
    independentCoalescentPathLaw_isMarkovPathCoupling κ x y, ?_⟩
  rw [successful_independentCoalescentPathLaw_iff_coalescenceTime_finite]
  simpa only [coalescenceTime_lt_top_iff] using
    independentCoalescent_pairPathHitsDiagonal_eq_one κ π hπ hirr haper x y

/-- Klenke's coupling theorem: transition rows converge in full total variation. -/
theorem Kernel.fullTotalVariationDistance_pow_tendsto_zero_of_irreducible_aperiodic_invariantProbability
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (x y : E) :
    Tendsto (fun n => fullTotalVariationDistance ((κ ^ n) x) ((κ ^ n) y))
      atTop (nhds 0) :=
  (κ.hasSuccessfulCouplings_of_irreducible_aperiodic_invariantProbability
    π hπ hirr haper).tendsto_fullTotalVariationDistance_kernelPowers x y

end ProbabilityTheory
