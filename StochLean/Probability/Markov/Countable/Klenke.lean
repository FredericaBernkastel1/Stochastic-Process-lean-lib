/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Coalescent
public import StochLean.Probability.Markov.Countable.HittingProbability
public import StochLean.Probability.Markov.Countable.SetHitting

/-!
# Klenke's product-chain coupling argument

For an irreducible, aperiodic countable-state Markov kernel with an invariant probability measure,
the independent product chain is irreducible and recurrent.  Its semantic coalescent modification
therefore hits the diagonal almost surely.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

noncomputable section

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def positiveSetHitEvent (A : Set E) : Set (ℕ → E) :=
  {ω | ∃ n, 1 ≤ n ∧ ω n ∈ A}

theorem antitone_beforeHittingEvent (A : Set E) :
    Antitone (beforeHittingEvent A) := by
  intro m n hmn ω hω
  rw [mem_beforeHittingEvent_iff] at hω ⊢
  intro j hj₁ hjm
  exact hω j hj₁ (hjm.trans hmn)

theorem compl_positiveSetHitEvent_eq_iInter_beforeHitting (A : Set E) :
    (positiveSetHitEvent A)ᶜ = ⋂ n : ℕ, beforeHittingEvent A n := by
  ext ω
  simp only [Set.mem_compl_iff, positiveSetHitEvent, Set.mem_ofPred_eq,
    Set.mem_iInter, mem_beforeHittingEvent_iff]
  push Not
  constructor
  · intro h n j hj₁ hjn
    exact h j hj₁
  · intro h j hj₁
    exact h j j hj₁ le_rfl

theorem measurableSet_positiveSetHitEvent (A : Set E) (hA : MeasurableSet A) :
    MeasurableSet (positiveSetHitEvent A) := by
  rw [← compl_compl (positiveSetHitEvent A),
    compl_positiveSetHitEvent_eq_iInter_beforeHitting A]
  exact (MeasurableSet.iInter (measurableSet_beforeHittingEvent A hA)).compl

theorem safeKernel_independentCoalescent_eq_parallelComp
    (κ : Kernel E E) [IsMarkovKernel κ] :
    safeKernel (independentCoalescentKernel κ) {p : E × E | p.1 = p.2}
        measurableSet_pairDiagonal =
      safeKernel (κ ∥ₖ κ) {p : E × E | p.1 = p.2}
        measurableSet_pairDiagonal := by
  apply Kernel.ext
  intro p
  rcases p with ⟨x, y⟩
  by_cases hxy : x = y
  · subst y
    rw [safeKernel_apply_of_mem, safeKernel_apply_of_mem]
    · rfl
    · simp
  · rw [safeKernel_apply_of_not_mem, safeKernel_apply_of_not_mem,
      independentCoalescentKernel_apply_of_ne κ hxy,
      Kernel.parallelComp_apply κ κ (x, y)]
    · simpa using hxy
    · simpa using hxy

theorem markovChainLaw_beforeDiagonal_eq_parallelComp
    (κ : Kernel E E) [IsMarkovKernel κ] {x y : E} (hxy : x ≠ y) (n : ℕ) :
    markovChainLaw (independentCoalescentKernel κ) (x, y)
        (beforeHittingEvent {p : E × E | p.1 = p.2} n) =
      markovChainLaw (κ ∥ₖ κ) (x, y)
        (beforeHittingEvent {p : E × E | p.1 = p.2} n) := by
  rw [markovChainLaw_beforeHittingEvent_eq_safe_pow
      (independentCoalescentKernel κ) (x, y)
      {p : E × E | p.1 = p.2} measurableSet_pairDiagonal (by simpa) n,
    markovChainLaw_beforeHittingEvent_eq_safe_pow
      (κ ∥ₖ κ) (x, y)
      {p : E × E | p.1 = p.2} measurableSet_pairDiagonal (by simpa) n,
    safeKernel_independentCoalescent_eq_parallelComp κ]

theorem parallelComp_positiveDiagonalHit_eq_one
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (x y : E) :
    markovChainLaw (κ ∥ₖ κ) (x, y)
      (positiveSetHitEvent {p : E × E | p.1 = p.2}) = 1 := by
  letI : IsProbabilityMeasure (π.prod π) := inferInstance
  have hprodInv : (κ ∥ₖ κ).Invariant (π.prod π) := hπ.prod hπ
  have hprodIrr : Kernel.IsIrreducible Measure.count (κ ∥ₖ κ) :=
    κ.isIrreducible_parallelComp_self hirr haper
  have hfixed := returnProbability_eq_one_of_irreducible_invariant
    (κ ∥ₖ κ) (π.prod π) hprodInv hprodIrr (x, y) (x, x)
  have hfixed' : markovChainLaw (κ ∥ₖ κ) (x, y)
      (positiveHitEvent (x, x)) = 1 := by
    simpa [returnProbability, positiveHitEvent] using hfixed
  apply le_antisymm prob_le_one
  rw [← hfixed']
  apply measure_mono
  intro ω hω
  change ω ∈ positiveHitEvent (x, x) at hω
  rw [positiveHitEvent, ← iUnion_firstReturnSlice] at hω
  rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
  change ω ∈ beforeReturnEvent (x, x) n ∩ {z | z (n + 1) = (x, x)} at hn
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
  rw [hn.2]
  simp

theorem independentCoalescent_positiveDiagonalHit_eq_one
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (x y : E) :
    markovChainLaw (independentCoalescentKernel κ) (x, y)
      (positiveSetHitEvent {p : E × E | p.1 = p.2}) = 1 := by
  by_cases hxy : x = y
  · subst y
    have hdiagNext : markovChainLaw (independentCoalescentKernel κ) (x, x)
        {z : ℕ → E × E | (z 1).1 = (z 1).2} = 1 := by
      change markovChainLaw (independentCoalescentKernel κ) (x, x)
        {z : ℕ → E × E | z 1 ∈ {p : E × E | p.1 = p.2}} = 1
      rw [markovChainLaw_apply_coordinate (independentCoalescentKernel κ) (x, x) 1
        measurableSet_pairDiagonal]
      rw [pow_one, independentCoalescentKernel_apply_diag]
      rw [Measure.map_apply]
      · simp
      · exact measurable_id.prodMk measurable_id
      · exact measurableSet_pairDiagonal
    apply le_antisymm prob_le_one
    rw [← hdiagNext]
    apply measure_mono
    intro ω hω
    exact ⟨1, le_rfl, hω⟩
  · have hprodPos := parallelComp_positiveDiagonalHit_eq_one
      κ π hπ hirr haper x y
    have hprodNever : markovChainLaw (κ ∥ₖ κ) (x, y)
        (⋂ n : ℕ, beforeHittingEvent {p : E × E | p.1 = p.2} n) = 0 := by
      rw [← compl_positiveSetHitEvent_eq_iInter_beforeHitting]
      rw [measure_compl
        (measurableSet_positiveSetHitEvent _ measurableSet_pairDiagonal)
        (measure_ne_top _ _), measure_univ, hprodPos]
      simp
    have hcoalNever : markovChainLaw (independentCoalescentKernel κ) (x, y)
        (⋂ n : ℕ, beforeHittingEvent {p : E × E | p.1 = p.2} n) = 0 := by
      rw [antitone_beforeHittingEvent _ |>.measure_iInter
        (fun n => (measurableSet_beforeHittingEvent _ measurableSet_pairDiagonal n).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩]
      simp_rw [markovChainLaw_beforeDiagonal_eq_parallelComp κ hxy]
      rw [← antitone_beforeHittingEvent _ |>.measure_iInter
        (fun n => (measurableSet_beforeHittingEvent _ measurableSet_pairDiagonal n).nullMeasurableSet)
        ⟨0, measure_ne_top _ _⟩]
      exact hprodNever
    have hcompl : markovChainLaw (independentCoalescentKernel κ) (x, y)
        (positiveSetHitEvent {p : E × E | p.1 = p.2})ᶜ = 0 := by
      rw [compl_positiveSetHitEvent_eq_iInter_beforeHitting]
      exact hcoalNever
    have hc := measure_compl
      (μ := markovChainLaw (independentCoalescentKernel κ) (x, y))
      (measurableSet_positiveSetHitEvent _ measurableSet_pairDiagonal)
      (measure_ne_top _ _)
    rw [measure_univ, hcompl] at hc
    apply le_antisymm prob_le_one
    exact tsub_eq_zero_iff_le.mp hc.symm

/-- Klenke's product-chain argument: the semantic coalescent hits the diagonal almost surely. -/
theorem independentCoalescent_pairPathHitsDiagonal_eq_one
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (haper : κ.IsAperiodic) (x y : E) :
    markovChainLaw (independentCoalescentKernel κ) (x, y)
      {z | PairPathHitsDiagonal z} = 1 := by
  have hpositive := independentCoalescent_positiveDiagonalHit_eq_one
    κ π hπ hirr haper x y
  apply le_antisymm prob_le_one
  rw [← hpositive]
  apply measure_mono
  rintro ω ⟨n, _hn, hdiag⟩
  exact ⟨n, hdiag⟩

end

end ProbabilityTheory
