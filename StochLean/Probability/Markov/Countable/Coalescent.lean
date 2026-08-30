/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Coupling.Basic
public import StochLean.Probability.Markov.Countable.Green
public import StochLean.Probability.Markov.Countable.Periodicity
public import StochLean.Probability.Markov.Countable.Invariant
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Independent coalescent coupling

The kernel is defined from its semantics, not from the error-prone printed/OCR singleton formula:
off the diagonal the two coordinates move independently; on the diagonal a single transition is
pushed through `z ↦ (z,z)`.  Consequently the diagonal is absorbing.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Parallel composition is compatible with sequential kernel composition on countable state
spaces.  The proof is by singleton extensionality and Tonelli factorization. -/
theorem parallelComp_comp_parallelComp
    (κ₁ κ₂ η₁ η₂ : Kernel E E)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂]
    [IsSFiniteKernel η₁] [IsSFiniteKernel η₂] :
    (κ₂ ∥ₖ η₂) ∘ₖ (κ₁ ∥ₖ η₁) = (κ₂ ∘ₖ κ₁) ∥ₖ (η₂ ∘ₖ η₁) := by
  apply Kernel.ext
  intro p
  apply Measure.ext_of_singleton
  intro z
  have hz : ({z} : Set (E × E)) = ({z.1} : Set E) ×ˢ ({z.2} : Set E) := by
    ext w
    simp [Prod.ext_iff]
  rw [Kernel.comp_apply' _ _ _ (measurableSet_singleton z),
    Kernel.parallelComp_apply]
  simp_rw [hz, Kernel.parallelComp_apply_prod ({z.1} : Set E) ({z.2} : Set E)]
  rw [lintegral_prod_mul
    ((κ₂.measurable_coe (measurableSet_singleton z.1)).aemeasurable)
    ((η₂.measurable_coe (measurableSet_singleton z.2)).aemeasurable),
    Kernel.comp_apply' _ _ _ (measurableSet_singleton z.1),
    Kernel.comp_apply' _ _ _ (measurableSet_singleton z.2)]

/-- Powers of a product kernel are the products of the corresponding powers. -/
theorem parallelComp_pow (κ η : Kernel E E)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    ∀ n : ℕ, (κ ∥ₖ η) ^ n = (κ ^ n) ∥ₖ (η ^ n)
  | 0 => by
      change Kernel.id = Kernel.id ∥ₖ Kernel.id
      exact (Kernel.id_parallelComp_id (α := E) (β := E)).symm
  | n + 1 => by
      rw [pow_succ', parallelComp_pow κ η n, pow_succ', pow_succ']
      change (κ ∥ₖ η) ∘ₖ ((κ ^ n) ∥ₖ (η ^ n)) =
        (κ ∘ₖ (κ ^ n)) ∥ₖ (η ∘ₖ (η ^ n))
      letI : IsMarkovKernel (κ ^ n) := isMarkovKernel_pow κ n
      letI : IsMarkovKernel (η ^ n) := isMarkovKernel_pow η n
      exact parallelComp_comp_parallelComp (κ ^ n) κ (η ^ n) η

/-- A simultaneous product transition has the product of the two marginal transition masses. -/
theorem parallelComp_pow_apply_singleton (κ η : Kernel E E)
    [IsMarkovKernel κ] [IsMarkovKernel η] (n : ℕ) (x y u v : E) :
    ((κ ∥ₖ η) ^ n) (x, y) {(u, v)} = (κ ^ n) x {u} * (η ^ n) y {v} := by
  have huv : ({(u, v)} : Set (E × E)) = ({u} : Set E) ×ˢ ({v} : Set E) := by
    ext w
    simp [Prod.ext_iff]
  letI : IsMarkovKernel (κ ^ n) := isMarkovKernel_pow κ n
  letI : IsMarkovKernel (η ^ n) := isMarkovKernel_pow η n
  rw [parallelComp_pow, huv,
    Kernel.parallelComp_apply_prod ({u} : Set E) ({v} : Set E)]

/-- Two marginal transitions occurring at the same time give a reachable transition in the
parallel product chain. -/
theorem Kernel.parallelComp_canReach_of_common_time
    (κ η : Kernel E E) [IsMarkovKernel κ] [IsMarkovKernel η]
    {x y u v : E} {n : ℕ}
    (hκ : n ∈ κ.transitionTimes x u) (hη : n ∈ η.transitionTimes y v) :
    (κ ∥ₖ η).CanReach (x, y) (u, v) := by
  refine ⟨n, ?_⟩
  rw [parallelComp_pow_apply_singleton]
  exact ENNReal.mul_pos hκ.ne' hη.ne'

/-- Klenke's product-chain irreducibility step: an irreducible aperiodic countable-state kernel
has an irreducible independent product kernel. -/
theorem Kernel.isIrreducible_parallelComp_self
    (κ : Kernel E E) [IsMarkovKernel κ]
    (hirr : Kernel.IsIrreducible Measure.count κ) (haper : κ.IsAperiodic) :
    Kernel.IsIrreducible Measure.count (κ ∥ₖ κ) := by
  rw [Kernel.isIrreducible_count_iff_forall_canReach] at hirr ⊢
  rintro ⟨x, y⟩ ⟨u, v⟩
  obtain ⟨N₁, hN₁⟩ := haper.eventually_transitionTimes (hirr x u)
  obtain ⟨N₂, hN₂⟩ := haper.eventually_transitionTimes (hirr y v)
  let n := max N₁ N₂
  exact Kernel.parallelComp_canReach_of_common_time κ κ
    (hN₁ n (le_max_left _ _)) (hN₂ n (le_max_right _ _))

/-- Binding a product measure by a parallel product kernel factors into the product of the two
bound measures. -/
theorem parallelComp_comp_prodMeasure (κ η : Kernel E E)
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (μ ν : Measure E) [SFinite μ] [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  apply Measure.ext_of_singleton
  intro z
  have hz : ({z} : Set (E × E)) = ({z.1} : Set E) ×ˢ ({z.2} : Set E) := by
    ext w
    simp [Prod.ext_iff]
  rw [Measure.bind_apply (measurableSet_singleton z) (Kernel.aemeasurable _), hz]
  simp_rw [Kernel.parallelComp_apply_prod ({z.1} : Set E) ({z.2} : Set E)]
  rw [lintegral_prod_mul
    ((κ.measurable_coe (measurableSet_singleton z.1)).aemeasurable)
    ((η.measurable_coe (measurableSet_singleton z.2)).aemeasurable),
    Measure.prod_prod,
    Measure.bind_apply (measurableSet_singleton z.1) (Kernel.aemeasurable _),
    Measure.bind_apply (measurableSet_singleton z.2) (Kernel.aemeasurable _)]

/-- Products of invariant measures are invariant for the parallel product kernel. -/
theorem Kernel.Invariant.prod {κ η : Kernel E E} {μ ν : Measure E}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] [SFinite μ] [SFinite ν]
    (hκ : κ.Invariant μ) (hη : η.Invariant ν) :
    (κ ∥ₖ η).Invariant (μ.prod ν) := by
  rw [Kernel.Invariant] at hκ hη ⊢
  calc
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) :=
      ProbabilityTheory.parallelComp_comp_prodMeasure κ η μ ν
    _ = μ.prod ν := congrArg₂ Measure.prod hκ hη

/-- The diagonal in a countable measurable state space is measurable. -/
theorem measurableSet_pairDiagonal : MeasurableSet {p : E × E | p.1 = p.2} := by
  have hdiag : {p : E × E | p.1 = p.2} = ⋃ x : E, {(x, x)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨p.1, Prod.ext rfl h.symm⟩
    · rintro ⟨x, rfl⟩
      rfl
  rw [hdiag]
  exact MeasurableSet.iUnion fun _ => measurableSet_singleton _

/-- A single transition copied into both coordinates. -/
noncomputable def diagonalStepKernel (κ : Kernel E E) : Kernel (E × E) (E × E) :=
  (κ.map (fun z => (z, z))).comap Prod.fst measurable_fst

instance diagonalStepKernel.instIsMarkovKernel (κ : Kernel E E) [IsMarkovKernel κ] :
    IsMarkovKernel (diagonalStepKernel κ) := by
  unfold diagonalStepKernel
  let hdiag : Measurable (fun z : E => (z, z)) := measurable_id.prodMk measurable_id
  letI : IsMarkovKernel (κ.map fun z => (z, z)) := Kernel.IsMarkovKernel.map κ hdiag
  infer_instance

/-- Independent product evolution away from the diagonal, and shared evolution on it. -/
noncomputable def independentCoalescentKernel (κ : Kernel E E) : Kernel (E × E) (E × E) := by
  classical
  exact Kernel.piecewise measurableSet_pairDiagonal (diagonalStepKernel κ) (κ ∥ₖ κ)

instance independentCoalescentKernel.instIsMarkovKernel
    (κ : Kernel E E) [IsMarkovKernel κ] :
    IsMarkovKernel (independentCoalescentKernel κ) := by
  unfold independentCoalescentKernel
  letI : IsMarkovKernel (κ ∥ₖ κ) := by
    refine ⟨fun p => ?_⟩
    rw [Kernel.parallelComp_apply κ κ p]
    infer_instance
  infer_instance

/-- Off the diagonal the next pair law is the independent product law. -/
theorem independentCoalescentKernel_apply_of_ne
    (κ : Kernel E E) [IsMarkovKernel κ] {x y : E} (hxy : x ≠ y) :
    independentCoalescentKernel κ (x, y) = (κ x).prod (κ y) := by
  classical
  rw [independentCoalescentKernel, Kernel.piecewise_apply, if_neg]
  · exact Kernel.parallelComp_apply κ κ (x, y)
  · simpa using hxy

/-- On the diagonal the next pair is the pushforward of one transition through the diagonal map. -/
theorem independentCoalescentKernel_apply_diag
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    independentCoalescentKernel κ (x, x) =
      Measure.map (fun z => (z, z)) (κ x) := by
  classical
  have hdiag : Measurable (fun z : E => (z, z)) := measurable_id.prodMk measurable_id
  rw [independentCoalescentKernel, Kernel.piecewise_apply, if_pos (by simp),
    diagonalStepKernel, Kernel.comap_apply, Kernel.map_apply κ hdiag]

/-- The diagonal is absorbing in one step. -/
theorem independentCoalescentKernel_diagonal_compl
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    independentCoalescentKernel κ (x, x) {p | p.1 ≠ p.2} = 0 := by
  rw [independentCoalescentKernel_apply_diag, Measure.map_apply]
  · simp
  · exact measurable_id.prodMk measurable_id
  · exact measurableSet_pairDiagonal.compl

/-- Each transition of the independent coalescent kernel has the original first-coordinate
marginal. -/
theorem independentCoalescentKernel_map_fst
    (κ : Kernel E E) [IsMarkovKernel κ] :
    (independentCoalescentKernel κ).map Prod.fst =
      κ.comap Prod.fst measurable_fst := by
  ext p
  rcases p with ⟨x, y⟩
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  by_cases hxy : x = y
  · subst y
    have hdiag : Measurable (fun z : E => (z, z)) :=
      measurable_id.prodMk measurable_id
    rw [independentCoalescentKernel_apply_diag]
    rw [Measure.map_map measurable_fst hdiag]
    have hfun : Prod.fst ∘ (fun z : E => (z, z)) = id := rfl
    rw [hfun, Measure.map_id]
  · rw [independentCoalescentKernel_apply_of_ne κ hxy]
    simpa using Measure.map_fst_prod (E := E) (F := E) (μ := κ x) (ν := κ y)

/-- Each transition of the independent coalescent kernel has the original second-coordinate
marginal. -/
theorem independentCoalescentKernel_map_snd
    (κ : Kernel E E) [IsMarkovKernel κ] :
    (independentCoalescentKernel κ).map Prod.snd =
      κ.comap Prod.snd measurable_snd := by
  ext p
  rcases p with ⟨x, y⟩
  rw [Kernel.map_apply _ measurable_snd, Kernel.comap_apply]
  by_cases hxy : x = y
  · subst y
    have hdiag : Measurable (fun z : E => (z, z)) :=
      measurable_id.prodMk measurable_id
    rw [independentCoalescentKernel_apply_diag]
    rw [Measure.map_map measurable_snd hdiag]
    have hfun : Prod.snd ∘ (fun z : E => (z, z)) = id := rfl
    rw [hfun, Measure.map_id]
  · rw [independentCoalescentKernel_apply_of_ne κ hxy]
    simpa using Measure.map_snd_prod (E := E) (F := E) (μ := κ x) (ν := κ y)

/-- A path coupling is just a coupling of the two canonical path laws. -/
def IsMarkovPathCoupling (κ : Kernel E E) [IsMarkovKernel κ]
    (x y : E) (γ : Measure ((ℕ → E) × (ℕ → E))) : Prop :=
  IsCoupling γ (markovChainLaw κ x) (markovChainLaw κ y)

/-- Klenke's successful-coupling tail criterion. -/
def IsSuccessfulPathCoupling (γ : Measure ((ℕ → E) × (ℕ → E))) : Prop :=
  Tendsto (fun n => γ {p | ∃ k ≥ n, p.1 k ≠ p.2 k}) atTop (nhds 0)

/-- Almost-sure eventual equality of two coupled paths. -/
def EventuallyEqualAE (γ : Measure ((ℕ → E) × (ℕ → E))) : Prop :=
  ∀ᵐ p ∂γ, ∃ n, ∀ k ≥ n, p.1 k = p.2 k

/-- Existence of a successful coupling for a selected pair of starting states. -/
def HasSuccessfulCouplingFrom (κ : Kernel E E) [IsMarkovKernel κ]
    (x y : E) : Prop :=
  ∃ γ : Measure ((ℕ → E) × (ℕ → E)),
    IsMarkovPathCoupling κ x y γ ∧ IsSuccessfulPathCoupling γ

/-- A kernel admits successful couplings when every pair of canonical path laws does. -/
def HasSuccessfulCouplings (κ : Kernel E E) [IsMarkovKernel κ] : Prop :=
  ∀ x y, HasSuccessfulCouplingFrom κ x y

/-- Split a path of pairs into a pair of coordinate paths. -/
def splitPairPath (z : ℕ → E × E) : (ℕ → E) × (ℕ → E) :=
  (fun n => (z n).1, fun n => (z n).2)

theorem measurable_splitPairPath : Measurable (splitPairPath (E := E)) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro n
    exact measurable_fst.comp (measurable_pi_apply n)
  · rw [measurable_pi_iff]
    intro n
    exact measurable_snd.comp (measurable_pi_apply n)

/-- The path coupling generated by the semantic independent-coalescent transition kernel. -/
noncomputable def independentCoalescentPathLaw
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    Measure ((ℕ → E) × (ℕ → E)) :=
  Measure.map splitPairPath
    (markovChainLaw (independentCoalescentKernel κ) (x, y))

instance independentCoalescentPathLaw.instIsProbabilityMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    IsProbabilityMeasure (independentCoalescentPathLaw κ x y) := by
  unfold independentCoalescentPathLaw
  exact Measure.isProbabilityMeasure_map measurable_splitPairPath.aemeasurable

/-- The two coordinate laws of the independent-coalescent construction are the canonical path
laws of the original chain. -/
theorem independentCoalescentPathLaw_isMarkovPathCoupling
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    IsMarkovPathCoupling κ x y (independentCoalescentPathLaw κ x y) := by
  constructor
  · rw [independentCoalescentPathLaw,
      Measure.map_map measurable_fst measurable_splitPairPath]
    change Measure.map (pathMap Prod.fst)
      (markovChainLaw (independentCoalescentKernel κ) (x, y)) = markovChainLaw κ x
    exact markovChainLaw_map (independentCoalescentKernel κ) κ measurable_fst
      (independentCoalescentKernel_map_fst κ) (x, y)
  · rw [independentCoalescentPathLaw,
      Measure.map_map measurable_snd measurable_splitPairPath]
    change Measure.map (pathMap Prod.snd)
      (markovChainLaw (independentCoalescentKernel κ) (x, y)) = markovChainLaw κ y
    exact markovChainLaw_map (independentCoalescentKernel κ) κ measurable_snd
      (independentCoalescentKernel_map_snd κ) (x, y)

/-- A pair path hits the diagonal at some finite time. -/
def PairPathHitsDiagonal (z : ℕ → E × E) : Prop :=
  ∃ n, (z n).1 = (z n).2

/-- A pair path remains on the diagonal from some finite time onward. -/
def PairPathEventuallyDiagonal (z : ℕ → E × E) : Prop :=
  ∃ n, ∀ k ≥ n, (z k).1 = (z k).2

/-- The ordinary time-zero hitting time of the diagonal. -/
noncomputable def coalescenceTime (z : ℕ → E × E) : WithTop ℕ :=
  hittingAfter (fun n w => w n) {p : E × E | p.1 = p.2} 0 z

theorem coalescenceTime_lt_top_iff (z : ℕ → E × E) :
    coalescenceTime z < (⊤ : WithTop ℕ) ↔ PairPathHitsDiagonal z := by
  constructor
  · intro h
    have hne : hittingAfter (fun n (w : ℕ → E × E) => w n)
        {p : E × E | p.1 = p.2} 0 z ≠ ⊤ := by
      simpa only [coalescenceTime] using ne_of_lt h
    by_contra hhit
    apply hne
    apply hittingAfter_eq_top_iff.mpr
    intro n _hn hdiag
    exact hhit ⟨n, hdiag⟩
  · rintro ⟨n, hn⟩
    rw [lt_top_iff_ne_top]
    intro htop
    change hittingAfter (fun n (w : ℕ → E × E) => w n)
      {p : E × E | p.1 = p.2} 0 z = ⊤ at htop
    have hnever := (hittingAfter_eq_top_iff.mp htop) n (Nat.zero_le n)
    exact hnever hn

theorem measurableSet_pairPathHitsDiagonal :
    MeasurableSet {z : ℕ → E × E | PairPathHitsDiagonal z} := by
  have hrepr : {z : ℕ → E × E | PairPathHitsDiagonal z} =
      ⋃ n : ℕ, {z | (z n).1 = (z n).2} := by
    ext z
    simp [PairPathHitsDiagonal]
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro n
  change MeasurableSet
    ((fun z : ℕ → E × E => z n) ⁻¹' {p : E × E | p.1 = p.2})
  exact (measurable_pi_apply n) measurableSet_pairDiagonal

theorem measurableSet_pairPathEventuallyDiagonal :
    MeasurableSet {z : ℕ → E × E | PairPathEventuallyDiagonal z} := by
  have hrepr : {z : ℕ → E × E | PairPathEventuallyDiagonal z} =
      ⋃ n : ℕ, ⋂ k : ℕ, ⋂ (_h : n ≤ k), {z | (z k).1 = (z k).2} := by
    ext z
    simp [PairPathEventuallyDiagonal]
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _h
  change MeasurableSet
    ((fun z : ℕ → E × E => z k) ⁻¹' {p : E × E | p.1 = p.2})
  exact (measurable_pi_apply k) measurableSet_pairDiagonal

/-- Under the independent-coalescent path law, a diagonal state cannot be followed by an
off-diagonal state. -/
theorem independentCoalescent_adjacent_bad_zero
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) (n : ℕ) :
    markovChainLaw (independentCoalescentKernel κ) (x, y)
      ({z : ℕ → E × E | (z n).1 = (z n).2} ∩
        {z : ℕ → E × E | (z (n + 1)).1 ≠ (z (n + 1)).2}) = 0 := by
  change markovChainLaw (independentCoalescentKernel κ) (x, y)
      ({z : ℕ → E × E | z n ∈ {p : E × E | p.1 = p.2}} ∩
        {z : ℕ → E × E | z (n + 1) ∈ ({p : E × E | p.1 = p.2}ᶜ)}) = 0
  rw [markovChainLaw_inter_coordinate_succ
    (independentCoalescentKernel κ) (x, y) n
    measurableSet_pairDiagonal measurableSet_pairDiagonal.compl]
  apply setLIntegral_eq_zero measurableSet_pairDiagonal
  intro p hp
  rcases p with ⟨u, v⟩
  change u = v at hp
  subst v
  exact independentCoalescentKernel_diagonal_compl κ u

/-- The diagonal is pathwise absorbing outside one null set, simultaneously at every time. -/
theorem independentCoalescent_absorbing_ae
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    ∀ᵐ z ∂markovChainLaw (independentCoalescentKernel κ) (x, y),
      ∀ n, (z n).1 = (z n).2 → (z (n + 1)).1 = (z (n + 1)).2 := by
  apply ae_all_iff.2
  intro n
  rw [ae_iff]
  have hset :
      {z : ℕ → E × E |
        ¬ ((z n).1 = (z n).2 → (z (n + 1)).1 = (z (n + 1)).2)} =
        {z | (z n).1 = (z n).2} ∩
          {z | (z (n + 1)).1 ≠ (z (n + 1)).2} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · exact Classical.not_imp.mp
    · rintro ⟨hdiag, hnext⟩ h
      exact hnext (h hdiag)
  rw [hset]
  exact independentCoalescent_adjacent_bad_zero κ x y n

/-- For the absorbing independent coalescent, eventual diagonal residence is equivalent almost
surely to one finite diagonal hit. -/
theorem independentCoalescent_eventuallyDiagonal_iff_hits_ae
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    ∀ᵐ z ∂markovChainLaw (independentCoalescentKernel κ) (x, y),
      PairPathEventuallyDiagonal z ↔ PairPathHitsDiagonal z := by
  filter_upwards [independentCoalescent_absorbing_ae κ x y] with z hz
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn n le_rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, fun k hnk => ?_⟩
    induction k, hnk using Nat.le_induction with
    | base => exact hn
    | succ k hnk ih => exact hz k ih

end ProbabilityTheory
