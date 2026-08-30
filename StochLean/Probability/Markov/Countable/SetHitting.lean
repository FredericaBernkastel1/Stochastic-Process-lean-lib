/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Invariant

/-!
# Hitting measurable sets in countable-state Markov chains

The safe kernel is killed on entry into a measurable target set.  Its powers are identified with
the finite-horizon avoidance probabilities of the canonical Markov-chain law.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

noncomputable section

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def beforeHittingEvent (A : Set E) (n : ℕ) : Set (ℕ → E) :=
  {ω | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) A ω}

def beforeHittingHistory (A : Set E) (n : ℕ) : Set ((i : Finset.Iic n) → E) :=
  {z | ∀ j : Finset.Iic n, 1 ≤ (j : ℕ) → z j ∉ A}

theorem mem_beforeHittingEvent_iff (A : Set E) (n : ℕ) (ω : ℕ → E) :
    ω ∈ beforeHittingEvent A n ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ n → ω j ∉ A := by
  have hle : firstPositiveHittingTime (fun k (z : ℕ → E) => z k) A ω ≤ (n : ℕ∞) ↔
      ∃ j : ℕ, j ∈ Set.Icc 1 n ∧ ω j ∈ A := by
    change hittingAfter (fun k (z : ℕ → E) => z k) A 1 ω ≤ (n : WithTop ℕ) ↔ _
    exact hittingAfter_le_iff
  constructor
  · intro h j hj₁ hjn hjA
    exact (not_lt_of_ge (hle.mpr ⟨j, ⟨hj₁, hjn⟩, hjA⟩)) h
  · intro h
    rw [beforeHittingEvent, Set.mem_ofPred_eq, lt_iff_not_ge]
    intro hret
    obtain ⟨j, hj, hjA⟩ := hle.mp hret
    exact h j hj.1 hj.2 hjA

theorem measurableSet_beforeHittingHistory (A : Set E) (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (beforeHittingHistory A n) := by
  let J : Type := {j : ℕ // j ∈ Set.Icc 1 n}
  have hrepr : beforeHittingHistory A n =
      (⋃ j : J, {z : (i : Finset.Iic n) → E |
        z ⟨j, Finset.mem_Iic.mpr j.property.2⟩ ∈ A})ᶜ := by
    ext z
    simp only [beforeHittingHistory, Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_iUnion, not_exists]
    constructor
    · intro h j hjA
      exact h ⟨j, Finset.mem_Iic.mpr j.property.2⟩ j.property.1 hjA
    · intro h j hj₁ hjA
      exact h ⟨j, ⟨hj₁, Finset.mem_Iic.mp j.property⟩⟩ hjA
  rw [hrepr]
  exact (MeasurableSet.iUnion fun j : J =>
    (measurable_pi_apply (⟨j, Finset.mem_Iic.mpr j.property.2⟩ : Finset.Iic n)) hA).compl

theorem beforeHittingEvent_eq_preimage_history
    (A : Set E) (n : ℕ) :
    beforeHittingEvent A n =
      Preorder.frestrictLe n ⁻¹' beforeHittingHistory A n := by
  ext ω
  rw [mem_beforeHittingEvent_iff]
  constructor
  · intro h j hj₁
    exact h j hj₁ (Finset.mem_Iic.mp j.property)
  · intro h j hj₁ hjn
    exact h ⟨j, Finset.mem_Iic.mpr hjn⟩ hj₁

theorem measurableSet_beforeHittingEvent
    (A : Set E) (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (beforeHittingEvent A n) := by
  rw [beforeHittingEvent_eq_preimage_history]
  exact (measurableSet_beforeHittingHistory A hA n).preimage
    (Preorder.measurable_frestrictLe n)

theorem setIntegral_partialTraj_transitionProbability_beforeHittingHistory
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ)
    {B : Set E} (hB : MeasurableSet B) :
    ∫ z in beforeHittingHistory A n,
        transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) B
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 n (fun _ => start) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeHittingHistory A n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) B y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) := by
  have hnext : MeasurableSet {z : ℕ → E | z (n + 1) ∈ B} :=
    (measurable_pi_apply (n + 1)) hB
  have hf : Integrable (eventIndicator (fun z : ℕ → E => z (n + 1)) B)
      (Kernel.traj (X := fun _ : ℕ => E)
        (markovChainStep κ) 0 (fun _ => start)) := by
    change Integrable ({z : ℕ → E | z (n + 1) ∈ B}.indicator
      (fun _ => (1 : ℝ))) _
    exact (integrable_const (1 : ℝ)).indicator hnext
  have htraj := Kernel.setIntegral_traj_partialTraj
    (κ := markovChainStep κ) (a := 0) (b := n) (Nat.zero_le n)
    (x₀ := fun _ => start)
    (f := eventIndicator (fun z : ℕ → E => z (n + 1)) B) hf
    (measurableSet_beforeHittingHistory A hA n)
  have hinner :
      (fun z : (i : Finset.Iic n) → E =>
          ∫ y, eventIndicator (fun w : ℕ → E => w (n + 1)) B y
            ∂Kernel.traj (markovChainStep κ) n z) =
        fun z => transitionProbability κ
          (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) B := by
    funext z
    exact integral_eventIndicator_traj_succ κ n z hB
  rw [hinner] at htraj
  exact htraj

theorem setIntegral_transitionProbability_beforeHitting_preimage
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ)
    {B : Set E} (hB : MeasurableSet B) :
    ∫ z in Preorder.frestrictLe n ⁻¹' beforeHittingHistory A n,
        transitionProbability κ (z n) B
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeHittingHistory A n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) B y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) := by
  have hfinite := setIntegral_partialTraj_transitionProbability_beforeHittingHistory
    κ start A hA n hB
  have hmap := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => E) (κ := markovChainStep κ) 0 n (fun _ => start)
  rw [← hmap] at hfinite
  have htrans : Measurable (fun z : (i : Finset.Iic n) → E =>
      transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) B) :=
    ((κ.measurable_coe hB).ennreal_toReal.comp (measurable_pi_apply _))
  rw [setIntegral_map (measurableSet_beforeHittingHistory A hA n)
    htrans.aestronglyMeasurable
    (Preorder.measurable_frestrictLe n).aemeasurable] at hfinite
  simpa only [Preorder.frestrictLe_apply] using hfinite

theorem setIntegral_transitionProbability_beforeHitting
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ)
    {B : Set E} (hB : MeasurableSet B) :
    ∫ z in beforeHittingEvent A n, transitionProbability κ (z n) B
        ∂markovChainLaw κ start =
      (markovChainLaw κ start).real
        (beforeHittingEvent A n ∩ {z : ℕ → E | z (n + 1) ∈ B}) := by
  have h := setIntegral_transitionProbability_beforeHitting_preimage
    κ start A hA n hB
  rw [← beforeHittingEvent_eq_preimage_history A n] at h
  rw [← markovChainLaw_eq_traj κ start] at h
  rw [setIntegral_eventIndicator_coordinate_eq_real
    (markovChainLaw κ start) (beforeHittingEvent A n) (n + 1) hB] at h
  exact h

theorem setLIntegral_transition_beforeHitting
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (n : ℕ)
    {B : Set E} (hB : MeasurableSet B) :
    ∫⁻ z in beforeHittingEvent A n, κ (z n) B ∂markovChainLaw κ start =
      markovChainLaw κ start
        (beforeHittingEvent A n ∩ {z : ℕ → E | z (n + 1) ∈ B}) := by
  let μ := markovChainLaw κ start
  let C := beforeHittingEvent A n
  let L : ℝ≥0∞ := ∫⁻ z in C, κ (z n) B ∂μ
  let R : ℝ≥0∞ := μ (C ∩ {z : ℕ → E | z (n + 1) ∈ B})
  have hmeas : AEMeasurable (fun z : ℕ → E => κ (z n) B) (μ.restrict C) :=
    ((κ.measurable_coe hB).comp (measurable_pi_apply n)).aemeasurable
  have hpoint : ∀ᵐ z ∂μ.restrict C, κ (z n) B < ∞ :=
    Filter.Eventually.of_forall fun _z => lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  have hL_le : L ≤ 1 := by
    calc
      L ≤ ∫⁻ _z in C, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun _z => prob_le_one
      _ = μ C := by simp [C]
      _ ≤ 1 := prob_le_one
  have hR_le : R ≤ 1 := prob_le_one
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt (hL_le.trans_lt ENNReal.one_lt_top))
    (ne_of_lt (hR_le.trans_lt ENNReal.one_lt_top))).mp
  rw [show L.toReal = ∫ z in C, transitionProbability κ (z n) B ∂μ by
    change L.toReal = ∫ z in C, (κ (z n) B).toReal ∂μ
    exact (integral_toReal hmeas hpoint).symm]
  simpa [μ, C, R, Measure.real] using
    setIntegral_transitionProbability_beforeHitting κ start A hA n hB

/-- The substochastic kernel which is killed on entering `A`, and is zero when started in `A`. -/
noncomputable def safeKernel
    (κ : Kernel E E) (A : Set E) (hA : MeasurableSet A) : Kernel E E :=
  by
    classical
    exact Kernel.piecewise hA (Kernel.const E (0 : Measure E)) (κ.restrict hA.compl)

theorem safeKernel_apply_of_mem
    (κ : Kernel E E) (A : Set E) (hA : MeasurableSet A)
    {x : E} (hx : x ∈ A) :
    safeKernel κ A hA x = 0 := by
  classical
  rw [safeKernel, Kernel.piecewise_apply, if_pos hx]
  rfl

theorem safeKernel_apply_of_not_mem
    (κ : Kernel E E) (A : Set E) (hA : MeasurableSet A)
    {x : E} (hx : x ∉ A) :
    safeKernel κ A hA x = (κ x).restrict Aᶜ := by
  classical
  rw [safeKernel, Kernel.piecewise_apply, if_neg hx, Kernel.restrict_apply]

noncomputable def avoidanceSetTermMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (n : ℕ) : Measure E :=
  Measure.map (fun ω : ℕ → E => ω n)
    ((markovChainLaw κ start).restrict (beforeHittingEvent A n))

theorem avoidanceSetTermMeasure_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (n : ℕ) {B : Set E} (hB : MeasurableSet B) :
    avoidanceSetTermMeasure κ start A n B =
      markovChainLaw κ start
        (beforeHittingEvent A n ∩ {ω | ω n ∈ B}) := by
  rw [avoidanceSetTermMeasure, Measure.map_apply (measurable_pi_apply n) hB,
    Measure.restrict_apply]
  · congr 1
    ext ω
    simp [and_comm]
  · exact (measurable_pi_apply n) hB

theorem avoidanceSetTermMeasure_zero
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E) (A : Set E) :
    avoidanceSetTermMeasure κ start A 0 = Measure.dirac start := by
  apply Measure.ext_of_singleton
  intro y
  rw [avoidanceSetTermMeasure_apply κ start A 0 (measurableSet_singleton y)]
  have hzero : beforeHittingEvent A 0 = (Set.univ : Set (ℕ → E)) := by
    ext ω
    constructor
    · intro _
      trivial
    · intro _
      rw [mem_beforeHittingEvent_iff]
      intro j hj₁ hj₀
      exact (Nat.not_succ_le_zero 0 (hj₁.trans hj₀)).elim
  rw [hzero, Set.univ_inter,
    markovChainLaw_apply_coordinate κ start 0 (measurableSet_singleton y), pow_zero]
  rfl

theorem beforeHittingEvent_succ_inter_coordinate_of_not_mem
    (A : Set E) (y : E) (hy : y ∉ A) (n : ℕ) :
    beforeHittingEvent A (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = y} =
      beforeHittingEvent A n ∩ {ω : ℕ → E | ω (n + 1) = y} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_beforeHittingEvent_iff]
  constructor
  · rintro ⟨h, heq⟩
    exact ⟨fun j hj₁ hjn => h j hj₁ (hjn.trans (Nat.le_succ n)), heq⟩
  · rintro ⟨h, heq⟩
    constructor
    · intro j hj₁ hjn
      rcases Nat.lt_or_eq_of_le hjn with hj | rfl
      · exact h j hj₁ (Nat.le_of_lt_succ hj)
      · simpa [heq] using hy
    · exact heq

theorem beforeHittingEvent_succ_inter_coordinate_of_mem
    (A : Set E) (y : E) (hy : y ∈ A) (n : ℕ) :
    beforeHittingEvent A (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = y} = ∅ := by
  ext ω
  constructor
  · rintro ⟨havoid, heq⟩
    have hnot := (mem_beforeHittingEvent_iff A (n + 1) ω).1 havoid
      (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) le_rfl
    exact (hnot (heq ▸ hy)).elim
  · intro h
    exact h.elim

theorem avoidanceSetTermMeasure_succ_apply_of_not_mem
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (y : E) (hy : y ∉ A) (n : ℕ) :
    avoidanceSetTermMeasure κ start A (n + 1) {y} =
      (κ ∘ₘ avoidanceSetTermMeasure κ start A n) {y} := by
  rw [avoidanceSetTermMeasure_apply κ start A (n + 1)
    (measurableSet_singleton y)]
  simp only [Set.mem_singleton_iff]
  rw [beforeHittingEvent_succ_inter_coordinate_of_not_mem A y hy n]
  have hstep := setLIntegral_transition_beforeHitting κ start A hA n
    (measurableSet_singleton y)
  simp only [Set.mem_singleton_iff] at hstep
  rw [← hstep]
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable]
  rw [avoidanceSetTermMeasure]
  rw [lintegral_map
    (κ.measurable_coe (measurableSet_singleton y))
    (measurable_pi_apply n)]

theorem avoidanceSetTermMeasure_apply_singleton_of_mem
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hstart : start ∉ A) (n : ℕ) {y : E} (hy : y ∈ A) :
    avoidanceSetTermMeasure κ start A n {y} = 0 := by
  cases n with
  | zero =>
      rw [avoidanceSetTermMeasure_zero,
        Measure.dirac_apply' _ (measurableSet_singleton y)]
      have hne : start ≠ y := by
        intro h
        apply hstart
        simpa [h] using hy
      simp [hne]
  | succ n =>
      rw [avoidanceSetTermMeasure_apply κ start A (n + 1)
        (measurableSet_singleton y)]
      change markovChainLaw κ start
        (beforeHittingEvent A (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = y}) = 0
      calc
        markovChainLaw κ start
            (beforeHittingEvent A (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = y}) =
            markovChainLaw κ start ∅ := congrArg (markovChainLaw κ start)
              (beforeHittingEvent_succ_inter_coordinate_of_mem A y hy n)
        _ = 0 := OuterMeasureClass.measure_empty _

theorem avoidanceSetTermMeasure_succ_eq_safe
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (hstart : start ∉ A) (n : ℕ) :
    avoidanceSetTermMeasure κ start A (n + 1) =
      safeKernel κ A hA ∘ₘ avoidanceSetTermMeasure κ start A n := by
  apply Measure.ext_of_singleton
  intro y
  by_cases hy : y ∈ A
  · rw [avoidanceSetTermMeasure_apply_singleton_of_mem κ start A hstart (n + 1) hy]
    rw [Measure.bind_apply (measurableSet_singleton y)
      (safeKernel κ A hA).aemeasurable]
    symm
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ A
      · change (safeKernel κ A hA z) {y} = 0
        rw [safeKernel_apply_of_mem κ A hA hz]
        simp
      · change (safeKernel κ A hA z) {y} = 0
        rw [safeKernel_apply_of_not_mem κ A hA hz,
          Measure.restrict_apply (measurableSet_singleton y)]
        simp [hy]
  · rw [avoidanceSetTermMeasure_succ_apply_of_not_mem κ start A hA y hy n]
    rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable,
      Measure.bind_apply (measurableSet_singleton y) (safeKernel κ A hA).aemeasurable]
    simp_rw [lintegral_countable']
    apply tsum_congr
    intro z
    by_cases hz : z ∈ A
    · rw [safeKernel_apply_of_mem κ A hA hz]
      rw [avoidanceSetTermMeasure_apply_singleton_of_mem κ start A hstart n hz]
      simp
    · rw [safeKernel_apply_of_not_mem κ A hA hz,
        Measure.restrict_apply (measurableSet_singleton y)]
      simp [hy]

theorem avoidanceSetTermMeasure_eq_safe_pow
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (hstart : start ∉ A) :
    ∀ n : ℕ, avoidanceSetTermMeasure κ start A n =
      (safeKernel κ A hA ^ n) start
  | 0 => by rw [avoidanceSetTermMeasure_zero, pow_zero]; rfl
  | n + 1 => by
      rw [avoidanceSetTermMeasure_succ_eq_safe κ start A hA hstart n,
        avoidanceSetTermMeasure_eq_safe_pow κ start A hA hstart n, pow_succ']
      rfl

theorem markovChainLaw_beforeHittingEvent_eq_safe_pow
    (κ : Kernel E E) [IsMarkovKernel κ] (start : E)
    (A : Set E) (hA : MeasurableSet A) (hstart : start ∉ A) (n : ℕ) :
    markovChainLaw κ start (beforeHittingEvent A n) =
      (safeKernel κ A hA ^ n) start Set.univ := by
  have huniv := avoidanceSetTermMeasure_apply κ start A n MeasurableSet.univ
  simp only [Set.mem_univ, Set.ofPred_true, Set.inter_univ] at huniv
  rw [avoidanceSetTermMeasure_eq_safe_pow κ start A hA hstart n] at huniv
  exact huniv.symm

end

end ProbabilityTheory
