/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Invariant
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Hitting probabilities for countable-state Markov chains

Killed kernels encode avoidance of a singleton.  The principal result proves that an irreducible
Markov kernel with an invariant probability measure hits every state almost surely from every
starting state.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

noncomputable section

local instance : DecidableEq E := Classical.decEq E

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

noncomputable def killedKernel (κ : Kernel E E) (a : E) : Kernel E E :=
  κ.restrict (measurableSet_singleton a).compl

noncomputable def survivalMass (κ : Kernel E E) (a : E) (n : ℕ) (x : E) : ℝ≥0∞ :=
  (killedKernel κ a ^ n) x Set.univ

theorem killedKernel_apply_univ_le_one
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) :
    killedKernel κ a x Set.univ ≤ 1 := by
  rw [killedKernel, Kernel.restrict_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter]
  calc
    κ x ({a}ᶜ) ≤ κ x Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem antitone_survivalMass
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) :
    Antitone (fun n => survivalMass κ a n x) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [survivalMass, survivalMass, Kernel.pow_succ_apply_eq_lintegral _ n x
    MeasurableSet.univ]
  calc
    (∫⁻ y, killedKernel κ a y Set.univ ∂(killedKernel κ a ^ n) x) ≤
        ∫⁻ _y, (1 : ℝ≥0∞) ∂(killedKernel κ a ^ n) x :=
      lintegral_mono fun y => killedKernel_apply_univ_le_one κ a y
    _ = (killedKernel κ a ^ n) x Set.univ := by simp

noncomputable def neverHitIncluding (κ : Kernel E E) (a x : E) : ℝ≥0∞ :=
  if x = a then 0 else ⨅ n : ℕ, survivalMass κ a n x

theorem neverHitIncluding_self (κ : Kernel E E) (a : E) :
    neverHitIncluding κ a a = 0 := by simp [neverHitIncluding]

theorem survivalMass_le_one
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) (n : ℕ) :
    survivalMass κ a n x ≤ 1 := by
  calc
    survivalMass κ a n x ≤ survivalMass κ a 0 x :=
      antitone_survivalMass κ a x (Nat.zero_le n)
    _ = 1 := by
      rw [survivalMass, pow_zero]
      change Kernel.id x Set.univ = 1
      simp

theorem neverHitIncluding_le_one
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) :
    neverHitIncluding κ a x ≤ 1 := by
  by_cases hxa : x = a
  · simp [neverHitIncluding, hxa]
  · rw [neverHitIncluding, if_neg hxa]
    calc
      (⨅ n : ℕ, survivalMass κ a n x) ≤ survivalMass κ a 0 x := iInf_le _ 0
      _ = 1 := by
        rw [survivalMass, pow_zero]
        change Kernel.id x Set.univ = 1
        simp

theorem measurable_neverHitIncluding (κ : Kernel E E) (a : E) :
    Measurable (neverHitIncluding κ a) :=
  measurable_of_countable _

theorem survivalMass_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) (n : ℕ) :
    survivalMass κ a (n + 1) x =
      ∫⁻ y in {a}ᶜ, survivalMass κ a n y ∂κ x := by
  rw [survivalMass, show n + 1 = 1 + n by omega,
    Kernel.pow_add_apply_eq_lintegral (killedKernel κ a) 1 n x
    MeasurableSet.univ]
  simp only [pow_one]
  rw [killedKernel, Kernel.restrict_apply]
  rfl

theorem iInf_survivalMass_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) :
    (⨅ n : ℕ, survivalMass κ a (n + 1) x) =
      ⨅ n : ℕ, survivalMass κ a n x := by
  apply le_antisymm
  · exact le_iInf fun n => iInf_le_of_le n
      (antitone_survivalMass κ a x (Nat.le_succ n))
  · apply le_iInf
    intro n
    exact iInf_le_of_le (n + 1) le_rfl

theorem neverHitIncluding_harmonic
    (κ : Kernel E E) [IsMarkovKernel κ] (a x : E) :
    neverHitIncluding κ a x =
      if x = a then 0 else ∫⁻ y, neverHitIncluding κ a y ∂κ x := by
  by_cases hxa : x = a
  · simp [neverHitIncluding, hxa]
  rw [neverHitIncluding, if_neg hxa, if_neg hxa]
  have hmeas (n : ℕ) : Measurable (survivalMass κ a n) :=
    measurable_of_countable _
  have hanti : Antitone (fun n : ℕ => survivalMass κ a n) := by
    intro m n hmn y
    exact antitone_survivalMass κ a y hmn
  have hfin : (∫⁻ y in {a}ᶜ, survivalMass κ a 0 y ∂κ x) ≠ ∞ := by
    have hle : (∫⁻ y in {a}ᶜ, survivalMass κ a 0 y ∂κ x) ≤ 1 := by
      have hzero : survivalMass κ a 0 = fun _ => (1 : ℝ≥0∞) := by
        funext y
        rw [survivalMass, pow_zero]
        change Kernel.id y Set.univ = 1
        simp
      calc
        (∫⁻ y in {a}ᶜ, survivalMass κ a 0 y ∂κ x) = κ x ({a}ᶜ) := by
          rw [hzero]
          simp
        _ ≤ κ x Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)
  calc
    (⨅ n : ℕ, survivalMass κ a n x) =
        ⨅ n : ℕ, survivalMass κ a (n + 1) x :=
      (iInf_survivalMass_succ κ a x).symm
    _ = ⨅ n : ℕ, ∫⁻ y in {a}ᶜ, survivalMass κ a n y ∂κ x := by
      simp only [survivalMass_succ]
    _ = ∫⁻ y in {a}ᶜ, ⨅ n : ℕ, survivalMass κ a n y ∂κ x := by
      rw [lintegral_iInf (μ := (κ x).restrict {a}ᶜ) hmeas hanti hfin]
    _ = ∫⁻ y, neverHitIncluding κ a y ∂κ x := by
      rw [← lintegral_indicator (measurableSet_singleton a).compl]
      apply lintegral_congr
      intro y
      by_cases hya : y = a
      · simp [hya, neverHitIncluding]
      · simp [hya, neverHitIncluding]

/-- A nonnegative killed-chain survival function vanishes for an irreducible chain carrying an
invariant probability. -/
theorem neverHitIncluding_eq_zero_of_irreducible_invariant
    (κ : Kernel E E) [IsMarkovKernel κ] (a : E)
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    ∀ x, neverHitIncluding κ a x = 0 := by
  let h : E → ℝ≥0∞ := neverHitIncluding κ a
  let q : E → ℝ≥0∞ := fun x => ∫⁻ y, h y ∂κ x
  have hh_meas : Measurable h := measurable_neverHitIncluding κ a
  have hq_meas : Measurable q := hh_meas.lintegral_kernel
  have hh_le_q (x : E) : h x ≤ q x := by
    rw [show h x = neverHitIncluding κ a x by rfl,
      neverHitIncluding_harmonic]
    by_cases hxa : x = a
    · simp [hxa]
    · simp [hxa, q, h]
  have hh_le_one (x : E) : h x ≤ 1 := neverHitIncluding_le_one κ a x
  have hq_le_one (x : E) : q x ≤ 1 := by
    calc
      q x = ∫⁻ y, h y ∂κ x := rfl
      _ ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂κ x := lintegral_mono hh_le_one
      _ = 1 := by simp
  have hπh_fin : (∫⁻ x, h x ∂π) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ x, h x ∂π) ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂π := lintegral_mono hh_le_one
      _ = 1 := by simp
      _ < ∞ := ENNReal.one_lt_top
  have hπq_eq : (∫⁻ x, q x ∂π) = ∫⁻ x, h x ∂π := by
    calc
      (∫⁻ x, q x ∂π) = ∫⁻ x, h x ∂π.bind κ :=
        (Measure.lintegral_bind κ.aemeasurable hh_meas.aemeasurable).symm
      _ = ∫⁻ x, h x ∂π := by rw [hπ.def]
  have hdiff : (∫⁻ x, q x - h x ∂π) = 0 := by
    rw [lintegral_sub hh_meas hπh_fin (Filter.Eventually.of_forall hh_le_q), hπq_eq,
      tsub_self]
  have hπa_pos : 0 < π {a} := by
    have hirr' := (Kernel.isIrreducible_count_iff_forall_canReach κ).1 hirr
    have hnonempty : ∃ x : E, 0 < π {x} := by
      by_contra hnone
      have hall : ∀ x : E, π {x} = 0 := by
        intro x
        exact le_antisymm (le_of_not_gt fun hx => hnone ⟨x, hx⟩) bot_le
      have huniv : π Set.univ = 0 := by
        have hzero := (measure_preimage_eq_zero_iff_of_countable
          (μ := π) (s := Set.univ) (f := id) (Set.to_countable Set.univ)).2 (by
            intro x _hx
            simpa using hall x)
        simpa using hzero
      exact one_ne_zero ((measure_univ (μ := π)).symm.trans huniv)
    obtain ⟨x, hx⟩ := hnonempty
    exact hπ.measure_pos_of_canReach hx (hirr' x a)
  have hqa_zero : q a = 0 := by
    have hsingle : (q a - h a) * π {a} = 0 := by
      apply le_antisymm
      · calc
          (q a - h a) * π {a} = ∫⁻ x in {a}, q x - h x ∂π := by
              rw [lintegral_singleton]
          _ ≤ ∫⁻ x, q x - h x ∂π := setLIntegral_le_lintegral _ _
          _ = 0 := hdiff
      · exact bot_le
    have hha : h a = 0 := neverHitIncluding_self κ a
    rw [hha, tsub_zero] at hsingle
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hsingle with hq | hπzero
    · exact hq
    · exact False.elim (ne_of_gt hπa_pos hπzero)
  have hharm (x : E) : h x = q x := by
    rw [show h x = neverHitIncluding κ a x by rfl,
      neverHitIncluding_harmonic]
    by_cases hxa : x = a
    · subst x
      simp only [if_pos rfl]
      exact hqa_zero.symm
    · simp only [if_neg hxa]
      rfl
  have hpow (n : ℕ) (x : E) : (∫⁻ y, h y ∂(κ ^ n) x) = h x := by
    induction n with
    | zero =>
        rw [pow_zero]
        exact Kernel.lintegral_id x
    | succ n ih =>
        rw [pow_succ']
        change (∫⁻ y, h y ∂(κ ∘ₖ (κ ^ n)) x) = h x
        rw [Kernel.lintegral_comp κ (κ ^ n) x hh_meas]
        have hk (y : E) : (∫⁻ z, h z ∂κ y) = h y := (hharm y).symm
        simp_rw [hk]
        exact ih
  have hirr' := (Kernel.isIrreducible_count_iff_forall_canReach κ).1 hirr
  intro x
  obtain ⟨n, hreach⟩ := hirr' a x
  have htotal : (∫⁻ y, h y ∂(κ ^ n) a) = 0 := by
    rw [hpow n a]
    exact neverHitIncluding_self κ a
  have hmul : h x * (κ ^ n) a {x} = 0 := by
    apply le_antisymm
    · calc
        h x * (κ ^ n) a {x} = ∫⁻ y in {x}, h y ∂(κ ^ n) a := by
            rw [lintegral_singleton]
        _ ≤ ∫⁻ y, h y ∂(κ ^ n) a := setLIntegral_le_lintegral _ _
        _ = 0 := htotal
    · exact bot_le
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx | hmass
  · exact hx
  · exact False.elim (ne_of_gt hreach hmass)

/-! ### Semantic identification with the canonical path law -/

theorem setIntegral_partialTraj_transitionProbability_beforeReturnHistory_from
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in beforeReturnHistory target n,
        transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 n (fun _ => start) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeReturnHistory target n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) A y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) := by
  have hnext : MeasurableSet {z : ℕ → E | z (n + 1) ∈ A} :=
    (measurable_pi_apply (n + 1)) hA
  have hf : Integrable (eventIndicator (fun z : ℕ → E => z (n + 1)) A)
      (Kernel.traj (X := fun _ : ℕ => E)
        (markovChainStep κ) 0 (fun _ => start)) := by
    change Integrable ({z : ℕ → E | z (n + 1) ∈ A}.indicator
      (fun _ => (1 : ℝ))) _
    exact (integrable_const (1 : ℝ)).indicator hnext
  have htraj := Kernel.setIntegral_traj_partialTraj
    (κ := markovChainStep κ) (a := 0) (b := n) (Nat.zero_le n)
    (x₀ := fun _ => start)
    (f := eventIndicator (fun z : ℕ → E => z (n + 1)) A) hf
    (measurableSet_beforeReturnHistory target n)
  have hinner :
      (fun z : (i : Finset.Iic n) → E =>
          ∫ y, eventIndicator (fun w : ℕ → E => w (n + 1)) A y
            ∂Kernel.traj (markovChainStep κ) n z) =
        fun z => transitionProbability κ
          (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A := by
    funext z
    exact integral_eventIndicator_traj_succ κ n z hA
  rw [hinner] at htraj
  exact htraj

theorem setIntegral_transitionProbability_beforeReturn_preimage_from
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in Preorder.frestrictLe n ⁻¹' beforeReturnHistory target n,
        transitionProbability κ (z n) A
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeReturnHistory target n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) A y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => start) := by
  have hfinite :=
    setIntegral_partialTraj_transitionProbability_beforeReturnHistory_from
      κ start target n hA
  have hmap := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => E) (κ := markovChainStep κ) 0 n (fun _ => start)
  rw [← hmap] at hfinite
  have htrans : Measurable (fun z : (i : Finset.Iic n) → E =>
      transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A) :=
    ((κ.measurable_coe hA).ennreal_toReal.comp (measurable_pi_apply _))
  rw [setIntegral_map (measurableSet_beforeReturnHistory target n)
    htrans.aestronglyMeasurable
    (Preorder.measurable_frestrictLe n).aemeasurable] at hfinite
  simpa only [Preorder.frestrictLe_apply] using hfinite

theorem setIntegral_transitionProbability_beforeReturn_from
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in beforeReturnEvent target n, transitionProbability κ (z n) A
        ∂markovChainLaw κ start =
      (markovChainLaw κ start).real
        (beforeReturnEvent target n ∩ {z : ℕ → E | z (n + 1) ∈ A}) := by
  have h := setIntegral_transitionProbability_beforeReturn_preimage_from
    κ start target n hA
  rw [← beforeReturnEvent_eq_preimage_history target n] at h
  rw [← markovChainLaw_eq_traj κ start] at h
  rw [setIntegral_eventIndicator_coordinate_eq_real
    (markovChainLaw κ start) (beforeReturnEvent target n) (n + 1) hA] at h
  exact h

theorem setLIntegral_transition_beforeReturn_from
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ z in beforeReturnEvent target n, κ (z n) A ∂markovChainLaw κ start =
      markovChainLaw κ start
        (beforeReturnEvent target n ∩ {z : ℕ → E | z (n + 1) ∈ A}) := by
  let μ := markovChainLaw κ start
  let B := beforeReturnEvent target n
  let L : ℝ≥0∞ := ∫⁻ z in B, κ (z n) A ∂μ
  let R : ℝ≥0∞ := μ (B ∩ {z : ℕ → E | z (n + 1) ∈ A})
  have hmeas : AEMeasurable (fun z : ℕ → E => κ (z n) A) (μ.restrict B) :=
    ((κ.measurable_coe hA).comp (measurable_pi_apply n)).aemeasurable
  have hpoint : ∀ᵐ z ∂μ.restrict B, κ (z n) A < ∞ :=
    Filter.Eventually.of_forall fun _z =>
      lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  have hL_le : L ≤ 1 := by
    calc
      L ≤ ∫⁻ _z in B, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun _z => prob_le_one
      _ = μ B := by simp [B]
      _ ≤ 1 := prob_le_one
  have hR_le : R ≤ 1 := prob_le_one
  apply (ENNReal.toReal_eq_toReal_iff'
    (ne_of_lt (hL_le.trans_lt ENNReal.one_lt_top))
    (ne_of_lt (hR_le.trans_lt ENNReal.one_lt_top))).mp
  rw [show L.toReal = ∫ z in B, transitionProbability κ (z n) A ∂μ by
    change L.toReal = ∫ z in B, (κ (z n) A).toReal ∂μ
    exact (integral_toReal hmeas hpoint).symm]
  simpa [μ, B, R, Measure.real] using
    setIntegral_transitionProbability_beforeReturn_from κ start target n hA

/-- Distribution at time `n`, restricted to paths which avoided `target` at times `1,...,n`. -/
noncomputable def avoidanceTermMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ) : Measure E :=
  Measure.map (fun ω : ℕ → E => ω n)
    ((markovChainLaw κ start).restrict (beforeReturnEvent target n))

theorem avoidanceTermMeasure_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    avoidanceTermMeasure κ start target n A =
      markovChainLaw κ start
        (beforeReturnEvent target n ∩ {ω | ω n ∈ A}) := by
  rw [avoidanceTermMeasure, Measure.map_apply (measurable_pi_apply n) hA,
    Measure.restrict_apply]
  · congr 1
    ext ω
    simp [and_comm]
  · exact (measurable_pi_apply n) hA

theorem avoidanceTermMeasure_zero
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) :
    avoidanceTermMeasure κ start target 0 = Measure.dirac start := by
  apply Measure.ext_of_singleton
  intro y
  rw [avoidanceTermMeasure_apply κ start target 0 (measurableSet_singleton y),
    beforeReturnEvent_zero, Set.univ_inter,
    markovChainLaw_apply_coordinate κ start 0 (measurableSet_singleton y), pow_zero]
  rfl

theorem avoidanceTermMeasure_succ_apply_of_ne
    (κ : Kernel E E) [IsMarkovKernel κ]
    (start target y : E) (hyt : y ≠ target) (n : ℕ) :
    avoidanceTermMeasure κ start target (n + 1) {y} =
      (κ ∘ₘ avoidanceTermMeasure κ start target n) {y} := by
  rw [avoidanceTermMeasure_apply κ start target (n + 1)
    (measurableSet_singleton y)]
  simp only [Set.mem_singleton_iff]
  rw [beforeReturnEvent_inter_coordinate_succ_of_ne target y hyt n |>.symm]
  have hstep := setLIntegral_transition_beforeReturn_from κ start target n
    (measurableSet_singleton y)
  simp only [Set.mem_singleton_iff] at hstep
  rw [← hstep]
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable]
  rw [avoidanceTermMeasure]
  rw [lintegral_map
    (κ.measurable_coe (measurableSet_singleton y))
    (measurable_pi_apply n)]

theorem avoidanceTermMeasure_succ_apply_target
    (κ : Kernel E E) [IsMarkovKernel κ]
    (start target : E) (n : ℕ) :
    avoidanceTermMeasure κ start target (n + 1) {target} = 0 := by
  rw [avoidanceTermMeasure_apply κ start target (n + 1)
    (measurableSet_singleton target)]
  simpa only [Set.mem_singleton_iff, measure_empty] using congrArg
    (markovChainLaw κ start)
    (beforeReturnEvent_inter_coordinate_self_succ (E := E) target n)

theorem avoidanceTermMeasure_succ
    (κ : Kernel E E) [IsMarkovKernel κ]
    (start target : E) (n : ℕ) :
    avoidanceTermMeasure κ start target (n + 1) =
      killedKernel κ target ∘ₘ avoidanceTermMeasure κ start target n := by
  apply Measure.ext_of_singleton
  intro y
  by_cases hyt : y = target
  · subst y
    rw [avoidanceTermMeasure_succ_apply_target]
    rw [Measure.bind_apply (measurableSet_singleton target)
      (killedKernel κ target).aemeasurable]
    symm
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun z => by
      change killedKernel κ target z {target} = 0
      rw [killedKernel, Kernel.restrict_apply,
        Measure.restrict_apply (measurableSet_singleton target)]
      simp
  · rw [avoidanceTermMeasure_succ_apply_of_ne κ start target y hyt n]
    rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable,
      Measure.bind_apply (measurableSet_singleton y)
        (killedKernel κ target).aemeasurable]
    apply lintegral_congr
    intro z
    rw [killedKernel, Kernel.restrict_apply,
      Measure.restrict_apply (measurableSet_singleton y)]
    simp [hyt]

theorem avoidanceTermMeasure_eq_killed_pow
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) :
    ∀ n : ℕ, avoidanceTermMeasure κ start target n =
      (killedKernel κ target ^ n) start
  | 0 => by
      rw [avoidanceTermMeasure_zero, pow_zero]
      rfl
  | n + 1 => by
      rw [avoidanceTermMeasure_succ,
        avoidanceTermMeasure_eq_killed_pow κ start target n, pow_succ']
      rfl

theorem markovChainLaw_beforeReturnEvent_eq_survivalMass
    (κ : Kernel E E) [IsMarkovKernel κ] (start target : E) (n : ℕ) :
    markovChainLaw κ start (beforeReturnEvent target n) =
      survivalMass κ target n start := by
  have huniv := avoidanceTermMeasure_apply κ start target n MeasurableSet.univ
  simp only [Set.mem_univ, Set.setOf_true, Set.inter_univ] at huniv
  rw [avoidanceTermMeasure_eq_killed_pow κ start target n] at huniv
  exact huniv.symm

theorem iInf_survivalMass_eq_lintegral_neverHitIncluding
    (κ : Kernel E E) [IsMarkovKernel κ] (target start : E) :
    (⨅ n : ℕ, survivalMass κ target n start) =
      ∫⁻ y, neverHitIncluding κ target y ∂κ start := by
  have hmeas (n : ℕ) : Measurable (survivalMass κ target n) :=
    measurable_of_countable _
  have hanti : Antitone (fun n : ℕ => survivalMass κ target n) := by
    intro m n hmn y
    exact antitone_survivalMass κ target y hmn
  have hfin : (∫⁻ y in {target}ᶜ, survivalMass κ target 0 y ∂κ start) ≠ ∞ := by
    have hzero : survivalMass κ target 0 = fun _ => (1 : ℝ≥0∞) := by
      funext y
      rw [survivalMass, pow_zero]
      change Kernel.id y Set.univ = 1
      simp
    apply ne_of_lt
    calc
      (∫⁻ y in {target}ᶜ, survivalMass κ target 0 y ∂κ start) =
          κ start ({target}ᶜ) := by rw [hzero]; simp
      _ ≤ κ start Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ∞ := ENNReal.one_lt_top
  calc
    (⨅ n : ℕ, survivalMass κ target n start) =
        ⨅ n : ℕ, survivalMass κ target (n + 1) start :=
      (iInf_survivalMass_succ κ target start).symm
    _ = ⨅ n : ℕ, ∫⁻ y in {target}ᶜ, survivalMass κ target n y ∂κ start := by
      simp only [survivalMass_succ]
    _ = ∫⁻ y in {target}ᶜ, ⨅ n : ℕ, survivalMass κ target n y ∂κ start := by
      rw [lintegral_iInf (μ := (κ start).restrict {target}ᶜ) hmeas hanti hfin]
    _ = ∫⁻ y, neverHitIncluding κ target y ∂κ start := by
      rw [← lintegral_indicator (measurableSet_singleton target).compl]
      apply lintegral_congr
      intro y
      by_cases hyt : y = target
      · simp [hyt, neverHitIncluding]
      · simp [hyt, neverHitIncluding]

theorem measurableSet_beforeReturnEvent' (target : E) (n : ℕ) :
    MeasurableSet (beforeReturnEvent target n) := by
  rw [beforeReturnEvent_eq_preimage_history]
  exact (measurableSet_beforeReturnHistory target n).preimage
    (Preorder.measurable_frestrictLe n)

theorem antitone_beforeReturnEvent (target : E) :
    Antitone (beforeReturnEvent target) := by
  intro m n hmn ω hn
  change (n : WithTop ℕ) < firstPositiveHittingTime
    (fun k (z : ℕ → E) => z k) {target} ω at hn
  change (m : WithTop ℕ) < firstPositiveHittingTime
    (fun k (z : ℕ → E) => z k) {target} ω
  exact (WithTop.coe_le_coe.mpr hmn).trans_lt hn

/-- Event that `target` is hit at a strictly positive finite time. -/
def positiveHitEvent (target : E) : Set (ℕ → E) :=
  {ω | firstPositiveHittingTime (fun n z => z n) {target} ω < (⊤ : ℕ∞)}

theorem compl_positiveHitEvent_eq_iInter_beforeReturn (target : E) :
    (positiveHitEvent target)ᶜ =
      ⋂ n : ℕ, beforeReturnEvent target n := by
  ext ω
  simp only [positiveHitEvent, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iInter,
    beforeReturnEvent, Set.mem_ofPred_eq]
  let τ := firstPositiveHittingTime (fun n (z : ℕ → E) => z n) {target} ω
  cases hτ : τ with
  | top =>
      constructor
      · intro _h n
        simpa [τ, hτ] using ENat.natCast_lt_top n
      · intro _h hlt
        exact (not_lt_of_ge (show (⊤ : ℕ∞) ≤ ⊤ from le_rfl))
          (by simpa [τ, hτ] using hlt)
  | coe k =>
      constructor
      · intro h
        exact False.elim (h (by simpa [τ, hτ] using ENat.natCast_lt_top k))
      · intro h
        exact False.elim (lt_irrefl (k : ℕ∞) (by simpa [τ, hτ] using h k))

theorem measurableSet_iInter_beforeReturnEvent (target : E) :
    MeasurableSet (⋂ n : ℕ, beforeReturnEvent target n) := by
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_beforeReturnEvent' target n

theorem measurableSet_positiveHitEvent (target : E) :
    MeasurableSet (positiveHitEvent target) := by
  rw [positiveHitEvent]
  rw [← iUnion_firstReturnSlice target]
  exact MeasurableSet.iUnion (measurableSet_firstReturnSlice target)

theorem returnProbability_eq_one_of_irreducible_invariant
    (κ : Kernel E E) [IsMarkovKernel κ]
    (π : Measure E) [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ)
    (start target : E) :
    returnProbability κ start target = 1 := by
  have hsurvival_zero : (⨅ n : ℕ, survivalMass κ target n start) = 0 := by
    rw [iInf_survivalMass_eq_lintegral_neverHitIncluding]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun y =>
      neverHitIncluding_eq_zero_of_irreducible_invariant κ target π hπ hirr y
  have hnever : markovChainLaw κ start
      (⋂ n : ℕ, beforeReturnEvent target n) = 0 := by
    rw [antitone_beforeReturnEvent target |>.measure_iInter
      (fun n => (measurableSet_beforeReturnEvent' target n).nullMeasurableSet)
      ⟨0, measure_ne_top (markovChainLaw κ start) _⟩]
    simp_rw [markovChainLaw_beforeReturnEvent_eq_survivalMass κ start target]
    exact hsurvival_zero
  have hcompl_zero : markovChainLaw κ start (positiveHitEvent target)ᶜ = 0 := by
    exact (congrArg (markovChainLaw κ start)
      (compl_positiveHitEvent_eq_iInter_beforeReturn target)).trans hnever
  have hone_le : 1 ≤ markovChainLaw κ start (positiveHitEvent target) := by
    have hcomp := measure_compl (measurableSet_positiveHitEvent (E := E) target)
      (measure_ne_top (markovChainLaw κ start) (positiveHitEvent target))
    rw [measure_univ] at hcomp
    rw [hcompl_zero] at hcomp
    exact tsub_eq_zero_iff_le.mp hcomp.symm
  apply le_antisymm
  · exact returnProbability_le_one κ start target
  · simpa [returnProbability, positiveHitEvent] using hone_le

end

end ProbabilityTheory
