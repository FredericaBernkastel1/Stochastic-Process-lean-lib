/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Green

/-!
# Excursion occupation measure

The construction is a countable sum of pushforwards of restricted path laws.  It does not rebuild a
measure from singleton weights, and it keeps the infinite-return event in the underlying extended
stopping-time semantics.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Event that the strict-positive return to `x` occurs after time `n`. -/
def beforeReturnEvent (x : E) (n : ℕ) : Set (ℕ → E) :=
  {ω | (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω}

/-- Finite-history form of the event of avoiding `x` at positive times through `n`. -/
def beforeReturnHistory (x : E) (n : ℕ) : Set ((i : Finset.Iic n) → E) :=
  {z | ∀ j : Finset.Iic n, 1 ≤ (j : ℕ) → z j ≠ x}

/-- Pointwise characterization of the strict-return tail event. -/
theorem mem_beforeReturnEvent_iff (x : E) (n : ℕ) (ω : ℕ → E) :
    ω ∈ beforeReturnEvent x n ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ n → ω j ≠ x := by
  have hle :
      firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω ≤ (n : ℕ∞) ↔
        ∃ j : ℕ, j ∈ Set.Icc 1 n ∧ ω j ∈ ({x} : Set E) := by
    change hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω ≤ (n : WithTop ℕ) ↔ _
    exact hittingAfter_le_iff
  constructor
  · intro h j hj₁ hjn hjx
    exact (not_lt_of_ge (hle.mpr ⟨j, ⟨hj₁, hjn⟩, by simpa using hjx⟩)) h
  · intro h
    rw [beforeReturnEvent, Set.mem_ofPred_eq, lt_iff_not_ge]
    intro hret
    obtain ⟨j, hj, hjx⟩ := hle.mp hret
    exact h j hj.1 hj.2 (by simpa using hjx)

/-- The finite-history avoidance set is measurable. -/
theorem measurableSet_beforeReturnHistory (x : E) (n : ℕ) :
    MeasurableSet (beforeReturnHistory x n) := by
  let J : Type := {j : ℕ // j ∈ Set.Icc 1 n}
  have hrepr : beforeReturnHistory x n =
      (⋃ j : J, {z : (i : Finset.Iic n) → E |
        z ⟨j, Finset.mem_Iic.mpr j.property.2⟩ = x})ᶜ := by
    ext z
    simp only [beforeReturnHistory, Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_iUnion, not_exists]
    constructor
    · intro h j hjx
      exact h ⟨j, Finset.mem_Iic.mpr j.property.2⟩ j.property.1 hjx
    · intro h j hj₁ hjx
      exact h ⟨j, ⟨hj₁, Finset.mem_Iic.mp j.property⟩⟩ hjx
  rw [hrepr]
  exact (MeasurableSet.iUnion fun j : J =>
    (show MeasurableSet ((fun z : (i : Finset.Iic n) → E =>
        z (⟨j, Finset.mem_Iic.mpr j.property.2⟩ : Finset.Iic n)) ⁻¹' {x}) from
      (measurable_pi_apply (⟨j, Finset.mem_Iic.mpr j.property.2⟩ : Finset.Iic n))
        (measurableSet_singleton x))).compl

/-- Avoidance through time `n` is precisely the pullback of the finite-history avoidance set. -/
theorem beforeReturnEvent_eq_preimage_history (x : E) (n : ℕ) :
    beforeReturnEvent x n =
      Preorder.frestrictLe n ⁻¹' beforeReturnHistory x n := by
  ext ω
  rw [mem_beforeReturnEvent_iff]
  constructor
  · intro h j hj₁
    exact h j hj₁ (Finset.mem_Iic.mp j.property)
  · intro h j hj₁ hjn
    exact h ⟨j, Finset.mem_Iic.mpr hjn⟩ hj₁

/-- The slice on which the first strict-positive return to `x` occurs at time `n + 1`. -/
def firstReturnSlice (x : E) (n : ℕ) : Set (ℕ → E) :=
  beforeReturnEvent x n ∩ {ω | ω (n + 1) = x}

/-- Return slices are measurable cylinder-tail intersections. -/
theorem measurableSet_firstReturnSlice (x : E) (n : ℕ) :
    MeasurableSet (firstReturnSlice x n) := by
  apply (measurableSet_firstPositiveHittingTime_gt x n).inter
  change MeasurableSet ((fun ω : ℕ → E => ω (n + 1)) ⁻¹' ({x} : Set E))
  exact (measurable_pi_apply (n + 1)) (measurableSet_singleton x)

/-- Finite-history form of the slice on which the first strict return occurs at time `n + 1`. -/
def firstReturnSliceHistory (x : E) (n : ℕ) :
    Set ((i : Finset.Iic (n + 1)) → E) :=
  Preorder.frestrictLe₂ (π := fun _ : ℕ => E) n.le_succ ⁻¹' beforeReturnHistory x n ∩
    {z | z ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ = x}

/-- The finite-history first-return slice is measurable. -/
theorem measurableSet_firstReturnSliceHistory (x : E) (n : ℕ) :
    MeasurableSet (firstReturnSliceHistory x n) := by
  apply (measurableSet_beforeReturnHistory x n).preimage
    (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => E) n.le_succ) |>.inter
  exact (@measurable_pi_apply (Finset.Iic (n + 1)) (fun _ => E) _
    ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) (measurableSet_singleton x)

/-- A path belongs to a first-return slice exactly when its history through the return time does. -/
theorem firstReturnSlice_eq_preimage_history_succ (x : E) (n : ℕ) :
    firstReturnSlice x n =
      Preorder.frestrictLe (n + 1) ⁻¹' firstReturnSliceHistory x n := by
  rw [firstReturnSlice, beforeReturnEvent_eq_preimage_history]
  ext ω
  change
    Preorder.frestrictLe n ω ∈ beforeReturnHistory x n ∧ ω (n + 1) = x ↔
      Preorder.frestrictLe₂ n.le_succ (Preorder.frestrictLe (n + 1) ω) ∈
          beforeReturnHistory x n ∧ ω (n + 1) = x
  rw [show Preorder.frestrictLe₂ n.le_succ (Preorder.frestrictLe (n + 1) ω) =
      Preorder.frestrictLe n ω by rfl]

/-- A first-return slice is measurable with respect to the finite-history sigma-field at its
return time. -/
theorem measurableSet_firstReturnSlice_piLE (x : E) (n : ℕ) :
    @MeasurableSet (ℕ → E) (Filtration.piLE (X := fun _ : ℕ => E) (n + 1))
      (firstReturnSlice x n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe,
    firstReturnSlice_eq_preimage_history_succ x n]
  exact ⟨firstReturnSliceHistory x n,
    measurableSet_firstReturnSliceHistory x n, rfl⟩

/-- Finite-trajectory version of the one-step renewal identity. -/
theorem setIntegral_partialTraj_transitionProbability_beforeReturnHistory
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in beforeReturnHistory x n,
        transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 n (fun _ => x) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeReturnHistory x n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) A y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => x) := by
  have hnext : MeasurableSet {z : ℕ → E | z (n + 1) ∈ A} :=
    (measurable_pi_apply (n + 1)) hA
  have hf : Integrable (eventIndicator (fun z : ℕ → E => z (n + 1)) A)
      (Kernel.traj (X := fun _ : ℕ => E)
        (markovChainStep κ) 0 (fun _ => x)) := by
    change Integrable ({z : ℕ → E | z (n + 1) ∈ A}.indicator
      (fun _ => (1 : ℝ))) _
    exact (integrable_const (1 : ℝ)).indicator hnext
  have htraj := Kernel.setIntegral_traj_partialTraj
    (κ := markovChainStep κ) (a := 0) (b := n) (Nat.zero_le n)
    (x₀ := fun _ => x)
    (f := eventIndicator (fun z : ℕ → E => z (n + 1)) A) hf
    (measurableSet_beforeReturnHistory x n)
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

/-- Pulling the finite renewal identity back to the canonical path space. -/
theorem setIntegral_transitionProbability_beforeReturn_preimage
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in Preorder.frestrictLe n ⁻¹' beforeReturnHistory x n,
        transitionProbability κ (z n) A
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => x) =
      ∫ y in Preorder.frestrictLe n ⁻¹' beforeReturnHistory x n,
        eventIndicator (fun z : ℕ → E => z (n + 1)) A y
        ∂Kernel.traj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (fun _ => x) := by
  have hfinite :=
    setIntegral_partialTraj_transitionProbability_beforeReturnHistory κ x n hA
  have hmap := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => E) (κ := markovChainStep κ) 0 n (fun _ => x)
  rw [← hmap] at hfinite
  have htrans : Measurable (fun z : (i : Finset.Iic n) → E =>
      transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A) :=
    ((κ.measurable_coe hA).ennreal_toReal.comp (measurable_pi_apply _))
  rw [setIntegral_map (measurableSet_beforeReturnHistory x n)
    htrans.aestronglyMeasurable
    (Preorder.measurable_frestrictLe n).aemeasurable] at hfinite
  simpa only [Preorder.frestrictLe_apply] using hfinite

/-- Integrating a coordinate-event indicator over a restricted path law gives the real mass of
the corresponding intersection. -/
theorem setIntegral_eventIndicator_coordinate_eq_real
    (μ : Measure (ℕ → E)) [IsFiniteMeasure μ] (B : Set (ℕ → E))
    (m : ℕ) {A : Set E} (hA : MeasurableSet A) :
    ∫ z in B, eventIndicator (fun w : ℕ → E => w m) A z ∂μ =
      μ.real (B ∩ {z : ℕ → E | z m ∈ A}) := by
  have hcoordinate : MeasurableSet {z : ℕ → E | z m ∈ A} :=
    (measurable_pi_apply m) hA
  rw [show eventIndicator (fun w : ℕ → E => w m) A =
      {z : ℕ → E | z m ∈ A}.indicator (fun _ => (1 : ℝ)) by rfl,
    setIntegral_indicator hcoordinate, integral_const,
    measureReal_restrict_apply_univ]
  simp only [smul_eq_mul, mul_one]

/-- The finite partial trajectory assigns a first-return history the same real mass as the
corresponding cylinder event under the canonical path law. -/
theorem partialTraj_firstReturnSliceHistory_real
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (k : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => E)
        (markovChainStep κ) 0 (k + 1) (fun _ => x)).real
        (firstReturnSliceHistory x k) =
      (markovChainLaw κ x).real (firstReturnSlice x k) := by
  have hmap := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => E) (κ := markovChainStep κ) 0 (k + 1) (fun _ => x)
  rw [← hmap, Measure.real,
    Measure.map_apply (Preorder.measurable_frestrictLe (k + 1))
      (measurableSet_firstReturnSliceHistory x k)]
  rw [firstReturnSlice_eq_preimage_history_succ x k]
  rw [← markovChainLaw_eq_traj κ x]
  rfl

/-- After a first return at time `k + 1`, the integral of the endpoint event `n` steps later
factors through the `n`-step return probability. -/
theorem setIntegral_partialTraj_firstReturnSliceHistory
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (k n : ℕ) :
    ∫ z in firstReturnSliceHistory x k,
        (∫ y, eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
          ∂Kernel.traj (markovChainStep κ) (k + 1) z)
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x) =
      (Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x)).real
          (firstReturnSliceHistory x k) *
        transitionProbability (κ ^ n) x {x} := by
  rw [show (∫ z in firstReturnSliceHistory x k,
      (∫ y, eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
        ∂Kernel.traj (markovChainStep κ) (k + 1) z)
      ∂Kernel.partialTraj (X := fun _ : ℕ => E)
        (markovChainStep κ) 0 (k + 1) (fun _ => x)) =
      ∫ _z in firstReturnSliceHistory x k,
        transitionProbability (κ ^ n) x {x}
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x) by
    apply setIntegral_congr_fun (measurableSet_firstReturnSliceHistory x k)
    intro z hz
    change (∫ y, eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n))
      ({x} : Set E) y ∂Kernel.traj (markovChainStep κ) (k + 1) z) =
        transitionProbability (κ ^ n) x {x}
    rw [integral_eventIndicator_traj_add κ (k + 1) n z
      (measurableSet_singleton x)]
    exact congrArg (fun y => transitionProbability (κ ^ n) y {x}) hz.2]
  rw [setIntegral_const]
  simp only [smul_eq_mul]

/-- The finite-trajectory disintegration formula specialized to a first-return slice and a future
endpoint event. -/
theorem setIntegral_firstReturnSlice_endpoint
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (k n : ℕ) :
    ∫ y in firstReturnSlice x k,
        eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
        ∂markovChainLaw κ x =
      ∫ z in firstReturnSliceHistory x k,
        (∫ y, eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
          ∂Kernel.traj (markovChainStep κ) (k + 1) z)
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x) := by
  have hf : Integrable
      (eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E))
      (Kernel.traj (X := fun _ : ℕ => E) (markovChainStep κ) 0 (fun _ => x)) := by
    change Integrable
      ({ω : ℕ → E | ω ((k + 1) + n) ∈ ({x} : Set E)}.indicator (fun _ => (1 : ℝ))) _
    exact (integrable_const (1 : ℝ)).indicator
      ((measurable_pi_apply ((k + 1) + n)) (measurableSet_singleton x))
  rw [markovChainLaw_eq_traj κ x,
    firstReturnSlice_eq_preimage_history_succ x k]
  exact (Kernel.setIntegral_traj_partialTraj
    (κ := markovChainStep κ) (a := 0) (b := k + 1) (Nat.zero_le (k + 1))
    (x₀ := fun _ => x)
    (f := eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E)) hf
    (measurableSet_firstReturnSliceHistory x k)).symm

/-- Real-valued first-return factorization: on the slice returning at `k + 1`, an endpoint event
`n` steps later has mass equal to the slice mass times the `n`-step return probability. -/
theorem markovChainLaw_firstReturnSlice_inter_coordinate_add_real
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (k n : ℕ) :
    (markovChainLaw κ x).real
        (firstReturnSlice x k ∩ {ω : ℕ → E | ω ((k + 1) + n) = x}) =
      (markovChainLaw κ x).real (firstReturnSlice x k) *
        transitionProbability (κ ^ n) x {x} := by
  calc
    _ = ∫ y in firstReturnSlice x k,
        eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
        ∂markovChainLaw κ x :=
      (setIntegral_eventIndicator_coordinate_eq_real
        (markovChainLaw κ x) (firstReturnSlice x k) ((k + 1) + n)
          (measurableSet_singleton x)).symm
    _ = ∫ z in firstReturnSliceHistory x k,
        (∫ y, eventIndicator (fun ω : ℕ → E => ω ((k + 1) + n)) ({x} : Set E) y
          ∂Kernel.traj (markovChainStep κ) (k + 1) z)
        ∂Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x) :=
      setIntegral_firstReturnSlice_endpoint κ x k n
    _ = (Kernel.partialTraj (X := fun _ : ℕ => E)
          (markovChainStep κ) 0 (k + 1) (fun _ => x)).real
          (firstReturnSliceHistory x k) *
        transitionProbability (κ ^ n) x {x} :=
      setIntegral_partialTraj_firstReturnSliceHistory κ x k n
    _ = _ := by rw [partialTraj_firstReturnSliceHistory_real κ x k]

/-- Extended-nonnegative first-return factorization. -/
theorem markovChainLaw_firstReturnSlice_inter_coordinate_add
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (k n : ℕ) :
    markovChainLaw κ x
        (firstReturnSlice x k ∩ {ω : ℕ → E | ω ((k + 1) + n) = x}) =
      markovChainLaw κ x (firstReturnSlice x k) * (κ ^ n) x {x} := by
  letI : IsMarkovKernel (κ ^ n) := isMarkovKernel_pow κ n
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (markovChainLaw κ x) _)
    (ENNReal.mul_ne_top (measure_ne_top (markovChainLaw κ x) _)
      (measure_ne_top ((κ ^ n) x) _))).mp
  rw [ENNReal.toReal_mul]
  exact markovChainLaw_firstReturnSlice_inter_coordinate_add_real κ x k n

/-- One-step Markov integration on the pre-return event.  This is the renewal identity used by
the excursion-invariance proof. -/
theorem setIntegral_transitionProbability_beforeReturn
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫ z in beforeReturnEvent x n, transitionProbability κ (z n) A
        ∂markovChainLaw κ x =
      (markovChainLaw κ x).real
        (beforeReturnEvent x n ∩ {z : ℕ → E | z (n + 1) ∈ A}) := by
  have h := setIntegral_transitionProbability_beforeReturn_preimage κ x n hA
  rw [← beforeReturnEvent_eq_preimage_history x n] at h
  rw [← markovChainLaw_eq_traj κ x] at h
  rw [setIntegral_eventIndicator_coordinate_eq_real
    (markovChainLaw κ x) (beforeReturnEvent x n) (n + 1) hA] at h
  exact h

/-- Extended-nonnegative form of the one-step renewal identity. -/
theorem setLIntegral_transition_beforeReturn
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ z in beforeReturnEvent x n, κ (z n) A ∂markovChainLaw κ x =
      markovChainLaw κ x
        (beforeReturnEvent x n ∩ {z : ℕ → E | z (n + 1) ∈ A}) := by
  let μ := markovChainLaw κ x
  let B := beforeReturnEvent x n
  let L : ℝ≥0∞ := ∫⁻ z in B, κ (z n) A ∂μ
  let R : ℝ≥0∞ := μ (B ∩ {z : ℕ → E | z (n + 1) ∈ A})
  have hmeas : AEMeasurable (fun z : ℕ → E => κ (z n) A) (μ.restrict B) :=
    ((κ.measurable_coe hA).comp (measurable_pi_apply n)).aemeasurable
  have hpoint : ∀ᵐ z ∂μ.restrict B, κ (z n) A < ∞ :=
    Filter.Eventually.of_forall fun z =>
      lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  have hL_le : L ≤ 1 := by
    calc
      L ≤ ∫⁻ _z in B, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono fun z => prob_le_one
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
    setIntegral_transitionProbability_beforeReturn κ x n hA

/-- Membership in a return slice is equivalent to an exact finite return time. -/
theorem mem_firstReturnSlice_iff (x : E) (n : ℕ) (ω : ℕ → E) :
    ω ∈ firstReturnSlice x n ↔
      firstPositiveHittingTime (fun k z => z k) {x} ω = (↑(n + 1) : ℕ∞) := by
  let τ := firstPositiveHittingTime (fun k z => z k) {x} ω
  constructor
  · intro h
    have hnτ : (n : ℕ∞) < τ := h.1
    have hτle : τ ≤ (n + 1 : ℕ∞) := by
      change hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω ≤
        (n + 1 : WithTop ℕ)
      exact hittingAfter_le_of_mem (Nat.succ_le_succ (Nat.zero_le n)) (by simpa using h.2)
    have hτtop : τ ≠ ⊤ := ne_top_of_le_ne_top (by simp) hτle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτtop
    have hnk : n < k := WithTop.coe_lt_coe.mp (hk ▸ hnτ)
    have hkle : k ≤ n + 1 := WithTop.coe_le_coe.mp (hk ▸ hτle)
    have hkeq : k = n + 1 := Nat.le_antisymm hkle (Nat.succ_le_iff.mpr hnk)
    exact hk.symm.trans (congrArg (fun j : ℕ => (j : ℕ∞)) hkeq)
  · intro hτ
    constructor
    · change (n : ℕ∞) < firstPositiveHittingTime (fun k z => z k) {x} ω
      rw [hτ]
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)
    · have hne : firstPositiveHittingTime (fun k z => z k) {x} ω ≠ ⊤ :=
        hτ ▸ (WithTop.coe_ne_top : (↑(n + 1) : ℕ∞) ≠ ⊤)
      have hmem := hittingAfter_mem_set_of_ne_top
        (u := fun k (z : ℕ → E) => z k) (s := ({x} : Set E)) (n := 1)
        (ω := ω) hne
      change ω (hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω).untopA = x at hmem
      change hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω =
        (↑(n + 1) : WithTop ℕ) at hτ
      rw [hτ] at hmem
      rw [WithTop.untopA_eq_untop (by simp)] at hmem
      have huntop : (↑n + 1 : WithTop ℕ).untop (by simp) = n + 1 := by
        apply WithTop.coe_injective
        rw [WithTop.coe_untop]
        simp
      simpa [huntop] using hmem

/-- Different exact return-time slices are disjoint. -/
theorem pairwise_disjoint_firstReturnSlice (x : E) :
    Pairwise (Disjoint on firstReturnSlice x) := by
  intro n m hnm
  change Disjoint (firstReturnSlice x n) (firstReturnSlice x m)
  rw [Set.disjoint_left]
  intro ω hn hm
  have hn' := (mem_firstReturnSlice_iff x n ω).mp hn
  have hm' := (mem_firstReturnSlice_iff x m ω).mp hm
  apply hnm
  exact Nat.succ.inj (WithTop.coe_eq_coe.mp (hn'.symm.trans hm'))

/-- The union of the exact return-time slices is the finite-return event. -/
theorem iUnion_firstReturnSlice (x : E) :
    (⋃ n : ℕ, firstReturnSlice x n) =
      {ω : ℕ → E |
        firstPositiveHittingTime (fun k z => z k) {x} ω < (⊤ : ℕ∞)} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, mem_firstReturnSlice_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [hn]
    exact ENat.natCast_lt_top _
  · intro hfinite
    have hne : firstPositiveHittingTime (fun k z => z k) {x} ω ≠ (⊤ : ℕ∞) :=
      ne_of_lt hfinite
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hkpos : 1 ≤ k := by
      exact WithTop.coe_le_coe.mp (hk ▸ one_le_firstPositiveHittingTime
        (fun k (z : ℕ → E) => z k) {x} ω)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hkpos))
    exact ⟨n, hk.symm⟩

/-- The total mass of all exact return slices is the strict return probability. -/
theorem tsum_firstReturnSlice_eq_returnProbability
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    ∑' n : ℕ, markovChainLaw κ x (firstReturnSlice x n) =
      returnProbability κ x x := by
  rw [← MeasureTheory.measure_iUnion (pairwise_disjoint_firstReturnSlice x)
    (measurableSet_firstReturnSlice x), iUnion_firstReturnSlice, returnProbability]
  apply congrArg (markovChainLaw κ x)
  ext ω
  simp only [Set.mem_ofPred_eq]
  cases firstPositiveHittingTime (fun k z => z k) {x} ω using ENat.recTopCoe <;> simp

/-- A return at time `N + 1` is partitioned by the time of the first strict return. -/
theorem returnCoordinate_eq_biUnion_firstReturnSlice (x : E) (N : ℕ) :
    {ω : ℕ → E | ω (N + 1) = x} =
      ⋃ k ∈ Finset.range (N + 1),
        firstReturnSlice x k ∩ {ω : ℕ → E | ω (N + 1) = x} := by
  ext ω
  constructor
  · intro hω
    have hle :
        firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω ≤
          (N + 1 : ℕ∞) := by
      change hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω ≤
        (N + 1 : ℕ∞)
      exact hittingAfter_le_of_mem (Nat.succ_le_succ (Nat.zero_le N)) (by simpa using hω)
    have hne : firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω ≠ (⊤ : ℕ∞) :=
      ne_top_of_le_ne_top (by simp) hle
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hne
    have hjpos : 1 ≤ j := WithTop.coe_le_coe.mp
      (hj ▸ one_le_firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hjpos))
    have hkN : k ≤ N := Nat.succ_le_succ_iff.mp (WithTop.coe_le_coe.mp (hj ▸ hle))
    refine Set.mem_iUnion.2
      ⟨k, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hkN), ?_⟩⟩
    exact ⟨(mem_firstReturnSlice_iff x k ω).2 hj.symm, hω⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    rcases Set.mem_iUnion.1 hk with ⟨_hk, hkset⟩
    exact hkset.2

/-- The discrete Markov renewal equation for returns to a state. -/
theorem markovRenewalEquation
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (N : ℕ) :
    (κ ^ (N + 1)) x {x} =
      ∑ k ∈ Finset.range (N + 1),
        markovChainLaw κ x (firstReturnSlice x k) * (κ ^ (N - k)) x {x} := by
  rw [← markovChainLaw_apply_coordinate κ x (N + 1) (measurableSet_singleton x)]
  simp only [Set.mem_singleton_iff]
  rw [returnCoordinate_eq_biUnion_firstReturnSlice x N]
  rw [measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
    rw [show {ω : ℕ → E | ω (N + 1) = x} =
        {ω : ℕ → E | ω ((k + 1) + (N - k)) = x} by
      have htime : (k + 1) + (N - k) = N + 1 := by omega
      rw [htime]]
    exact markovChainLaw_firstReturnSlice_inter_coordinate_add κ x k (N - k)
  · intro k hk m hm hkm
    exact ((pairwise_disjoint_firstReturnSlice x) hkm).mono
      Set.inter_subset_left Set.inter_subset_left
  · intro k hk
    apply (measurableSet_firstReturnSlice x k).inter
    change MeasurableSet ((fun ω : ℕ → E => ω (N + 1)) ⁻¹' ({x} : Set E))
    exact (measurable_pi_apply (N + 1)) (measurableSet_singleton x)

theorem beforeReturnEvent_zero (x : E) :
    beforeReturnEvent x 0 = (Set.univ : Set (ℕ → E)) := by
  ext ω
  simp only [beforeReturnEvent, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact lt_of_lt_of_le (by simp) (one_le_firstPositiveHittingTime _ _ ω)

theorem beforeReturnEvent_inter_coordinate_self_succ (x : E) (n : ℕ) :
    beforeReturnEvent x (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = x} = ∅ := by
  ext ω
  constructor
  · intro hω
    have hle :
        firstPositiveHittingTime (fun k (z : ℕ → E) => z k) {x} ω ≤ (n + 1 : ℕ∞) := by
      change hittingAfter (fun k (z : ℕ → E) => z k) {x} 1 ω ≤ (n + 1 : WithTop ℕ)
      exact hittingAfter_le_of_mem (Nat.succ_le_succ (Nat.zero_le n)) (by simpa using hω.2)
    exact (not_lt_of_ge hle) hω.1
  · intro hω
    exact hω.elim

/-- At a state different from the base point, avoidance through `n` plus the next coordinate is
equivalent to avoidance through `n + 1` plus that coordinate. -/
theorem beforeReturnEvent_inter_coordinate_succ_of_ne
    (x y : E) (hxy : y ≠ x) (n : ℕ) :
    beforeReturnEvent x n ∩ {ω : ℕ → E | ω (n + 1) = y} =
      beforeReturnEvent x (n + 1) ∩ {ω : ℕ → E | ω (n + 1) = y} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_beforeReturnEvent_iff]
  constructor
  · rintro ⟨havoid, hcoord⟩
    refine ⟨?_, hcoord⟩
    intro j hj₁ hjle
    rcases Nat.lt_or_eq_of_le hjle with hjlt | rfl
    · exact havoid j hj₁ (Nat.lt_succ_iff.mp hjlt)
    · simpa [hcoord] using hxy
  · rintro ⟨havoid, hcoord⟩
    exact ⟨fun j hj₁ hjle => havoid j hj₁ (hjle.trans (Nat.le_succ n)), hcoord⟩

/-- The time-zero excursion term charges no state other than its starting point. -/
theorem markovChainLaw_beforeReturn_zero_coordinate_of_ne
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) (hxy : y ≠ x) :
    markovChainLaw κ x (beforeReturnEvent x 0 ∩ {ω : ℕ → E | ω 0 = y}) = 0 := by
  have hyx : x ≠ y := Ne.symm hxy
  rw [beforeReturnEvent_zero, Set.univ_inter]
  have hmarg := markovChainLaw_apply_coordinate κ x 0 (measurableSet_singleton y)
  simp only [Set.mem_singleton_iff] at hmarg
  rw [hmarg, pow_zero]
  change Kernel.id x {y} = 0
  rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
  simp [hyx]

/-- Excursion occupation measure: at time `n`, retain paths not yet returned and push them through
the `n`th coordinate, then sum over all `n`. -/
noncomputable def excursionOccupationMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Measure E :=
  Measure.sum fun n : ℕ =>
    Measure.map (fun ω : ℕ → E => ω n)
      ((markovChainLaw κ x).restrict (beforeReturnEvent x n))

/-- Tail-mass series naturally associated with an excursion. -/
noncomputable def excursionTailMass
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : ℝ≥0∞ :=
  ∑' n : ℕ, markovChainLaw κ x (beforeReturnEvent x n)

/-- The excursion tail series is exactly the extended mean return time. -/
theorem excursionTailMass_eq_meanReturnTime
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    excursionTailMass κ x = meanReturnTime κ x := by
  rw [excursionTailMass, meanReturnTime_eq_tsum_tail]
  rfl

/-- The total mass of the occupation measure is its return-time tail series. -/
theorem excursionOccupationMeasure_apply_univ
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    excursionOccupationMeasure κ x Set.univ = excursionTailMass κ x := by
  rw [excursionOccupationMeasure, excursionTailMass, Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ]
  simp [Measure.restrict_apply]

/-- The total mass of the excursion occupation measure is the mean return time. -/
theorem excursionOccupationMeasure_apply_univ_eq_meanReturnTime
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    excursionOccupationMeasure κ x Set.univ = meanReturnTime κ x := by
  rw [excursionOccupationMeasure_apply_univ, excursionTailMass_eq_meanReturnTime]

/-- Evaluation of the occupation measure on a measurable set. -/
theorem excursionOccupationMeasure_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) {A : Set E} (hA : MeasurableSet A) :
    excursionOccupationMeasure κ x A =
      ∑' n : ℕ, markovChainLaw κ x
        (beforeReturnEvent x n ∩ {ω | ω n ∈ A}) := by
  rw [excursionOccupationMeasure, Measure.sum_apply _ hA]
  apply tsum_congr
  intro n
  rw [Measure.map_apply (measurable_pi_apply n) hA,
    Measure.restrict_apply]
  · apply congrArg (markovChainLaw κ x)
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_comm]
  · exact (measurable_pi_apply n) hA

/-- A canonical excursion contains exactly one visit to its starting state: the time-zero visit. -/
theorem excursionOccupationMeasure_apply_singleton
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    excursionOccupationMeasure κ x {x} = 1 := by
  rw [excursionOccupationMeasure_apply κ x (measurableSet_singleton x)]
  rw [tsum_eq_single 0]
  · rw [beforeReturnEvent_zero, Set.univ_inter]
    have hmarg := markovChainLaw_apply_coordinate κ x 0 (measurableSet_singleton x)
    have hid : (κ ^ 0) x {x} = 1 := by
      rw [pow_zero]
      change Kernel.id x {x} = 1
      rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
      simp
    exact hmarg.trans hid
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hempty := beforeReturnEvent_inter_coordinate_self_succ (E := E) x m
    simp only [Set.mem_singleton_iff]
    rw [Nat.succ_eq_add_one, hempty]
    simp

end ProbabilityTheory
