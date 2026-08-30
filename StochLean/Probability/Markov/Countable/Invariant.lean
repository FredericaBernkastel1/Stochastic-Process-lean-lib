/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Renewal
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Invariant and normalized excursion measures

This module reuses `Kernel.Invariant`.  It supplies the general normalization bridge needed by the
excursion construction and exposes Kac's identity with the same extended-value convention as the
return-time layer.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace Kernel

variable {E : Type*} [MeasurableSpace E]

/-- Scalar multiples of invariant measures remain invariant. -/
theorem Invariant.smul {κ : Kernel E E} {μ : Measure E}
    (h : κ.Invariant μ) (c : ℝ≥0∞) : κ.Invariant (c • μ) := by
  rw [Invariant, Measure.comp_smul, h]

/-- Normalizing a finite nonzero invariant measure preserves invariance. -/
theorem Invariant.normalize [Nonempty E] {κ : Kernel E E} {μ : Measure E}
    (h : κ.Invariant μ) (hfin : μ Set.univ < ∞) (hne : μ ≠ 0) :
    κ.Invariant
      ((FiniteMeasure.normalize (⟨μ, ⟨hfin⟩⟩ : FiniteMeasure E) :
        ProbabilityMeasure E) : Measure E) := by
  let μf : FiniteMeasure E := ⟨μ, ⟨hfin⟩⟩
  change κ.Invariant ((FiniteMeasure.normalize μf : ProbabilityMeasure E) : Measure E)
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μf]
  · exact h.smul _
  · intro hz
    apply hne
    have hz' := congrArg FiniteMeasure.toMeasure hz
    simpa [μf] using hz'

end Kernel

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Applying the transition kernel to the excursion occupation measure shifts every retained path
coordinate forward by one. -/
theorem comp_excursionOccupationMeasure_apply_singleton
    (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    (κ ∘ₘ excursionOccupationMeasure κ x) {y} =
      ∑' n : ℕ, markovChainLaw κ x
        (beforeReturnEvent x n ∩ {ω : ℕ → E | ω (n + 1) = y}) := by
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable]
  rw [excursionOccupationMeasure, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_map (κ.measurable_coe (measurableSet_singleton y))
    (measurable_pi_apply n)]
  simpa only [Set.mem_singleton_iff] using
    setLIntegral_transition_beforeReturn κ x n (measurableSet_singleton y)

/-- Under recurrence at the base state, the shifted excursion series agrees with the original
occupation mass at every singleton. -/
theorem tsum_next_excursion_eq_excursionOccupationMeasure_singleton
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x y : E)
    (hrec : RecurrentAt κ x) :
    (∑' n : ℕ, markovChainLaw κ x
      (beforeReturnEvent x n ∩ {ω : ℕ → E | ω (n + 1) = y})) =
        excursionOccupationMeasure κ x {y} := by
  by_cases hyx : y = x
  · subst y
    calc
      (∑' n : ℕ, markovChainLaw κ x
        (beforeReturnEvent x n ∩ {ω : ℕ → E | ω (n + 1) = x})) =
          ∑' n : ℕ, markovChainLaw κ x (firstReturnSlice x n) := by
            apply tsum_congr
            intro n
            rfl
      _ = returnProbability κ x x := tsum_firstReturnSlice_eq_returnProbability κ x
      _ = 1 := hrec
      _ = excursionOccupationMeasure κ x {x} :=
        (excursionOccupationMeasure_apply_singleton κ x).symm
  · let f : ℕ → ℝ≥0∞ := fun n => markovChainLaw κ x
        (beforeReturnEvent x n ∩ {ω : ℕ → E | ω n = y})
    have hf0 : f 0 = 0 := by
      exact markovChainLaw_beforeReturn_zero_coordinate_of_ne κ x y hyx
    have htail : (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
      have hsplit := ENNReal.summable.sum_add_tsum_nat_add' (f := f) (k := 1)
      simpa [hf0] using hsplit
    have hshift :
        (∑' n : ℕ, markovChainLaw κ x
          (beforeReturnEvent x n ∩ {ω : ℕ → E | ω (n + 1) = y})) =
            ∑' n : ℕ, f (n + 1) := by
      apply tsum_congr
      intro n
      rw [beforeReturnEvent_inter_coordinate_succ_of_ne x y hyx n]
    have hoccupation : excursionOccupationMeasure κ x {y} = ∑' n : ℕ, f n := by
      simpa only [Set.mem_singleton_iff, f] using
        excursionOccupationMeasure_apply κ x (measurableSet_singleton y)
    rw [hshift, htail, ← hoccupation]

/-- The excursion occupation measure based at a recurrent state is invariant. -/
theorem recurrentAt_invariant_excursionOccupationMeasure
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hrec : RecurrentAt κ x) :
    κ.Invariant (excursionOccupationMeasure κ x) := by
  rw [Kernel.Invariant]
  apply Measure.ext_of_singleton
  intro y
  rw [comp_excursionOccupationMeasure_apply_singleton]
  exact tsum_next_excursion_eq_excursionOccupationMeasure_singleton κ x y hrec

/-- The normalized excursion law, available once finiteness of the occupation mass is known. -/
noncomputable def normalizedExcursionLaw
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hfin : excursionOccupationMeasure κ x Set.univ < ∞) : ProbabilityMeasure E :=
  letI : Nonempty E := ⟨x⟩
  FiniteMeasure.normalize
    (⟨excursionOccupationMeasure κ x, ⟨hfin⟩⟩ : FiniteMeasure E)

/-- Kac's return-time identity at a state, using the full-TV/extended-time conventions of this
package. -/
def SatisfiesKacFormulaAt
    (κ : Kernel E E) [IsMarkovKernel κ] (π : Measure E) (x : E) : Prop :=
  π {x} = (meanReturnTime κ x)⁻¹

/-- Project-facing spelling of Kac's identity. -/
theorem kacFormulaAt_iff
    (κ : Kernel E E) [IsMarkovKernel κ] (π : Measure E) (x : E) :
    SatisfiesKacFormulaAt κ π x ↔ π {x} = (meanReturnTime κ x)⁻¹ :=
  Iff.rfl

/-- The normalized excursion law satisfies Kac's return-time identity at its base state. -/
theorem normalizedExcursionLaw_satisfiesKacFormulaAt
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hfin : excursionOccupationMeasure κ x Set.univ < ∞) :
    SatisfiesKacFormulaAt κ
      ((normalizedExcursionLaw κ x hfin : ProbabilityMeasure E) : Measure E) x := by
  letI : Nonempty E := ⟨x⟩
  let μ := excursionOccupationMeasure κ x
  have hne : μ ≠ 0 := by
    intro hz
    have hz' := congrArg (fun m : Measure E => m {x}) hz
    rw [show μ {x} = 1 by
      exact excursionOccupationMeasure_apply_singleton κ x] at hz'
    simp at hz'
  let μf : FiniteMeasure E := ⟨μ, ⟨hfin⟩⟩
  have hμf : μf ≠ 0 := by
    intro hz
    apply hne
    have hz' := congrArg FiniteMeasure.toMeasure hz
    simpa [μf] using hz'
  have hmass : μf.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff μf).mpr hμf
  rw [SatisfiesKacFormulaAt, normalizedExcursionLaw]
  change ((FiniteMeasure.normalize μf : ProbabilityMeasure E) : Measure E) {x} = _
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μf]
  · rw [Measure.coe_nnreal_smul_apply, show (μf : Measure E) {x} = 1 by
      exact excursionOccupationMeasure_apply_singleton κ x]
    rw [mul_one, ENNReal.coe_inv hmass, FiniteMeasure.ennreal_mass,
      show (μf : Measure E) Set.univ = meanReturnTime κ x by
      exact excursionOccupationMeasure_apply_univ_eq_meanReturnTime κ x]
  · exact hμf

/-- Any established invariance of the finite excursion occupation measure passes to its normalized
probability law. -/
theorem invariant_normalizedExcursionLaw
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hfin : excursionOccupationMeasure κ x Set.univ < ∞)
    (hinv : κ.Invariant (excursionOccupationMeasure κ x)) :
    κ.Invariant ((normalizedExcursionLaw κ x hfin : ProbabilityMeasure E) : Measure E) := by
  letI : Nonempty E := ⟨x⟩
  apply hinv.normalize hfin
  intro hz
  have hz' := congrArg (fun m : Measure E => m {x}) hz
  rw [excursionOccupationMeasure_apply_singleton] at hz'
  simp at hz'

/-- Positive recurrence supplies all hypotheses needed to normalize the excursion occupation
measure into an invariant probability law. -/
theorem PositiveRecurrentAt.normalizedExcursionLaw_invariant
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hpos : PositiveRecurrentAt κ x) :
    κ.Invariant
      ((normalizedExcursionLaw κ x (by
        rw [excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
        exact hpos) : ProbabilityMeasure E) : Measure E) := by
  let hfin : excursionOccupationMeasure κ x Set.univ < ∞ := by
    rw [excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
    exact hpos
  exact invariant_normalizedExcursionLaw κ x hfin
    (recurrentAt_invariant_excursionOccupationMeasure κ x (hpos.recurrentAt κ x))

/-- The invariant probability obtained from a positive recurrent excursion also satisfies Kac's
formula at the base state. -/
theorem PositiveRecurrentAt.normalizedExcursionLaw_invariant_and_kac
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x : E)
    (hpos : PositiveRecurrentAt κ x) :
    let hfin : excursionOccupationMeasure κ x Set.univ < ∞ := by
      rw [excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
      exact hpos
    κ.Invariant ((normalizedExcursionLaw κ x hfin : ProbabilityMeasure E) : Measure E) ∧
      SatisfiesKacFormulaAt κ
        ((normalizedExcursionLaw κ x hfin : ProbabilityMeasure E) : Measure E) x := by
  dsimp only
  constructor
  · exact hpos.normalizedExcursionLaw_invariant κ x
  · exact normalizedExcursionLaw_satisfiesKacFormulaAt κ x _

/-! ### Minimality of the excursion measure -/

/-- The retained distribution at one time in the excursion from `x`. -/
noncomputable def excursionTermMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ) : Measure E :=
  Measure.map (fun ω : ℕ → E => ω n)
    ((markovChainLaw κ x).restrict (beforeReturnEvent x n))

theorem excursionTermMeasure_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    excursionTermMeasure κ x n A =
      markovChainLaw κ x (beforeReturnEvent x n ∩ {ω | ω n ∈ A}) := by
  rw [excursionTermMeasure, Measure.map_apply (measurable_pi_apply n) hA,
    Measure.restrict_apply]
  · congr 1
    ext ω
    simp [and_comm]
  · exact (measurable_pi_apply n) hA

/-- Away from the base state, the next retained excursion distribution is obtained by applying
the transition kernel to the current retained distribution. -/
theorem excursionTermMeasure_succ_apply_of_ne
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x y : E) (hyx : y ≠ x) (n : ℕ) :
    excursionTermMeasure κ x (n + 1) {y} =
      (κ ∘ₘ excursionTermMeasure κ x n) {y} := by
  rw [excursionTermMeasure_apply κ x (n + 1) (measurableSet_singleton y)]
  simp only [Set.mem_singleton_iff]
  rw [beforeReturnEvent_inter_coordinate_succ_of_ne x y hyx n |>.symm]
  have hstep := setLIntegral_transition_beforeReturn κ x n
    (measurableSet_singleton y)
  simp only [Set.mem_singleton_iff] at hstep
  rw [← hstep]
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable]
  rw [excursionTermMeasure]
  rw [lintegral_map
    (κ.measurable_coe (measurableSet_singleton y))
    (measurable_pi_apply n)]

theorem excursionTermMeasure_zero
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    excursionTermMeasure κ x 0 = Measure.dirac x := by
  apply Measure.ext_of_singleton
  intro y
  by_cases hyx : y = x
  · subst y
    rw [excursionTermMeasure_apply κ x 0 (measurableSet_singleton x),
      beforeReturnEvent_zero, Set.univ_inter,
      markovChainLaw_apply_coordinate κ x 0 (measurableSet_singleton x), pow_zero]
    rfl
  · rw [excursionTermMeasure_apply κ x 0 (measurableSet_singleton y),
      Measure.dirac_apply' _ (measurableSet_singleton y)]
    simp only [Set.mem_singleton_iff]
    rw [markovChainLaw_beforeReturn_zero_coordinate_of_ne κ x y hyx]
    simp [Ne.symm hyx]

/-- The first `N` retained excursion distributions. -/
noncomputable def excursionPartialMeasure
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (N : ℕ) : Measure E :=
  ∑ n ∈ Finset.range N, excursionTermMeasure κ x n

theorem excursionPartialMeasure_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (N : ℕ)
    {A : Set E} (_hA : MeasurableSet A) :
    excursionPartialMeasure κ x N A =
      ∑ n ∈ Finset.range N, excursionTermMeasure κ x n A := by
  simp [excursionPartialMeasure, Measure.finsetSum_apply]

theorem excursionPartialMeasure_succ_apply_of_ne
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x y : E) (hyx : y ≠ x) (N : ℕ) :
    excursionPartialMeasure κ x (N + 1) {y} =
      (κ ∘ₘ excursionPartialMeasure κ x N) {y} := by
  rw [excursionPartialMeasure_apply κ x (N + 1) (measurableSet_singleton y),
    Finset.sum_range_succ']
  have hzero : excursionTermMeasure κ x 0 {y} = 0 := by
    rw [excursionTermMeasure_zero, Measure.dirac_apply' _ (measurableSet_singleton y)]
    simp [Ne.symm hyx]
  rw [hzero, add_zero]
  calc
    (∑ n ∈ Finset.range N, excursionTermMeasure κ x (n + 1) {y}) =
        ∑ n ∈ Finset.range N, (κ ∘ₘ excursionTermMeasure κ x n) {y} := by
      apply Finset.sum_congr rfl
      intro n hn
      exact excursionTermMeasure_succ_apply_of_ne κ x y hyx n
    _ = (κ ∘ₘ excursionPartialMeasure κ x N) {y} := by
      rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable,
        excursionPartialMeasure, lintegral_finsetSum_measure]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable]

/-- Composition by a kernel is monotone in the input measure. -/
theorem measureComp_mono {μ ν : Measure E} (κ : Kernel E E) (hμν : μ ≤ ν) :
    κ ∘ₘ μ ≤ κ ∘ₘ ν := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
  exact lintegral_mono' hμν le_rfl

theorem excursionPartialMeasure_le_excursionOccupationMeasure
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (N : ℕ) :
    excursionPartialMeasure κ x N ≤ excursionOccupationMeasure κ x := by
  rw [Measure.le_iff]
  intro A hA
  rw [excursionPartialMeasure_apply κ x N hA, excursionOccupationMeasure,
    Measure.sum_apply _ hA]
  exact ENNReal.sum_le_tsum (Finset.range N)

namespace Kernel.Invariant

theorem pow {κ : Kernel E E} {μ : Measure E}
    (hμ : κ.Invariant μ) : ∀ n : ℕ, (κ ^ n).Invariant μ
  | 0 => by
      rw [pow_zero, Kernel.Invariant]
      exact Measure.id_comp
  | n + 1 => by
      rw [pow_succ']
      exact hμ.comp (pow hμ n)

/-- Positive invariant mass propagates along reachability. -/
theorem measure_pos_of_canReach
    [Countable E] {κ : Kernel E E} [IsMarkovKernel κ] {μ : Measure E}
    (hμ : κ.Invariant μ) {x y : E} (hμx : 0 < μ {x})
    (hxy : κ.CanReach x y) : 0 < μ {y} := by
  obtain ⟨n, hn⟩ := hxy
  have hinv := hμ.pow n
  rw [Kernel.Invariant] at hinv
  have heq := congrArg (fun m : Measure E => m {y}) hinv
  rw [Measure.bind_apply (measurableSet_singleton y) (κ ^ n).aemeasurable] at heq
  rw [← heq]
  calc
    0 < μ {x} * (κ ^ n) x {y} := ENNReal.mul_pos hμx.ne' hn.ne'
    _ = ∫⁻ z in {x}, (κ ^ n) z {y} ∂μ := by
      rw [lintegral_singleton]
      exact mul_comm _ _
    _ ≤ ∫⁻ z, (κ ^ n) z {y} ∂μ := setLIntegral_le_lintegral _ _

/-- Subtracting a dominated finite invariant measure preserves invariance. -/
theorem sub_of_le
    {κ : Kernel E E} {μ ν : Measure E} [IsFiniteMeasure ν]
    (hμ : κ.Invariant μ) (hν : κ.Invariant ν) (hνμ : ν ≤ μ) :
    κ.Invariant (μ - ν) := by
  have hdecomp : μ - ν + ν = μ := Measure.sub_add_cancel_of_le hνμ
  have heq : (κ ∘ₘ (μ - ν)) + ν = (μ - ν) + ν := by
    calc
      (κ ∘ₘ (μ - ν)) + ν = (κ ∘ₘ (μ - ν)) + (κ ∘ₘ ν) := by rw [hν]
      _ = κ ∘ₘ ((μ - ν) + ν) := Measure.comp_add.symm
      _ = κ ∘ₘ μ := by rw [hdecomp]
      _ = μ := hμ
      _ = (μ - ν) + ν := hdecomp.symm
  rw [Kernel.Invariant]
  apply le_antisymm
  · apply Measure.le_of_add_le_add_left (μ := ν)
    simpa only [add_comm] using heq.le
  · apply Measure.le_of_add_le_add_left (μ := ν)
    simpa only [add_comm] using heq.ge

end Kernel.Invariant

/-- Every invariant probability of an irreducible countable chain has full singleton support. -/
theorem invariantProbability_singleton_pos
    [Countable E] {κ : Kernel E E} [IsMarkovKernel κ]
    {π : Measure E} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) (y : E) :
    0 < π {y} := by
  rw [Kernel.isIrreducible_count_iff_forall_canReach] at hirr
  by_contra hy
  have hall : ∀ x : E, π {x} = 0 := by
    intro x
    by_contra hx
    have hxpos : 0 < π {x} := bot_lt_iff_ne_bot.mpr hx
    exact hy (hπ.measure_pos_of_canReach hxpos (hirr x y))
  have hzero : π = 0 := Measure.ext_of_singleton hall
  have huniv := congrArg (fun m : Measure E => m Set.univ) hzero
  simp at huniv

/-- The first `N` excursion terms, scaled by the invariant mass at the base state, are dominated
by the invariant measure. -/
theorem excursionPartialMeasure_smul_le_invariant
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) {μ : Measure E} (hμ : κ.Invariant μ) :
    ∀ N, μ {x} • excursionPartialMeasure κ x N ≤ μ := by
  intro N
  induction N with
  | zero =>
      simp [excursionPartialMeasure]
      exact bot_le
  | succ N ih =>
      rw [Measure.le_iff]
      intro A hA
      have hsingle (y : E) :
          (μ {x} • excursionPartialMeasure κ x (N + 1)) {y} ≤ μ {y} := by
        by_cases hyx : y = x
        · subst y
          rw [Measure.smul_apply, smul_eq_mul]
          calc
            μ {x} * excursionPartialMeasure κ x (N + 1) {x} ≤ μ {x} * 1 := by
              gcongr
              calc
                excursionPartialMeasure κ x (N + 1) {x} ≤
                    excursionOccupationMeasure κ x {x} :=
                  excursionPartialMeasure_le_excursionOccupationMeasure κ x (N + 1) {x}
                _ = 1 := excursionOccupationMeasure_apply_singleton κ x
            _ = μ {x} := mul_one _
        · rw [Measure.smul_apply, smul_eq_mul,
            excursionPartialMeasure_succ_apply_of_ne κ x y hyx]
          have hcomp := measureComp_mono κ ih
          have happ := hcomp {y}
          rw [Measure.comp_smul, hμ] at happ
          simpa only [Measure.smul_apply, smul_eq_mul] using happ
      rw [← Measure.tsum_indicator_apply_singleton
        (μ {x} • excursionPartialMeasure κ x (N + 1)) A hA,
        ← Measure.tsum_indicator_apply_singleton μ A hA]
      exact ENNReal.tsum_le_tsum fun y => by
        by_cases hyA : y ∈ A
        · simpa [Set.indicator_of_mem hyA] using hsingle y
        · simp [Set.indicator_of_notMem hyA]

/-- The excursion occupation measure is the minimal invariant measure having unit mass at its
base point. -/
theorem excursionOccupationMeasure_smul_le_invariant
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) {μ : Measure E} (hμ : κ.Invariant μ) :
    μ {x} • excursionOccupationMeasure κ x ≤ μ := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.smul_apply, excursionOccupationMeasure,
    Measure.sum_apply _ hA, smul_eq_mul, ← ENNReal.tsum_mul_left,
    ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  have hN := excursionPartialMeasure_smul_le_invariant κ x hμ N A
  rw [Measure.smul_apply, smul_eq_mul,
    excursionPartialMeasure_apply κ x N hA, Finset.mul_sum] at hN
  exact hN

/-- An invariant probability assigning positive mass to a state makes that state positive
recurrent. -/
theorem invariantProbability_positiveRecurrentAt
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) {π : Measure E} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hπx : 0 < π {x}) :
    PositiveRecurrentAt κ x := by
  rw [PositiveRecurrentAt, ← excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
  have hdom := excursionOccupationMeasure_smul_le_invariant κ x hπ Set.univ
  have hπuniv : π Set.univ = 1 := measure_univ
  rw [Measure.smul_apply, smul_eq_mul, hπuniv] at hdom
  by_contra htop
  have htop' : excursionOccupationMeasure κ x Set.univ = ∞ := top_unique (not_lt.mp htop)
  rw [htop', ENNReal.mul_top hπx.ne'] at hdom
  exact (not_le_of_gt ENNReal.one_lt_top) hdom

/-- An irreducible invariant probability is its base-state mass times the excursion occupation
measure. -/
theorem invariantProbability_eq_smul_excursion
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) {π : Measure E} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    π = π {x} • excursionOccupationMeasure κ x := by
  rw [Kernel.isIrreducible_count_iff_forall_canReach] at hirr
  have hπx : 0 < π {x} := invariantProbability_singleton_pos hπ (by
    rw [Kernel.isIrreducible_count_iff_forall_canReach]
    exact hirr) x
  have hpos : PositiveRecurrentAt κ x :=
    invariantProbability_positiveRecurrentAt κ x hπ hπx
  let ν : Measure E := π {x} • excursionOccupationMeasure κ x
  have hνπ : ν ≤ π := excursionOccupationMeasure_smul_le_invariant κ x hπ
  letI : IsFiniteMeasure ν :=
    IsFiniteMeasure.mk (lt_of_le_of_lt (hνπ Set.univ) (measure_lt_top π Set.univ))
  have hνinv : κ.Invariant ν := by
    exact (recurrentAt_invariant_excursionOccupationMeasure κ x
      (hpos.recurrentAt κ x)).smul (π {x})
  have hresinv : κ.Invariant (π - ν) := hπ.sub_of_le hνinv hνπ
  have hνx : ν {x} = π {x} := by
    simp only [ν, Measure.smul_apply, smul_eq_mul,
      excursionOccupationMeasure_apply_singleton, mul_one]
  have hresx : (π - ν) {x} = 0 := by
    rw [Measure.sub_apply (measurableSet_singleton x) hνπ, hνx, tsub_self]
  have hreszero : π - ν = 0 := by
    by_contra hne
    have hexists : ∃ y : E, (π - ν) {y} ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Measure.ext_of_singleton hall)
    obtain ⟨y, hy⟩ := hexists
    have hypos : 0 < (π - ν) {y} := bot_lt_iff_ne_bot.mpr hy
    have hxpos := hresinv.measure_pos_of_canReach hypos (hirr y x)
    rw [hresx] at hxpos
    exact (lt_irrefl 0 hxpos)
  have hdecomp : π - ν + ν = π := Measure.sub_add_cancel_of_le hνπ
  rw [hreszero, zero_add] at hdecomp
  exact hdecomp.symm

/-- Kac's formula for every invariant probability of an irreducible countable chain. -/
theorem invariantProbability_satisfiesKacFormulaAt
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (x : E) {π : Measure E} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (hirr : Kernel.IsIrreducible Measure.count κ) :
    SatisfiesKacFormulaAt κ π x := by
  have heq := invariantProbability_eq_smul_excursion κ x hπ hirr
  have huniv := congrArg (fun μ : Measure E => μ Set.univ) heq
  have hπuniv : π Set.univ = 1 := measure_univ
  rw [hπuniv, Measure.smul_apply, smul_eq_mul,
    excursionOccupationMeasure_apply_univ_eq_meanReturnTime] at huniv
  rw [SatisfiesKacFormulaAt]
  exact ENNReal.eq_inv_of_mul_eq_one_left huniv.symm

/-- An irreducible countable Markov kernel has at most one invariant probability. -/
theorem invariantProbability_unique
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (hirr : Kernel.IsIrreducible Measure.count κ)
    {π ρ : Measure E} [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hπ : κ.Invariant π) (hρ : κ.Invariant ρ) : π = ρ := by
  have hπeq := invariantProbability_eq_smul_excursion κ
    (Classical.choice (nonempty_of_isProbabilityMeasure π)) hπ hirr
  let x : E := Classical.choice (nonempty_of_isProbabilityMeasure π)
  have hρeq := invariantProbability_eq_smul_excursion κ x hρ hirr
  have hπkac := invariantProbability_satisfiesKacFormulaAt κ x hπ hirr
  have hρkac := invariantProbability_satisfiesKacFormulaAt κ x hρ hirr
  rw [SatisfiesKacFormulaAt] at hπkac hρkac
  calc
    π = π {x} • excursionOccupationMeasure κ x := by simpa only [x] using hπeq
    _ = ρ {x} • excursionOccupationMeasure κ x := by rw [hπkac, hρkac]
    _ = ρ := hρeq.symm

/-- Positive recurrence propagates to every reachable state; in particular it is constant on a
communicating class. -/
theorem PositiveRecurrentAt.of_communicates
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] {x y : E}
    (hxy : κ.CanReach x y) (_hyx : κ.CanReach y x)
    (hx : PositiveRecurrentAt κ x) : PositiveRecurrentAt κ y := by
  let hfin : excursionOccupationMeasure κ x Set.univ < ∞ := by
    rw [excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
    exact hx
  let π : Measure E :=
    ((normalizedExcursionLaw κ x hfin : ProbabilityMeasure E) : Measure E)
  letI : IsProbabilityMeasure π := by infer_instance
  have hπinv : κ.Invariant π := hx.normalizedExcursionLaw_invariant κ x
  have hkac := normalizedExcursionLaw_satisfiesKacFormulaAt κ x hfin
  have hπx : 0 < π {x} := by
    rw [SatisfiesKacFormulaAt] at hkac
    rw [hkac]
    exact ENNReal.inv_pos.mpr hx.ne
  have hπy : 0 < π {y} := hπinv.measure_pos_of_canReach hπx hxy
  exact invariantProbability_positiveRecurrentAt κ y hπinv hπy

/-- For an irreducible countable chain, positive recurrence at a selected state is equivalent to
existence of an invariant probability. -/
theorem irreducible_positiveRecurrentAt_iff_exists_invariantProbability
    [Countable E] (κ : Kernel E E) [IsMarkovKernel κ]
    (hirr : Kernel.IsIrreducible Measure.count κ) (x : E) :
    PositiveRecurrentAt κ x ↔
      ∃ π : ProbabilityMeasure E, κ.Invariant (π : Measure E) := by
  constructor
  · intro hx
    let hfin : excursionOccupationMeasure κ x Set.univ < ∞ := by
      rw [excursionOccupationMeasure_apply_univ_eq_meanReturnTime]
      exact hx
    exact ⟨normalizedExcursionLaw κ x hfin,
      hx.normalizedExcursionLaw_invariant κ x⟩
  · rintro ⟨π, hπ⟩
    letI : IsProbabilityMeasure (π : Measure E) := inferInstance
    have hπx : 0 < (π : Measure E) {x} :=
      invariantProbability_singleton_pos hπ hirr x
    exact invariantProbability_positiveRecurrentAt κ x hπ hπx

end ProbabilityTheory
