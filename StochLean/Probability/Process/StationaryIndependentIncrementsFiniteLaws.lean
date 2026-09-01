/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrementsProjective

/-!
# Finite increment laws of the canonical coordinate process

This file completes the project-local Kolmogorov construction of a real process from a convolution
semigroup.  It treats repeated times explicitly: the advancing intervals are matched bijectively
with the noninitial gaps of the distinct-time set, while zero-length increments use the derived
identity `ν 0 = δ 0`.  Consequently every finite ordered partition has the prescribed product law,
and the coordinate process has genuine stationary independent increments.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.SIIConstruction

/-- The finite set of values visited by a finite ordered time sequence. -/
noncomputable def partitionTimeSet {n : ℕ} (t : Fin (n + 1) → ℝ≥0) : Finset ℝ≥0 :=
  Finset.univ.image t

/-- Chronological rank of an entry in its finite value set. -/
noncomputable def partitionTimeRank {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (i : Fin (n + 1)) : Fin #(partitionTimeSet t) :=
  ((partitionTimeSet t).orderIsoOfFin rfl).symm
    ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem partitionTimeRank_apply_time {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (i : Fin (n + 1)) :
    (partitionTimeSet t).orderEmbOfFin rfl (partitionTimeRank t i) = t i := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)

theorem partitionTimeRank_surjective {n : ℕ} (t : Fin (n + 1) → ℝ≥0) :
    Function.Surjective (partitionTimeRank t) := by
  intro k
  have hk := ((partitionTimeSet t).orderIsoOfFin rfl k).property
  rcases Finset.mem_image.mp hk with ⟨i, _, hi⟩
  refine ⟨i, ?_⟩
  apply ((partitionTimeSet t).orderIsoOfFin rfl).injective
  apply Subtype.ext
  simpa [partitionTimeRank] using hi

theorem monotone_partitionTimeRank {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) : Monotone (partitionTimeRank t) := by
  intro i j hij
  apply ((partitionTimeSet t).orderIsoOfFin rfl).symm.monotone
  exact ht hij

theorem partitionTimeRank_zero {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) : (partitionTimeRank t 0).val = 0 := by
  obtain ⟨i, hi⟩ := partitionTimeRank_surjective t
    ⟨0, by
      have hnonempty : (partitionTimeSet t).Nonempty := by
        exact ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
      simpa using Finset.card_pos.mpr hnonempty⟩
  have hle := monotone_partitionTimeRank ht (Fin.zero_le i)
  have hle' : partitionTimeRank t 0 ≤
      ⟨0, by
        have hnonempty : (partitionTimeSet t).Nonempty := by
          exact ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
        simpa using Finset.card_pos.mpr hnonempty⟩ := by
    simpa only [hi] using hle
  exact Nat.eq_zero_of_le_zero (Fin.le_iff_val_le_val.mp hle')

theorem partitionTimeRank_succ_le {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) (i : Fin n) :
    (partitionTimeRank t i.succ).val ≤ (partitionTimeRank t i.castSucc).val + 1 := by
  by_contra hnot
  have hklt : (partitionTimeRank t i.castSucc).val + 1 < #(partitionTimeSet t) := by
    exact lt_of_lt_of_le (by omega) (partitionTimeRank t i.succ).isLt.le
  let k : Fin #(partitionTimeSet t) :=
    ⟨(partitionTimeRank t i.castSucc).val + 1, hklt⟩
  obtain ⟨q, hq⟩ := partitionTimeRank_surjective t k
  by_cases hqi : q ≤ i.castSucc
  · have hle := monotone_partitionTimeRank ht hqi
    rw [hq] at hle
    change (partitionTimeRank t i.castSucc).val + 1 ≤
      (partitionTimeRank t i.castSucc).val at hle
    omega
  · have hiq : i.succ ≤ q := by
      apply Fin.le_iff_val_le_val.mpr
      simpa using (Fin.lt_def.mp (lt_of_not_ge hqi))
    have hle := monotone_partitionTimeRank ht hiq
    rw [hq] at hle
    change (partitionTimeRank t i.succ).val ≤
      (partitionTimeRank t i.castSucc).val + 1 at hle
    omega

theorem partitionTimeRank_eq_or_succ {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) (i : Fin n) :
    partitionTimeRank t i.succ = partitionTimeRank t i.castSucc ∨
      (partitionTimeRank t i.succ).val = (partitionTimeRank t i.castSucc).val + 1 := by
  have hmono := monotone_partitionTimeRank ht (Fin.castSucc_le_succ i)
  have hstep := partitionTimeRank_succ_le ht i
  by_cases hEq : partitionTimeRank t i.succ = partitionTimeRank t i.castSucc
  · exact Or.inl hEq
  · right
    have hlt : (partitionTimeRank t i.castSucc).val <
        (partitionTimeRank t i.succ).val := by
      exact lt_of_le_of_ne (Fin.le_iff_val_le_val.mp hmono) (by
        intro h
        apply hEq
        exact Fin.ext h.symm)
    omega

theorem partitionTimeRank_strict_iff {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) (i : Fin n) :
    t i.castSucc < t i.succ ↔
      (partitionTimeRank t i.succ).val = (partitionTimeRank t i.castSucc).val + 1 := by
  have horder : t i.castSucc < t i.succ ↔
      partitionTimeRank t i.castSucc < partitionTimeRank t i.succ := by
    rw [← partitionTimeRank_apply_time t i.castSucc,
      ← partitionTimeRank_apply_time t i.succ]
    exact (partitionTimeSet t).orderEmbOfFin rfl |>.lt_iff_lt
  rw [horder]
  constructor
  · intro hlt
    have hstep := partitionTimeRank_succ_le ht i
    omega
  · intro h
    exact Fin.lt_def.mpr (by omega)

/-- Indices at which a monotone finite partition advances to a new time. -/
noncomputable def activeTransitions {n : ℕ} (t : Fin (n + 1) → ℝ≥0) : Finset (Fin n) :=
  Finset.univ.filter fun i => t i.castSucc < t i.succ

/-- All chronological gaps except the initial gap from zero to the first partition time. -/
noncomputable def noninitialGapIndices {n : ℕ} (t : Fin (n + 1) → ℝ≥0) :
    Finset (Fin #(partitionTimeSet t)) :=
  Finset.univ.filter fun k => 0 < k.val

theorem activeTransition_rank_pos {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) {i : Fin n} (hi : i ∈ activeTransitions t) :
    0 < (partitionTimeRank t i.succ).val := by
  have hstep := (partitionTimeRank_strict_iff ht i).mp (by simpa [activeTransitions] using hi)
  omega

theorem activeTransition_rank_injective {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) : Set.InjOn (fun i : Fin n => partitionTimeRank t i.succ)
      (activeTransitions t) := by
  intro i hi j hj heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hisj : i.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simpa using hij
    have hle := monotone_partitionTimeRank ht hisj
    have hjstep := (partitionTimeRank_strict_iff ht j).mp (by
      simpa [activeTransitions] using hj)
    have heqv := congrArg Fin.val heq
    change (partitionTimeRank t i.succ).val ≤
      (partitionTimeRank t j.castSucc).val at hle
    change (partitionTimeRank t j.succ).val =
      (partitionTimeRank t j.castSucc).val + 1 at hjstep
    change (partitionTimeRank t i.succ).val =
      (partitionTimeRank t j.succ).val at heqv
    omega
  · have hjsi : j.succ ≤ i.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simpa using hji
    have hle := monotone_partitionTimeRank ht hjsi
    have histep := (partitionTimeRank_strict_iff ht i).mp (by
      simpa [activeTransitions] using hi)
    have heqv := congrArg Fin.val heq
    change (partitionTimeRank t j.succ).val ≤
      (partitionTimeRank t i.castSucc).val at hle
    change (partitionTimeRank t i.succ).val =
      (partitionTimeRank t i.castSucc).val + 1 at histep
    change (partitionTimeRank t i.succ).val =
      (partitionTimeRank t j.succ).val at heqv
    omega

theorem exists_activeTransition_rank_eq {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) (k : Fin #(partitionTimeSet t)) (hk : 0 < k.val) :
    ∃ i : Fin n, i ∈ activeTransitions t ∧ partitionTimeRank t i.succ = k := by
  let pre : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun q => partitionTimeRank t q = k
  have hpre : pre.Nonempty := by
    obtain ⟨q, hq⟩ := partitionTimeRank_surjective t k
    exact ⟨q, by simp [pre, hq]⟩
  let q : Fin (n + 1) := pre.min' hpre
  have hqmem : q ∈ pre := Finset.min'_mem pre hpre
  have hqrank : partitionTimeRank t q = k := by simpa [pre] using hqmem
  have hqpos : 0 < q.val := by
    by_contra hzero
    have hqval : q.val = 0 := Nat.eq_zero_of_not_pos hzero
    let qzero : Fin (n + 1) := ⟨0, by omega⟩
    have hqzero : q = qzero := Fin.ext hqval
    have hzeroRank := partitionTimeRank_zero ht
    rw [hqzero] at hqrank
    have hrankval := congrArg Fin.val hqrank
    change (partitionTimeRank t qzero).val = k.val at hrankval
    change (partitionTimeRank t qzero).val = 0 at hzeroRank
    omega
  let i : Fin n := ⟨q.val - 1, by omega⟩
  have hiSucc : i.succ = q := by
    apply Fin.ext
    dsimp [i]
    omega
  refine ⟨i, ?_, by simpa [hiSucc] using hqrank⟩
  simp only [activeTransitions, Finset.mem_filter, Finset.mem_univ, true_and]
  apply (partitionTimeRank_strict_iff ht i).mpr
  have hmono := monotone_partitionTimeRank ht (Fin.castSucc_le_succ i)
  have hstep := partitionTimeRank_eq_or_succ ht i
  rcases hstep with heq | hsucc
  · exfalso
    have hprevMem : i.castSucc ∈ pre := by
      simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and]
      calc
        partitionTimeRank t i.castSucc = partitionTimeRank t i.succ := heq.symm
        _ = k := by simpa [hiSucc] using hqrank
    have hmin := Finset.min'_le pre i.castSucc hprevMem
    change q ≤ i.castSucc at hmin
    rw [← hiSucc] at hmin
    exact (not_le_of_gt (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) hmin
  · exact hsucc

theorem activeTransition_rank_surjective {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) : Set.SurjOn (fun i : Fin n => partitionTimeRank t i.succ)
      (activeTransitions t) (noninitialGapIndices t) := by
  intro k hk
  have hkpos : 0 < k.val := by simpa [noninitialGapIndices] using hk
  obtain ⟨i, hi, hirank⟩ := exists_activeTransition_rank_eq ht k hkpos
  exact ⟨i, hi, hirank⟩

/-- Read a vector on the distinct partition times along the original, possibly repeated,
partition. -/
noncomputable def partitionRestrictLinear {n : ℕ} (t : Fin (n + 1) → ℝ≥0) :
    ((partitionTimeSet t) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fun x i => x ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
  cont := by
    rw [continuous_pi_iff]
    intro i
    let ti : partitionTimeSet t := ⟨t i, by simp [partitionTimeSet]⟩
    exact continuous_apply ti

@[simp]
theorem partitionRestrictLinear_apply {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (x : partitionTimeSet t → ℝ) (i : Fin (n + 1)) :
    partitionRestrictLinear t x i =
      x ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ := rfl

/-- Consecutive differences of a finite vector. -/
def successiveDifferenceLinear (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) where
  toFun := fun x i => x i.succ - x i.castSucc
  map_add' x y := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    change c * x i.succ - c * x i.castSucc = c * (x i.succ - x i.castSucc)
    ring
  cont := by
    rw [continuous_pi_iff]
    intro i
    exact (continuous_apply i.succ).sub (continuous_apply i.castSucc)

@[simp]
theorem successiveDifferenceLinear_apply {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    successiveDifferenceLinear n x i = x i.succ - x i.castSucc := rfl

/-- Turn positions at the distinct times of a partition into the consecutive increments along
the original partition. -/
noncomputable def partitionIncrementLinear {n : ℕ} (t : Fin (n + 1) → ℝ≥0) :
    ((partitionTimeSet t) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (successiveDifferenceLinear n).comp (partitionRestrictLinear t)

@[simp]
theorem partitionIncrementLinear_apply {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (x : partitionTimeSet t → ℝ) (i : Fin n) :
    partitionIncrementLinear t x i =
      x ⟨t i.succ, Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩⟩ -
      x ⟨t i.castSucc, Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩⟩ := rfl

theorem partitionTimeRank_subtype {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (i : Fin (n + 1)) :
    ((partitionTimeSet t).orderIsoOfFin rfl).symm
      ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ =
      partitionTimeRank t i := rfl

theorem partitionIncrementLinear_gapTailIndicator_apply {n : ℕ}
    {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t)
    (k : Fin #(partitionTimeSet t)) (i : Fin n) :
    partitionIncrementLinear t (gapTailIndicator (partitionTimeSet t) k) i =
      if partitionTimeRank t i.castSucc < k ∧ k ≤ partitionTimeRank t i.succ then 1 else 0 := by
  rw [partitionIncrementLinear_apply]
  simp only [gapTailIndicator]
  let tsucc : partitionTimeSet t := ⟨t i.succ, by simp [partitionTimeSet]⟩
  let tprev : partitionTimeSet t := ⟨t i.castSucc, by simp [partitionTimeSet]⟩
  have hsucc : orderedTimeWithZero (partitionTimeSet t) k.succ ≤ tsucc ↔
      k ≤ partitionTimeRank t i.succ := by
    simpa only [tsucc, partitionTimeRank_subtype] using
      orderedTimeWithZero_succ_le_iff (partitionTimeSet t) k tsucc
  have hprev : orderedTimeWithZero (partitionTimeSet t) k.succ ≤ tprev ↔
      k ≤ partitionTimeRank t i.castSucc := by
    simpa only [tprev, partitionTimeRank_subtype] using
      orderedTimeWithZero_succ_le_iff (partitionTimeSet t) k tprev
  change ((if orderedTimeWithZero (partitionTimeSet t) k.succ ≤ tsucc then 1 else 0) -
      if orderedTimeWithZero (partitionTimeSet t) k.succ ≤ tprev then 1 else 0) = _
  simp only [hsucc, hprev]
  have hrankmono := monotone_partitionTimeRank ht (Fin.castSucc_le_succ i)
  by_cases hprev : k ≤ partitionTimeRank t i.castSucc
  · have hnext : k ≤ partitionTimeRank t i.succ := hprev.trans hrankmono
    simp [hprev, hnext]
  · have hprevlt : partitionTimeRank t i.castSucc < k := lt_of_not_ge hprev
    by_cases hnext : k ≤ partitionTimeRank t i.succ
    · simp [hprev, hnext, hprevlt]
    · simp [hprev, hnext]

theorem partitionIncrementLinear_gapTailIndicator_eq_single_of_active {n : ℕ}
    {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t) {i : Fin n}
    (hi : i ∈ activeTransitions t) :
    partitionIncrementLinear t
        (gapTailIndicator (partitionTimeSet t) (partitionTimeRank t i.succ)) =
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i) 1 := by
  ext j
  rw [partitionIncrementLinear_gapTailIndicator_apply ht]
  simp only [ContinuousLinearMap.single_apply]
  have histep := (partitionTimeRank_strict_iff ht i).mp (by
    simpa [activeTransitions] using hi)
  by_cases hji : j = i
  · subst j
    simp only [Pi.single_eq_same]
    have hcond : partitionTimeRank t i.castSucc < partitionTimeRank t i.succ ∧
        partitionTimeRank t i.succ ≤ partitionTimeRank t i.succ :=
      ⟨Fin.lt_def.mpr (by omega), le_rfl⟩
    rw [if_pos hcond]
  · rw [Pi.single_eq_of_ne hji]
    split_ifs with hcond
    · exfalso
      have hjstep := partitionTimeRank_eq_or_succ ht j
      rcases hjstep with hjEq | hjSucc
      · have hlt := hcond.1
        have hle := hcond.2
        rw [hjEq] at hle
        exact (not_lt_of_ge hle) hlt
      · have hEqRank : partitionTimeRank t j.succ = partitionTimeRank t i.succ := by
          apply Fin.ext
          have hlt := Fin.lt_def.mp hcond.1
          have hle := Fin.le_def.mp hcond.2
          change (partitionTimeRank t j.succ).val =
            (partitionTimeRank t j.castSucc).val + 1 at hjSucc
          omega
        have hjactive : j ∈ activeTransitions t := by
          simp only [activeTransitions, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (partitionTimeRank_strict_iff ht j).mpr hjSucc
        exact hji ((activeTransition_rank_injective ht) hjactive hi hEqRank)
    · rfl

theorem partitionIncrementLinear_gapTailIndicator_eq_zero_of_rank_zero {n : ℕ}
    {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t) (k : Fin #(partitionTimeSet t))
    (hk : k.val = 0) :
    partitionIncrementLinear t (gapTailIndicator (partitionTimeSet t) k) = 0 := by
  ext i
  rw [partitionIncrementLinear_gapTailIndicator_apply ht]
  simp only [Pi.zero_apply]
  split_ifs with hcond
  · have hnonneg : 0 ≤ (partitionTimeRank t i.castSucc).val := Nat.zero_le _
    have hlt := Fin.lt_def.mp hcond.1
    omega
  · rfl

theorem orderedGap_partitionTimeRank_succ {n : ℕ} {t : Fin (n + 1) → ℝ≥0}
    (ht : Monotone t) {i : Fin n} (hi : i ∈ activeTransitions t) :
    orderedGap (partitionTimeSet t) (partitionTimeRank t i.succ) =
      t i.succ - t i.castSucc := by
  have hstep := (partitionTimeRank_strict_iff ht i).mp (by
    simpa [activeTransitions] using hi)
  rw [orderedGap, orderedTimeWithZero_succ]
  rw [partitionTimeRank_apply_time]
  have hindices : (partitionTimeRank t i.succ).castSucc =
      (partitionTimeRank t i.castSucc).succ := by
    apply Fin.ext
    exact hstep
  rw [hindices, orderedTimeWithZero_succ, partitionTimeRank_apply_time]

theorem scalarChar_zero_time (nu : ℝ≥0 → ProbabilityMeasure ℝ)
    (hnu : IsConvolutionSemigroup nu) (c : ℝ) : scalarChar nu 0 c = 1 := by
  rw [scalarChar, hnu.zero_eq_pointMass_real]
  change charFunDual (Measure.dirac 0) (c • ContinuousLinearMap.id ℝ ℝ) = 1
  rw [charFunDual_dirac]
  simp

theorem charFunDual_pi_scalar (nu : ℝ≥0 → ProbabilityMeasure ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (L : StrongDual ℝ (Fin n → ℝ)) :
    charFunDual
        (Measure.pi fun i : Fin n => (nu (t i.succ - t i.castSucc) : Measure ℝ)) L =
      ∏ i : Fin n, scalarChar nu (t i.succ - t i.castSucc)
        (L ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i) 1)) := by
  rw [charFunDual_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [scalarChar]
  congr 1
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  have hs : (Pi.single i x : Fin n → ℝ) = x • Pi.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  rw [hs, map_smul]
  simp [smul_eq_mul, mul_comm]

theorem prod_partitionGap_scalar_eq_prod_partitionIncrement_scalar
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
    (L : StrongDual ℝ (Fin n → ℝ)) :
    (∏ k : Fin #(partitionTimeSet t),
        scalarChar nu (orderedGap (partitionTimeSet t) k)
          (L (partitionIncrementLinear t (gapTailIndicator (partitionTimeSet t) k)))) =
      ∏ i : Fin n, scalarChar nu (t i.succ - t i.castSucc)
        (L ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i) 1)) := by
  let gapFactor := fun k : Fin #(partitionTimeSet t) =>
    scalarChar nu (orderedGap (partitionTimeSet t) k)
      (L (partitionIncrementLinear t (gapTailIndicator (partitionTimeSet t) k)))
  let transitionFactor := fun i : Fin n =>
    scalarChar nu (t i.succ - t i.castSucc)
      (L ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) i) 1))
  have hgapSubset : noninitialGapIndices t ⊆ Finset.univ := by simp
  have hgapUnit : ∀ k ∈ (Finset.univ : Finset (Fin #(partitionTimeSet t))),
      k ∉ noninitialGapIndices t → gapFactor k = 1 := by
    intro k _ hk
    have hkzero : k.val = 0 := by
      simp only [noninitialGapIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      omega
    dsimp [gapFactor]
    rw [partitionIncrementLinear_gapTailIndicator_eq_zero_of_rank_zero ht k hkzero]
    simp
  have hgapTrim : (∏ k ∈ noninitialGapIndices t, gapFactor k) =
      ∏ k : Fin #(partitionTimeSet t), gapFactor k :=
    Finset.prod_subset hgapSubset hgapUnit
  have htransitionSubset : activeTransitions t ⊆ Finset.univ := by simp
  have htransitionUnit : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      i ∉ activeTransitions t → transitionFactor i = 1 := by
    intro i _ hi
    have hle := ht (Fin.castSucc_le_succ i)
    have hnotlt : ¬t i.castSucc < t i.succ := by
      simpa only [activeTransitions, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have heq : t i.succ = t i.castSucc := le_antisymm (le_of_not_gt hnotlt) hle
    dsimp [transitionFactor]
    rw [heq, tsub_self, scalarChar_zero_time nu hnu]
  have htransitionTrim : (∏ i ∈ activeTransitions t, transitionFactor i) =
      ∏ i : Fin n, transitionFactor i :=
    Finset.prod_subset htransitionSubset htransitionUnit
  have hreindex : (∏ i ∈ activeTransitions t, transitionFactor i) =
      ∏ k ∈ noninitialGapIndices t, gapFactor k := by
    apply Finset.prod_bij (fun i _ => partitionTimeRank t i.succ)
    · intro i hi
      simp only [noninitialGapIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact activeTransition_rank_pos ht hi
    · intro i hi j hj heq
      exact activeTransition_rank_injective ht hi hj heq
    · intro k hk
      obtain ⟨i, hi, hirank⟩ := activeTransition_rank_surjective ht hk
      exact ⟨i, hi, hirank⟩
    · intro i hi
      dsimp [transitionFactor, gapFactor]
      rw [orderedGap_partitionTimeRank_succ ht hi,
        partitionIncrementLinear_gapTailIndicator_eq_single_of_active ht hi]
  change (∏ k : Fin #(partitionTimeSet t), gapFactor k) =
    ∏ i : Fin n, transitionFactor i
  rw [← hgapTrim, ← htransitionTrim, hreindex]

/-- Consecutive differences of the finite position law have exactly the independent product law
prescribed by the convolution semigroup, including repeated partition times. -/
theorem map_finitePositionLaw_partitionIncrementLinear
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    (finitePositionLaw nu (partitionTimeSet t)).map (partitionIncrementLinear t) =
      Measure.pi fun i : Fin n => (nu (t i.succ - t i.castSucc) : Measure ℝ) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_finitePositionLaw_tail, charFunDual_pi_scalar]
  change (∏ k : Fin #(partitionTimeSet t),
      scalarChar nu (orderedGap (partitionTimeSet t) k)
        (L (partitionIncrementLinear t (gapTailIndicator (partitionTimeSet t) k)))) = _
  exact prod_partitionGap_scalar_eq_prod_partitionIncrement_scalar nu hnu t ht L

section CoordinateIncrementLaws

variable (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)

/-- The canonical coordinate process has the complete finite product laws of its stationary
increments. -/
theorem hasFiniteStationaryIncrementLaws_coordinateProcess :
    HasFiniteStationaryIncrementLaws coordinateProcess nu
      (coordinateMeasureOfSemigroup nu hnu) := by
  intro n t ht
  let I := partitionTimeSet t
  let A := partitionIncrementLinear t
  have hpositions : HasLaw I.restrict (finitePositionLaw nu I)
      (coordinateMeasureOfSemigroup nu hnu) :=
    hasLaw_restrict_of_semigroup nu hnu I
  have hlinear : HasLaw A
      (Measure.pi fun i : Fin n => (nu (t i.succ - t i.castSucc) : Measure ℝ))
      (finitePositionLaw nu I) := by
    refine ⟨A.continuous.aemeasurable, ?_⟩
    exact map_finitePositionLaw_partitionIncrementLinear nu hnu t ht
  have hcomp := hlinear.fun_comp hpositions
  refine hcomp.congr (Filter.Eventually.of_forall fun ω => ?_)
  ext i
  rfl

/-- The canonical coordinate process realizes the semigroup as its time-zero increment-law
family. -/
theorem hasIncrementLawFamily_coordinateProcess :
    HasIncrementLawFamily coordinateProcess nu (coordinateMeasureOfSemigroup nu hnu) := by
  intro t
  simpa only [coordinateProcess, tsub_zero] using
    (hasFiniteStationaryIncrementLaws_coordinateProcess nu hnu).incrementLaw 0 t (by simp)

/-- Kolmogorov construction of a genuine stationary-independent-increment process from any real
convolution semigroup. -/
theorem hasStationaryIndependentIncrements_coordinateProcess :
    HasStationaryIndependentIncrements coordinateProcess (coordinateMeasureOfSemigroup nu hnu) :=
  (hasFiniteStationaryIncrementLaws_coordinateProcess nu hnu).hasStationaryIndependentIncrements

end CoordinateIncrementLaws

end ProbabilityTheory.SIIConstruction
