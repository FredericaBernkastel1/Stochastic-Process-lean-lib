/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Process.StationaryIndependentIncrementsConstruction
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Projective consistency of stationary independent-increment finite laws

The proof is internal to StochLean.  Chronological refinement blocks merge adjacent independent
increment laws by the convolution-semigroup identity; finite-dimensional characteristic-function
uniqueness then proves exact projective consistency.  No external probability package is used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.SIIConstruction

noncomputable def incrementsToPositionsLinear (I : Finset ℝ≥0) :
    (Fin #I → ℝ) →L[ℝ] (I → ℝ) where
  toFun := incrementsToPositions I
  map_add' x y := by
    ext i
    simp [incrementsToPositions, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [incrementsToPositions, Finset.mul_sum]
  cont := by
    rw [continuous_pi_iff]
    intro i
    exact continuous_finset_sum _ fun j _ => continuous_apply j

@[simp]
theorem incrementsToPositionsLinear_apply (I : Finset ℝ≥0) (x : Fin #I → ℝ) :
    incrementsToPositionsLinear I x = incrementsToPositions I x := rfl

theorem finitePositionLaw_eq_map_linear
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0) :
    finitePositionLaw nu I =
      (incrementProduct nu I).map (incrementsToPositionsLinear I) := rfl

theorem charFunDual_finitePositionLaw
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0)
    (L : StrongDual ℝ (I → ℝ)) :
    charFunDual (finitePositionLaw nu I) L =
      ∏ i : Fin #I, charFunDual (nu (orderedGap I i) : Measure ℝ)
        ((L.comp (incrementsToPositionsLinear I)).comp
          (.single ℝ (fun _ : Fin #I => ℝ) i)) := by
  rw [finitePositionLaw_eq_map_linear, charFunDual_map, incrementProduct,
    charFunDual_pi]

/-- Indicator of the selected times lying after the endpoint of a chronological gap. -/
noncomputable def gapTailIndicator (I : Finset ℝ≥0) (i : Fin #I) : I → ℝ :=
  fun t => if orderedTimeWithZero I i.succ ≤ t then 1 else 0

theorem incrementsToPositionsLinear_single_one
    (I : Finset ℝ≥0) (i : Fin #I) :
    incrementsToPositionsLinear I
      ((ContinuousLinearMap.single ℝ (fun _ : Fin #I => ℝ) i) 1) =
      gapTailIndicator I i := by
  ext t
  simp only [incrementsToPositionsLinear_apply, incrementsToPositions,
    ContinuousLinearMap.single_apply, gapTailIndicator]
  have htime : orderedTimeWithZero I i.succ ≤ t ↔
      i ≤ (I.orderIsoOfFin rfl).symm t := by
    change (I.orderIsoOfFin rfl i) ≤ t ↔ _
    constructor
    · intro hle
      simpa only [OrderIso.symm_apply_apply] using
        (I.orderIsoOfFin rfl).symm.monotone hle
    · intro hle
      simpa only [OrderIso.apply_symm_apply] using
        (I.orderIsoOfFin rfl).monotone hle
  by_cases hi : i ≤ (I.orderIsoOfFin rfl).symm t
  · rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, if_pos (htime.mpr hi)]
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp [hi]
  · rw [Finset.sum_eq_zero]
    · rw [if_neg (mt htime.mp hi)]
    · intro b hb
      have hbi : b ≠ i := by
        intro hEq
        subst b
        exact hi (Finset.mem_Iic.mp hb)
      simp [Pi.single_eq_of_ne hbi]

theorem charFunDual_finitePositionLaw_tail
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (I : Finset ℝ≥0)
    (L : StrongDual ℝ (I → ℝ)) :
    charFunDual (finitePositionLaw nu I) L =
      ∏ i : Fin #I, charFunDual (nu (orderedGap I i) : Measure ℝ)
        ((L (gapTailIndicator I i)) • ContinuousLinearMap.id ℝ ℝ) := by
  rw [charFunDual_finitePositionLaw]
  congr 1
  funext i
  congr 1
  ext
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  simpa only [ContinuousLinearMap.single_apply, smul_eq_mul, mul_one] using
    congrArg L (incrementsToPositionsLinear_single_one I i)

section RefinementCombinatorics

variable {m n : ℕ}

/-- The number of selected endpoints strictly before a fine gap endpoint.  The extra terminal
value `m` records fine gaps after the last selected time. -/
noncomputable def refinementBlock (e : Fin m ↪o Fin n) (i : Fin n) : Fin (m + 1) :=
  ⟨#((Finset.univ : Finset (Fin m)).filter fun j => e j < i), by
    have hcard : #((Finset.univ : Finset (Fin m)).filter fun j => e j < i) ≤ m := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => e j < i)
    omega⟩

theorem refinementBlock_val (e : Fin m ↪o Fin n) (i : Fin n) :
    (refinementBlock e i).val =
      #((Finset.univ : Finset (Fin m)).filter fun j => e j < i) := rfl

/-- A fine gap is before selected endpoint `k` exactly when its refinement block is at most `k`. -/
theorem refinementBlock_le_iff (e : Fin m ↪o Fin n) (i : Fin n) (k : Fin m) :
    (refinementBlock e i).val ≤ k.val ↔ i ≤ e k := by
  constructor
  · intro hcard
    by_contra hnot
    have hek : e k < i := lt_of_not_ge hnot
    have hsub : Finset.Iic k ⊆
        (Finset.univ : Finset (Fin m)).filter (fun j => e j < i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (e.monotone (Finset.mem_Iic.mp hj)).trans_lt hek
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hle
    have hcontra : k.val + 1 ≤ (refinementBlock e i).val := by
      simpa only [refinementBlock_val] using hle
    omega
  · intro hik
    have hsub : (Finset.univ : Finset (Fin m)).filter (fun j => e j < i) ⊆
        Finset.Iio k := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_Iio.mpr ((e.lt_iff_lt).mp (hj.trans_le hik))
    have hle := Finset.card_le_card hsub
    simpa only [refinementBlock_val, Fin.card_Iio] using hle

theorem refinementBlock_eq_zero_iff (e : Fin m ↪o Fin n) (i : Fin n)
    (k : Fin m) (hk : k.val = 0) :
    refinementBlock e i = (0 : Fin (m + 1)) ↔ i ≤ e k := by
  rw [Fin.ext_iff]
  simp only [Fin.val_zero]
  have h := refinementBlock_le_iff e i k
  omega

theorem refinementBlock_eq_succ_iff (e : Fin m ↪o Fin n) (i : Fin n)
    (k : Fin m) (hk : k.val + 1 < m) :
    refinementBlock e i = ⟨k.val + 1, by omega⟩ ↔ e k < i ∧ i ≤ e ⟨k.val + 1, hk⟩ := by
  rw [Fin.ext_iff]
  change (refinementBlock e i).val = k.val + 1 ↔ _
  have hleft := refinementBlock_le_iff e i k
  have hright := refinementBlock_le_iff e i ⟨k.val + 1, hk⟩
  constructor
  · intro heq
    constructor
    · by_contra hnot
      have hb := hleft.mpr (le_of_not_gt hnot)
      omega
    · apply hright.mp
      change (refinementBlock e i).val ≤ k.val + 1
      omega
  · rintro ⟨hl, hr⟩
    have hnle : ¬ (refinementBlock e i).val ≤ k.val := by
      intro hb
      exact (not_le_of_gt hl) (hleft.mp hb)
    have hle := hright.mpr hr
    change (refinementBlock e i).val ≤ k.val + 1 at hle
    apply Nat.le_antisymm hle
    omega

theorem refinementBlock_selected (e : Fin m ↪o Fin n) (j : Fin m) :
    refinementBlock e (e j) = j.castSucc := by
  apply Fin.ext
  simp only [refinementBlock_val, Fin.coe_castSucc]
  have hfilter : ((Finset.univ : Finset (Fin m)).filter fun k => e k < e j) =
      Finset.Iio j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact e.lt_iff_lt
  rw [hfilter, Fin.card_Iio]

theorem sum_Ioc_sub {M : Type*} [AddCommGroup M] {n : ℕ}
    (a b : Fin n) (hab : a ≤ b) (f : Fin (n + 1) → M) :
    ∑ i ∈ Finset.Ioc a b, (f i.succ - f i.castSucc) = f b.succ - f a.succ := by
  have ha := Fin.sum_Iic_sub a f
  have hb := Fin.sum_Iic_sub b f
  have hdisj : Disjoint (Finset.Iic a) (Finset.Ioc a b) :=
    Finset.Iic_disjoint_Ioc le_rfl
  have hunion : Finset.Iic a ∪ Finset.Ioc a b = Finset.Iic b :=
    Finset.Iic_union_Ioc_eq_Iic hab
  rw [← hunion, Finset.sum_union hdisj] at hb
  rw [ha] at hb
  calc
    _ = (f a.succ - f 0 + ∑ i ∈ Finset.Ioc a b,
        (f i.succ - f i.castSucc)) - (f a.succ - f 0) := by abel
    _ = (f b.succ - f 0) - (f a.succ - f 0) := by rw [hb]
    _ = _ := by abel

end RefinementCombinatorics

section FinsetRefinement

variable {I J : Finset ℝ≥0}

/-- Order embedding of a smaller finite time set into a containing one. -/
def subsetSubtypeOrderEmbedding (hJI : J ⊆ I) : J ↪o I where
  toFun j := ⟨j, hJI j.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun z : I => (z : ℝ≥0)) h
  map_rel_iff' := Iff.rfl

/-- Chronological ranks in `J` viewed as chronological ranks in `I`. -/
noncomputable def subsetRankEmbedding (hJI : J ⊆ I) : Fin #J ↪o Fin #I :=
  (J.orderIsoOfFin rfl).toOrderEmbedding |>.trans
    (subsetSubtypeOrderEmbedding hJI) |>.trans
    (I.orderIsoOfFin rfl).symm.toOrderEmbedding

theorem subsetRankEmbedding_time (hJI : J ⊆ I) (j : Fin #J) :
    orderedTimeWithZero I (subsetRankEmbedding hJI j).succ =
      orderedTimeWithZero J j.succ := by
  simp only [orderedTimeWithZero_succ]
  rw [← Finset.coe_orderIsoOfFin_apply, ← Finset.coe_orderIsoOfFin_apply]
  let jI : I := ⟨(J.orderIsoOfFin rfl j : ℝ≥0), hJI (J.orderIsoOfFin rfl j).property⟩
  have hrank : subsetRankEmbedding hJI j = (I.orderIsoOfFin rfl).symm jI := rfl
  rw [hrank, OrderIso.apply_symm_apply]

theorem subsetRankEmbedding_symm_apply (hJI : J ⊆ I) (t : J) :
    subsetRankEmbedding hJI ((J.orderIsoOfFin rfl).symm t) =
      (I.orderIsoOfFin rfl).symm ⟨t, hJI t.property⟩ := by
  simp [subsetRankEmbedding, subsetSubtypeOrderEmbedding]
  apply Subtype.ext
  rfl

theorem orderedTimeWithZero_succ_le_iff (K : Finset ℝ≥0) (i : Fin #K) (t : K) :
    orderedTimeWithZero K i.succ ≤ t ↔ i ≤ (K.orderIsoOfFin rfl).symm t := by
  change K.orderIsoOfFin rfl i ≤ t ↔ _
  constructor
  · intro h
    simpa only [OrderIso.symm_apply_apply] using (K.orderIsoOfFin rfl).symm.monotone h
  · intro h
    simpa only [OrderIso.apply_symm_apply] using (K.orderIsoOfFin rfl).monotone h

/-- Coordinate restriction as a continuous linear map. -/
def restrictLinear (hJI : J ⊆ I) : (I → ℝ) →L[ℝ] (J → ℝ) where
  toFun := fun x j => x ⟨j, hJI j.property⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
  cont := by
    rw [continuous_pi_iff]
    intro j
    let jI : I := ⟨j, hJI j.property⟩
    exact continuous_apply jI

@[simp]
theorem restrictLinear_apply (hJI : J ⊆ I) (x : I → ℝ) (j : J) :
    restrictLinear hJI x j = x ⟨j, hJI j.property⟩ := rfl

theorem map_restrict₂_eq_map_restrictLinear (hJI : J ⊆ I) (μ : Measure (I → ℝ)) :
    μ.map (Finset.restrict₂ (π := fun _ : ℝ≥0 => ℝ) hJI) =
      μ.map (restrictLinear hJI) := rfl

theorem restrictLinear_gapTailIndicator_of_refinementBlock_eq
    (hJI : J ⊆ I) (i : Fin #I) (j : Fin #J)
    (hblock : refinementBlock (subsetRankEmbedding hJI) i = j.castSucc) :
    restrictLinear hJI (gapTailIndicator I i) = gapTailIndicator J j := by
  let e := subsetRankEmbedding hJI
  change refinementBlock e i = j.castSucc at hblock
  ext t
  simp only [restrictLinear_apply, gapTailIndicator]
  apply if_congr
  let tI : I := ⟨t, hJI t.property⟩
  let k : Fin #J := (J.orderIsoOfFin rfl).symm t
  have hrank : e k = (I.orderIsoOfFin rfl).symm tI :=
    subsetRankEmbedding_symm_apply hJI t
  rw [orderedTimeWithZero_succ_le_iff I i tI,
    orderedTimeWithZero_succ_le_iff J j t, ← hrank,
    ← refinementBlock_le_iff e i k]
  have hbval := congrArg Fin.val hblock
  change (refinementBlock e i).val = j.val at hbval
  change (refinementBlock e i).val ≤ k.val ↔ j.val ≤ k.val
  omega
  all_goals rfl

theorem restrictLinear_gapTailIndicator_of_terminalBlock
    (hJI : J ⊆ I) (i : Fin #I)
    (hblock : refinementBlock (subsetRankEmbedding hJI) i = Fin.last #J) :
    restrictLinear hJI (gapTailIndicator I i) = 0 := by
  let e := subsetRankEmbedding hJI
  change refinementBlock e i = Fin.last #J at hblock
  ext t
  simp only [restrictLinear_apply, gapTailIndicator, Pi.zero_apply]
  rw [if_neg]
  intro htime
  let tI : I := ⟨t, hJI t.property⟩
  let k : Fin #J := (J.orderIsoOfFin rfl).symm t
  have hrank : e k = (I.orderIsoOfFin rfl).symm tI :=
    subsetRankEmbedding_symm_apply hJI t
  have hle : (refinementBlock e i).val ≤ k.val :=
    (refinementBlock_le_iff e i k).mpr <| by
      rw [hrank]
      exact (orderedTimeWithZero_succ_le_iff I i tI).mp htime
  have hbval := congrArg Fin.val hblock
  change (refinementBlock e i).val = #J at hbval
  omega

theorem sum_orderedGap_Iic (I : Finset ℝ≥0) (b : Fin #I) :
    ∑ i ∈ Finset.Iic b, orderedGap I i = orderedTimeWithZero I b.succ := by
  apply NNReal.coe_injective
  push_cast
  simp_rw [orderedGap,
    NNReal.coe_sub (monotone_orderedTimeWithZero I (Fin.castSucc_le_succ _))]
  simpa using Fin.sum_Iic_sub b (fun k => (orderedTimeWithZero I k : ℝ))

theorem sum_orderedGap_Ioc (I : Finset ℝ≥0) (a b : Fin #I) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ioc a b, orderedGap I i =
      orderedTimeWithZero I b.succ - orderedTimeWithZero I a.succ := by
  apply NNReal.coe_injective
  push_cast
  simp_rw [orderedGap,
    NNReal.coe_sub (monotone_orderedTimeWithZero I (Fin.castSucc_le_succ _))]
  rw [NNReal.coe_sub (monotone_orderedTimeWithZero I
    (show a.succ ≤ b.succ from Fin.succ_le_succ_iff.mpr hab))]
  exact sum_Ioc_sub a b hab (fun k => (orderedTimeWithZero I k : ℝ))

/-- The fine gaps in one chronological refinement block sum to the corresponding coarse gap. -/
theorem sum_orderedGap_refinementBlock (hJI : J ⊆ I) (j : Fin #J) :
    ∑ i with refinementBlock (subsetRankEmbedding hJI) i = j.castSucc, orderedGap I i =
      orderedGap J j := by
  let e := subsetRankEmbedding hJI
  have hJpos : 0 < #J := Nat.zero_lt_of_lt j.isLt
  let j0 : Fin #J := ⟨0, hJpos⟩
  by_cases hj : j = j0
  · rw [hj]
    change ∑ i with refinementBlock e i = j0.castSucc, orderedGap I i = orderedGap J j0
    have hj0cast : j0.castSucc = (0 : Fin (#J + 1)) := by
      apply Fin.ext
      rfl
    rw [hj0cast]
    have hfiber : (Finset.univ.filter fun i : Fin #I =>
        refinementBlock e i = (0 : Fin (#J + 1))) = Finset.Iic (e j0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      exact refinementBlock_eq_zero_iff e i j0 rfl
    rw [hfiber, sum_orderedGap_Iic]
    change orderedTimeWithZero I (e j0).succ =
      orderedTimeWithZero J j0.succ - orderedTimeWithZero J j0.castSucc
    rw [subsetRankEmbedding_time]
    simp [j0]
  · have hjpos : 0 < j.val := by
      have hjne : j.val ≠ 0 := by
        intro hzero
        apply hj
        apply Fin.ext
        simpa [j0] using hzero
      omega
    let prev : Fin #J := ⟨j.val - 1, by omega⟩
    have hprev : prev.val + 1 = j.val := by
      dsimp [prev]
      omega
    have hfiber : (Finset.univ.filter fun i : Fin #I =>
        refinementBlock e i = j.castSucc) = Finset.Ioc (e prev) (e j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc]
      have href := refinementBlock_eq_succ_iff e i prev (by omega)
      have hblock : (⟨prev.val + 1, by omega⟩ : Fin (#J + 1)) = j.castSucc := by
        apply Fin.ext
        simpa using hprev
      have htime : (⟨prev.val + 1, by omega⟩ : Fin #J) = j := by
        apply Fin.ext
        exact hprev
      simpa only [hblock, htime] using href
    rw [hfiber, sum_orderedGap_Ioc]
    · change orderedTimeWithZero I (e j).succ - orderedTimeWithZero I (e prev).succ =
        orderedTimeWithZero J j.succ - orderedTimeWithZero J j.castSucc
      rw [subsetRankEmbedding_time, subsetRankEmbedding_time]
      have hsucc : prev.succ = j.castSucc := by
        apply Fin.ext
        exact hprev
      rw [hsucc]
    · exact e.monotone (by
        change prev.val ≤ j.val
        omega)

end FinsetRefinement

section ScalarCharacteristicFunction

/-- Characteristic function evaluated through the scalar continuous functional `x ↦ c*x`. -/
noncomputable def scalarChar (nu : ℝ≥0 → ProbabilityMeasure ℝ) (s : ℝ≥0) (c : ℝ) : ℂ :=
  charFunDual (nu s : Measure ℝ) (c • ContinuousLinearMap.id ℝ ℝ)

theorem scalarChar_add (nu : ℝ≥0 → ProbabilityMeasure ℝ)
    (hnu : IsConvolutionSemigroup nu) (s t : ℝ≥0) (c : ℝ) :
    scalarChar nu (s + t) c = scalarChar nu s c * scalarChar nu t c := by
  rw [scalarChar, scalarChar, scalarChar, hnu s t]
  exact charFunDual_conv _

@[simp]
theorem scalarChar_zero_coefficient (nu : ℝ≥0 → ProbabilityMeasure ℝ) (s : ℝ≥0) :
    scalarChar nu s 0 = 1 := by
  simp [scalarChar, charFunDual_apply]

theorem scalarChar_sum_of_nonempty (nu : ℝ≥0 → ProbabilityMeasure ℝ)
    (hnu : IsConvolutionSemigroup nu) {k : Type*} (s : Finset k) (hs : s.Nonempty)
    (g : k → ℝ≥0) (c : ℝ) :
    scalarChar nu (∑ i ∈ s, g i) c = ∏ i ∈ s, scalarChar nu (g i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hsempty : s = ∅
      · subst s
        simp
      · rw [Finset.sum_insert ha, Finset.prod_insert ha,
          scalarChar_add nu hnu]
        exact congrArg (scalarChar nu (g a) c * ·)
          (ih (Finset.nonempty_iff_ne_empty.mpr hsempty))

end ScalarCharacteristicFunction

section RefinementCharacteristicProduct

variable {I J : Finset ℝ≥0}

theorem prod_scalarChar_refinementBlock
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)
    (hJI : J ⊆ I) (L : StrongDual ℝ (J → ℝ)) (j : Fin #J) :
    ∏ i with refinementBlock (subsetRankEmbedding hJI) i = j.castSucc,
        scalarChar nu (orderedGap I i)
          (L (restrictLinear hJI (gapTailIndicator I i))) =
      scalarChar nu (orderedGap J j) (L (gapTailIndicator J j)) := by
  let e := subsetRankEmbedding hJI
  let s : Finset (Fin #I) := Finset.univ.filter fun i => refinementBlock e i = j.castSucc
  have hs : s.Nonempty := by
    refine ⟨e j, ?_⟩
    simp [s, refinementBlock_selected]
  have hcoeff : ∀ i ∈ s,
      L (restrictLinear hJI (gapTailIndicator I i)) = L (gapTailIndicator J j) := by
    intro i hi
    have hblock : refinementBlock e i = j.castSucc := by
      simpa [s] using hi
    exact congrArg L
      (restrictLinear_gapTailIndicator_of_refinementBlock_eq hJI i j hblock)
  change ∏ i ∈ s, scalarChar nu (orderedGap I i)
      (L (restrictLinear hJI (gapTailIndicator I i))) = _
  calc
    _ = ∏ i ∈ s, scalarChar nu (orderedGap I i) (L (gapTailIndicator J j)) := by
      exact Finset.prod_congr rfl fun i hi => by rw [hcoeff i hi]
    _ = scalarChar nu (∑ i ∈ s, orderedGap I i) (L (gapTailIndicator J j)) :=
      (scalarChar_sum_of_nonempty nu hnu s hs (orderedGap I)
        (L (gapTailIndicator J j))).symm
    _ = _ := by
      rw [show ∑ i ∈ s, orderedGap I i = orderedGap J j from by
        simpa [s, e] using sum_orderedGap_refinementBlock hJI j]

theorem prod_scalarChar_terminalBlock
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hJI : J ⊆ I)
    (L : StrongDual ℝ (J → ℝ)) :
    ∏ i with refinementBlock (subsetRankEmbedding hJI) i = Fin.last #J,
        scalarChar nu (orderedGap I i)
          (L (restrictLinear hJI (gapTailIndicator I i))) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hblock : refinementBlock (subsetRankEmbedding hJI) i = Fin.last #J := by
    simpa using hi
  rw [restrictLinear_gapTailIndicator_of_terminalBlock hJI i hblock]
  simp

theorem prod_scalarChar_refinement
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)
    (hJI : J ⊆ I) (L : StrongDual ℝ (J → ℝ)) :
    ∏ i : Fin #I, scalarChar nu (orderedGap I i)
        (L (restrictLinear hJI (gapTailIndicator I i))) =
      ∏ j : Fin #J, scalarChar nu (orderedGap J j) (L (gapTailIndicator J j)) := by
  let e := subsetRankEmbedding hJI
  rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin #I))
    (refinementBlock e)]
  rw [Fin.prod_univ_castSucc]
  have hcoarse : (∏ j : Fin #J, ∏ i ∈ (Finset.univ : Finset (Fin #I)) with
      refinementBlock e i = j.castSucc,
      scalarChar nu (orderedGap I i)
        (L (restrictLinear hJI (gapTailIndicator I i)))) =
      ∏ j : Fin #J, scalarChar nu (orderedGap J j) (L (gapTailIndicator J j)) := by
    apply Finset.prod_congr rfl
    intro j _
    simpa [e] using prod_scalarChar_refinementBlock nu hnu hJI L j
  have hterminal : (∏ i ∈ (Finset.univ : Finset (Fin #I)) with
      refinementBlock e i = Fin.last #J,
      scalarChar nu (orderedGap I i)
        (L (restrictLinear hJI (gapTailIndicator I i)))) = 1 := by
    simpa [e] using prod_scalarChar_terminalBlock nu hJI L
  rw [hcoarse, hterminal, mul_one]

end RefinementCharacteristicProduct

/-- The finite-dimensional position laws obtained from a real convolution semigroup are
projectively consistent. -/
theorem isProjectiveMeasureFamily_finitePositionLaw
    (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu) :
    IsProjectiveMeasureFamily (α := fun _ : ℝ≥0 => ℝ) (finitePositionLaw nu) := by
  intro I J hJI
  rw [map_restrict₂_eq_map_restrictLinear]
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map]
  rw [charFunDual_finitePositionLaw_tail, charFunDual_finitePositionLaw_tail]
  change (∏ j : Fin #J, scalarChar nu (orderedGap J j) (L (gapTailIndicator J j))) =
    ∏ i : Fin #I, scalarChar nu (orderedGap I i)
      (L (restrictLinear hJI (gapTailIndicator I i)))
  exact (prod_scalarChar_refinement nu hnu hJI L).symm

section CoordinateSemigroup

variable (nu : ℝ≥0 → ProbabilityMeasure ℝ) (hnu : IsConvolutionSemigroup nu)

/-- Canonical coordinate-product measure constructed directly from a convolution semigroup. -/
noncomputable def coordinateMeasureOfSemigroup : Measure (ℝ≥0 → ℝ) :=
  coordinateMeasure nu (isProjectiveMeasureFamily_finitePositionLaw nu hnu)

instance coordinateMeasureOfSemigroup.instIsProbabilityMeasure :
    IsProbabilityMeasure (coordinateMeasureOfSemigroup nu hnu) := by
  unfold coordinateMeasureOfSemigroup
  infer_instance

instance coordinateMeasureOfSemigroup.instIsFiniteMeasure :
    IsFiniteMeasure (coordinateMeasureOfSemigroup nu hnu) := by infer_instance

/-- Every prescribed finite position law is recovered from the canonical semigroup coordinate
measure. -/
theorem hasLaw_restrict_of_semigroup (I : Finset ℝ≥0) :
    HasLaw I.restrict (finitePositionLaw nu I) (coordinateMeasureOfSemigroup nu hnu) := by
  simpa only [coordinateMeasureOfSemigroup] using
    hasLaw_restrict nu (isProjectiveMeasureFamily_finitePositionLaw nu hnu) I

end CoordinateSemigroup

end ProbabilityTheory.SIIConstruction
