/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.CumulativeSumVolume
public import StochLean.ForMathlib.MeasureTheory.WithDensityEquiv
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Finite-dimensional exponential-arrival calculation

This module records the analytic heart of Klenke 5.36.  A finite ordered partition and an
arbitrary vector of arrival counts determine a product of ordered simplices.  Integrating the
constant remaining after the exponential overshoot integral gives exactly the product of the
corresponding Poisson atom probabilities.
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory.PoissonProcess

noncomputable section

/-- A finite independent exponential family has the product exponential density with respect to
finite-dimensional Lebesgue measure. -/
theorem pi_expMeasure_eq_withDensity (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (Measure.pi fun _ : Fin m ↦ expMeasure r) =
      volume.withDensity (fun x : Fin m → ℝ ↦ ∏ i, exponentialPDF r (x i)) := by
  let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  induction m with
  | zero =>
      rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ expMeasure r)]
      rw [Measure.volume_pi_eq_dirac (α := fun _ : Fin 0 ↦ ℝ)]
      simp
  | succ m ih =>
      let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0
      apply e.measurableEmbedding.map_injective
      rw [(measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ expMeasure r) 0).map_eq]
      rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).map_withDensity_equiv
        e]
      rw [ih]
      change (volume.withDensity (exponentialPDF r)).prod
          (volume.withDensity fun x : Fin m → ℝ ↦ ∏ i, exponentialPDF r (x i)) = _
      rw [MeasureTheory.prod_withDensity]
      · congr 1
        funext p
        simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv_zero, Fin.consEquiv_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
      · exact (measurable_exponentialPDFReal r).ennreal_ofReal
      · exact Finset.univ.measurable_prod fun i _ ↦
          (measurable_exponentialPDFReal r).ennreal_ofReal.comp (measurable_pi_apply i)

/-- Every cumulative coordinate of a finite exponential family is atomless. -/
lemma pi_expMeasure_cumulative_eq_zero {m : ℕ} (rate : NNReal) (hr : 0 < rate)
    (i : Fin m) (c : ℝ) :
    (Measure.pi fun _ : Fin m ↦ expMeasure rate)
      {w | cumulativeLinearEquiv m w i = c} = 0 := by
  rw [pi_expMeasure_eq_withDensity m (r := (rate : ℝ)) (by exact_mod_cast hr)]
  apply withDensity_absolutelyContinuous volume _
  let B : Set (Fin m → ℝ) := {y | y i = c}
  have hB : MeasurableSet B := by
    change MeasurableSet ((fun y : Fin m → ℝ ↦ y i) ⁻¹' {c})
    exact measurable_pi_apply i (measurableSet_singleton c)
  change volume (cumulativeLinearEquiv m ⁻¹' B) = 0
  rw [(measurePreserving_cumulativeLinearEquiv m).measure_preimage hB.nullMeasurableSet]
  change (Measure.pi fun _ : Fin m ↦ (volume : Measure ℝ)) B = 0
  exact Measure.pi_hyperplane (fun _ : Fin m ↦ (volume : Measure ℝ)) i c

/-- Translation of an ordered simplex into a time interval starting at `a`. -/
def shiftedOrderedSimplex (n : ℕ) (a d : ℝ) : Set (Fin n → ℝ) :=
  (fun x ↦ x + fun _ ↦ a) '' MeasureTheory.orderedSimplex n d

lemma measurableSet_shiftedOrderedSimplex (n : ℕ) (a d : ℝ) :
    MeasurableSet (shiftedOrderedSimplex n a d) := by
  let e := MeasurableEquiv.addRight (fun _ : Fin n ↦ a)
  change MeasurableSet (e '' MeasureTheory.orderedSimplex n d)
  exact e.measurableSet_image.mpr (MeasureTheory.measurableSet_orderedSimplex n d)

theorem volume_shiftedOrderedSimplex (n : ℕ) (a : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    volume (shiftedOrderedSimplex n a d) = ENNReal.ofReal (d ^ n / (n.factorial : ℝ)) := by
  let e := MeasurableEquiv.addRight (fun _ : Fin n ↦ a)
  have hp : MeasurePreserving e volume volume := measurePreserving_add_right volume _
  rw [← hp.measure_preimage (measurableSet_shiftedOrderedSimplex n a d).nullMeasurableSet]
  have hpre : e ⁻¹' shiftedOrderedSimplex n a d = MeasureTheory.orderedSimplex n d := by
    exact Set.preimage_image_eq _ e.injective
  rw [hpre, MeasureTheory.volume_orderedSimplex n hd]

lemma shiftedOrderedSimplex_nonneg {n : ℕ} {a d : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ shiftedOrderedSimplex n a d) (ha : 0 ≤ a) (i : Fin n) : 0 ≤ y i := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact add_nonneg (MeasureTheory.orderedSimplex_nonneg hz i) ha

lemma shiftedOrderedSimplex_monotone {n : ℕ} {a d : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ shiftedOrderedSimplex n a d) : Monotone y := by
  obtain ⟨z, hz, rfl⟩ := hy
  intro i j hij
  simpa only [Pi.add_apply, add_comm] using
    add_le_add_right (MeasureTheory.orderedSimplex_monotone hz hij) a

lemma shiftedOrderedSimplex_lower {n : ℕ} {a d : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ shiftedOrderedSimplex n a d) (i : Fin n) : a ≤ y i := by
  obtain ⟨z, hz, rfl⟩ := hy
  simpa only [Pi.add_apply, add_comm, add_zero] using
    add_le_add_right (MeasureTheory.orderedSimplex_nonneg hz i) a

lemma shiftedOrderedSimplex_upper {n : ℕ} {a d : ℝ} {y : Fin n → ℝ}
    (hy : y ∈ shiftedOrderedSimplex n a d) (i : Fin n) : y i ≤ a + d := by
  obtain ⟨z, hz, rfl⟩ := hy
  simpa only [Pi.add_apply, add_comm] using
    add_le_add_left (MeasureTheory.orderedSimplex_le hz i) a

lemma mem_shiftedOrderedSimplex_iff {n : ℕ} {a d : ℝ} (hd : 0 ≤ d)
    (y : Fin n → ℝ) :
    y ∈ shiftedOrderedSimplex n a d ↔
      Monotone y ∧ (∀ i, a ≤ y i) ∧ (∀ i, y i ≤ a + d) := by
  constructor
  · intro hy
    exact ⟨shiftedOrderedSimplex_monotone hy,
      fun i ↦ shiftedOrderedSimplex_lower hy i,
      fun i ↦ shiftedOrderedSimplex_upper hy i⟩
  · rintro ⟨hmono, hlower, hupper⟩
    let z : Fin n → ℝ := fun i ↦ y i - a
    have hz : z ∈ MeasureTheory.orderedSimplex n d :=
      (MeasureTheory.mem_orderedSimplex_iff hd z).mpr ⟨
        fun i ↦ sub_nonneg.mpr (hlower i),
        fun i j hij ↦ sub_le_sub_right (hmono hij) a,
        fun i ↦ by dsimp [z]; linarith [hupper i]⟩
    refine ⟨z, hz, ?_⟩
    funext i
    simp [z]

/-- Split a finite coordinate vector into its first `k` and remaining `l` coordinates. -/
def splitFinMeasurableEquiv (k l : ℕ) :
    (Fin (k + l) → ℝ) ≃ᵐ (Fin k → ℝ) × (Fin l → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + l) ↦ ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l ↦ ℝ))

@[simp]
lemma splitFinMeasurableEquiv_fst (k l : ℕ) (x : Fin (k + l) → ℝ) (i : Fin k) :
    (splitFinMeasurableEquiv k l x).1 i = x (Fin.castAdd l i) := by
  simp only [splitFinMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]
  change (Equiv.piCongrLeft (fun _ : Fin (k + l) ↦ ℝ) finSumFinEquiv).symm x
    (Sum.inl i) = _
  rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_left]

@[simp]
lemma splitFinMeasurableEquiv_snd (k l : ℕ) (x : Fin (k + l) → ℝ) (i : Fin l) :
    (splitFinMeasurableEquiv k l x).2 i = x (Fin.natAdd k i) := by
  simp only [splitFinMeasurableEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply]
  change (Equiv.piCongrLeft (fun _ : Fin (k + l) ↦ ℝ) finSumFinEquiv).symm x
    (Sum.inr i) = _
  rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_right]

lemma monotone_of_splitFin {k l : ℕ} {x : Fin (k + l) → ℝ}
    (hleft : Monotone (splitFinMeasurableEquiv k l x).1)
    (hright : Monotone (splitFinMeasurableEquiv k l x).2)
    (hcross : ∀ i j, (splitFinMeasurableEquiv k l x).1 i ≤
      (splitFinMeasurableEquiv k l x).2 j) : Monotone x := by
  intro i j hij
  by_cases hi : i.val < k
  · let i' : Fin k := ⟨i.val, hi⟩
    have hii : Fin.castAdd l i' = i := Fin.ext rfl
    by_cases hj : j.val < k
    · let j' : Fin k := ⟨j.val, hj⟩
      have hjj : Fin.castAdd l j' = j := Fin.ext rfl
      rw [← hii, ← hjj, ← splitFinMeasurableEquiv_fst k l x i',
        ← splitFinMeasurableEquiv_fst k l x j']
      exact hleft (by simpa [i', j'] using hij)
    · let j' : Fin l := ⟨j.val - k, by omega⟩
      have hjj : Fin.natAdd k j' = j := Fin.ext (by simp [j']; omega)
      rw [← hii, ← hjj, ← splitFinMeasurableEquiv_fst k l x i',
        ← splitFinMeasurableEquiv_snd k l x j']
      exact hcross i' j'
  · have hj : ¬ j.val < k := fun h ↦ hi (lt_of_le_of_lt hij h)
    let i' : Fin l := ⟨i.val - k, by omega⟩
    let j' : Fin l := ⟨j.val - k, by omega⟩
    have hii : Fin.natAdd k i' = i := Fin.ext (by simp [i']; omega)
    have hjj : Fin.natAdd k j' = j := Fin.ext (by simp [j']; omega)
    rw [← hii, ← hjj, ← splitFinMeasurableEquiv_snd k l x i',
      ← splitFinMeasurableEquiv_snd k l x j']
    apply hright
    change i.val - k ≤ j.val - k
    omega

lemma measurePreserving_splitFinMeasurableEquiv (k l : ℕ) :
    MeasurePreserving (splitFinMeasurableEquiv k l) volume volume := by
  exact (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin k ⊕ Fin l ↦ ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (k + l) ↦ ℝ)
      finSumFinEquiv).symm

/-- Split the last coordinate from a finite real vector. -/
def splitLastMeasurableEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).trans
    MeasurableEquiv.prodComm

@[simp]
lemma splitLastMeasurableEquiv_fst (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin n) :
    (splitLastMeasurableEquiv n x).1 i = x i.castSucc := by
  simp [splitLastMeasurableEquiv, MeasurableEquiv.piFinSuccAbove_apply]
  rfl

@[simp]
lemma splitLastMeasurableEquiv_snd (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (splitLastMeasurableEquiv n x).2 = x (Fin.last n) := by
  simp [splitLastMeasurableEquiv, MeasurableEquiv.piFinSuccAbove_apply]
  rfl

@[simp]
lemma splitLastMeasurableEquiv_symm_castSucc (n : ℕ) (p : (Fin n → ℝ) × ℝ)
    (i : Fin n) : (splitLastMeasurableEquiv n).symm p i.castSucc = p.1 i := by
  have h := congrArg (fun q ↦ q.1 i) ((splitLastMeasurableEquiv n).apply_symm_apply p)
  simpa only [splitLastMeasurableEquiv_fst] using h

@[simp]
lemma splitLastMeasurableEquiv_symm_last (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    (splitLastMeasurableEquiv n).symm p (Fin.last n) = p.2 := by
  have h := congrArg Prod.snd ((splitLastMeasurableEquiv n).apply_symm_apply p)
  simpa only [splitLastMeasurableEquiv_snd] using h

lemma monotone_splitLast_symm {n : ℕ} {y : Fin n → ℝ} {z : ℝ}
    (hmono : Monotone y) (hle : ∀ i, y i ≤ z) :
    Monotone ((splitLastMeasurableEquiv n).symm (y, z)) := by
  intro i j hij
  by_cases hi : i.val < n
  · let i' : Fin n := ⟨i.val, hi⟩
    have hii : i'.castSucc = i := Fin.ext rfl
    by_cases hj : j.val < n
    · let j' : Fin n := ⟨j.val, hj⟩
      have hjj : j'.castSucc = j := Fin.ext rfl
      rw [← hii, ← hjj, splitLastMeasurableEquiv_symm_castSucc,
        splitLastMeasurableEquiv_symm_castSucc]
      exact hmono (by simpa [i', j'] using hij)
    · have hjj : j = Fin.last n := Fin.ext (by simp; omega)
      rw [← hii, hjj, splitLastMeasurableEquiv_symm_castSucc,
        splitLastMeasurableEquiv_symm_last]
      exact hle i'
  · have hii : i = Fin.last n := Fin.ext (by simp; omega)
    have hjj : j = Fin.last n := Fin.ext (by simp; omega)
    simp [hii, hjj]

lemma measurePreserving_splitLastMeasurableEquiv (n : ℕ) :
    MeasurePreserving (splitLastMeasurableEquiv n) volume volume := by
  exact (Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))

/-- Exponential overshoot integral beyond a nonnegative terminal time. -/
lemma lintegral_exponentialPDF_Ioi {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T) :
    ∫⁻ x in Ioi T, exponentialPDF r x = ENNReal.ofReal (Real.exp (-(r * T))) := by
  let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← withDensity_apply _ measurableSet_Ioi]
  change expMeasure r (Ioi T) = _
  rw [← compl_Iic, measure_compl measurableSet_Iic (by simp), measure_univ]
  rw [← ofReal_cdf (expMeasure r) T, cdf_expMeasure_eq hr T, if_pos hT]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · congr 1
    ring
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hr.le hT)))

/-- Total number of arrivals encoded by a list of `(count, left endpoint, duration)` blocks. -/
def blockTotal : List (ℕ × ℝ × ℝ) → ℕ
  | [] => 0
  | b :: bs => b.1 + blockTotal bs

/-- Ordered arrival-time chamber for a list of time blocks. -/
def listArrivalChamber : (bs : List (ℕ × ℝ × ℝ)) → Set (Fin (blockTotal bs) → ℝ)
  | [] => Set.univ
  | b :: bs =>
      splitFinMeasurableEquiv b.1 (blockTotal bs) ⁻¹'
        (shiftedOrderedSimplex b.1 b.2.1 b.2.2 ×ˢ listArrivalChamber bs)

lemma listArrivalChamber_lower {bs : List (ℕ × ℝ × ℝ)} {a : ℝ}
    {y : Fin (blockTotal bs) → ℝ} (hy : y ∈ listArrivalChamber bs)
    (hstart : ∀ b ∈ bs, a ≤ b.2.1) (i : Fin (blockTotal bs)) : a ≤ y i := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
      change Fin (b.1 + blockTotal bs) → ℝ at y
      change Fin (b.1 + blockTotal bs) at i
      change (splitFinMeasurableEquiv b.1 (blockTotal bs) y).1 ∈
          shiftedOrderedSimplex b.1 b.2.1 b.2.2 ∧
        (splitFinMeasurableEquiv b.1 (blockTotal bs) y).2 ∈ listArrivalChamber bs at hy
      by_cases hi : i.val < b.1
      · let i' : Fin b.1 := ⟨i.val, hi⟩
        have hii : Fin.castAdd (blockTotal bs) i' = i := Fin.ext rfl
        rw [← hii, ← splitFinMeasurableEquiv_fst b.1 (blockTotal bs) y i']
        exact (hstart b (by simp)).trans (shiftedOrderedSimplex_lower hy.1 i')
      · let i' : Fin (blockTotal bs) := ⟨i.val - b.1, by omega⟩
        have hii : Fin.natAdd b.1 i' = i := Fin.ext (by simp [i']; omega)
        rw [← hii, ← splitFinMeasurableEquiv_snd b.1 (blockTotal bs) y i']
        exact ih hy.2 (fun c hc ↦ hstart c (by simp [hc])) i'

lemma listArrivalChamber_upper {bs : List (ℕ × ℝ × ℝ)} {T : ℝ}
    {y : Fin (blockTotal bs) → ℝ} (hy : y ∈ listArrivalChamber bs)
    (hend : ∀ b ∈ bs, b.2.1 + b.2.2 ≤ T) (i : Fin (blockTotal bs)) : y i ≤ T := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
      change Fin (b.1 + blockTotal bs) → ℝ at y
      change Fin (b.1 + blockTotal bs) at i
      change (splitFinMeasurableEquiv b.1 (blockTotal bs) y).1 ∈
          shiftedOrderedSimplex b.1 b.2.1 b.2.2 ∧
        (splitFinMeasurableEquiv b.1 (blockTotal bs) y).2 ∈ listArrivalChamber bs at hy
      by_cases hi : i.val < b.1
      · let i' : Fin b.1 := ⟨i.val, hi⟩
        have hii : Fin.castAdd (blockTotal bs) i' = i := Fin.ext rfl
        rw [← hii, ← splitFinMeasurableEquiv_fst b.1 (blockTotal bs) y i']
        exact (shiftedOrderedSimplex_upper hy.1 i').trans (hend b (by simp))
      · let i' : Fin (blockTotal bs) := ⟨i.val - b.1, by omega⟩
        have hii : Fin.natAdd b.1 i' = i := Fin.ext (by simp [i']; omega)
        rw [← hii, ← splitFinMeasurableEquiv_snd b.1 (blockTotal bs) y i']
        exact ih hy.2 (fun c hc ↦ hend c (by simp [hc])) i'

/-- Strong block ordering sufficient for the concatenated chamber to be globally ordered. -/
def OrderedArrivalBlocks : List (ℕ × ℝ × ℝ) → Prop
  | [] => True
  | b :: bs =>
      (∀ c ∈ bs, b.2.1 + b.2.2 ≤ c.2.1) ∧ OrderedArrivalBlocks bs

lemma listArrivalChamber_monotone {bs : List (ℕ × ℝ × ℝ)}
    {y : Fin (blockTotal bs) → ℝ} (hy : y ∈ listArrivalChamber bs)
    (hordered : OrderedArrivalBlocks bs) : Monotone y := by
  induction bs with
  | nil => exact fun i ↦ Fin.elim0 i
  | cons b bs ih =>
      change (splitFinMeasurableEquiv b.1 (blockTotal bs) y).1 ∈
          shiftedOrderedSimplex b.1 b.2.1 b.2.2 ∧
        (splitFinMeasurableEquiv b.1 (blockTotal bs) y).2 ∈ listArrivalChamber bs at hy
      change (∀ c ∈ bs, b.2.1 + b.2.2 ≤ c.2.1) ∧ OrderedArrivalBlocks bs at hordered
      apply monotone_of_splitFin (shiftedOrderedSimplex_monotone hy.1)
        (ih hy.2 hordered.2)
      intro i j
      exact (shiftedOrderedSimplex_upper hy.1 i).trans
        (listArrivalChamber_lower hy.2 hordered.1 j)

lemma measurableSet_listArrivalChamber : ∀ bs, MeasurableSet (listArrivalChamber bs)
  | [] => MeasurableSet.univ
  | b :: bs =>
      (measurableSet_shiftedOrderedSimplex b.1 b.2.1 b.2.2).prod
        (measurableSet_listArrivalChamber bs) |>.preimage
          (splitFinMeasurableEquiv b.1 (blockTotal bs)).measurable

/-- The global arrival chamber has the product of the individual ordered-simplex volumes. -/
theorem volume_listArrivalChamber (bs : List (ℕ × ℝ × ℝ))
    (hd : ∀ b ∈ bs, 0 ≤ b.2.2) :
    volume (listArrivalChamber bs) =
      (bs.map fun b ↦ ENNReal.ofReal (b.2.2 ^ b.1 / (b.1.factorial : ℝ))).prod := by
  induction bs with
  | nil =>
      rw [listArrivalChamber, volume_pi]
      exact Measure.pi_empty_univ (fun _ : Fin 0 ↦ (volume : Measure ℝ))
  | cons b bs ih =>
      rw [listArrivalChamber]
      change volume (splitFinMeasurableEquiv b.1 (blockTotal bs) ⁻¹'
        (shiftedOrderedSimplex b.1 b.2.1 b.2.2 ×ˢ listArrivalChamber bs)) = _
      rw [(measurePreserving_splitFinMeasurableEquiv b.1 (blockTotal bs)).measure_preimage
        ((measurableSet_shiftedOrderedSimplex b.1 b.2.1 b.2.2).prod
          (measurableSet_listArrivalChamber bs)).nullMeasurableSet]
      change (volume.prod volume)
        (shiftedOrderedSimplex b.1 b.2.1 b.2.2 ×ˢ listArrivalChamber bs) = _
      rw [Measure.prod_prod, volume_shiftedOrderedSimplex b.1 b.2.1 (hd b (by simp)),
        ih (fun c hc ↦ hd c (by simp [hc]))]
      simp

lemma prod_exponentialPDF_of_nonneg {m : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∏ i, exponentialPDF r (x i) =
      ENNReal.ofReal (r ^ m * Real.exp (-(r * ∑ i, x i))) := by
  simp_rw [exponentialPDF_of_nonneg (hx _)]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  · intro i _
    exact mul_nonneg hr (Real.exp_pos _).le

/-- Cumulative gaps followed by splitting off the final arrival coordinate. -/
def exponentialArrivalMeasurableEquiv (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (cumulativeMeasurableEquiv (n + 1)).trans (splitLastMeasurableEquiv n)

lemma measurePreserving_exponentialArrivalMeasurableEquiv (n : ℕ) :
    MeasurePreserving (exponentialArrivalMeasurableEquiv n) volume volume := by
  exact (measurePreserving_splitLastMeasurableEquiv n).comp
    (measurePreserving_cumulativeLinearEquiv (n + 1))

lemma exponentialArrival_density_on_chamber {bs : List (ℕ × ℝ × ℝ)}
    {T r : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hstart : ∀ b ∈ bs, 0 ≤ b.2.1)
    (hend : ∀ b ∈ bs, b.2.1 + b.2.2 ≤ T)
    (hordered : OrderedArrivalBlocks bs)
    {p : (Fin (blockTotal bs) → ℝ) × ℝ}
    (hp : p ∈ listArrivalChamber bs ×ˢ Ioi T) :
    (∏ i, exponentialPDF r
      ((exponentialArrivalMeasurableEquiv (blockTotal bs)).symm p i)) =
      ENNReal.ofReal
        (r ^ (blockTotal bs + 1) * Real.exp (-(r * p.2))) := by
  let s := (splitLastMeasurableEquiv (blockTotal bs)).symm p
  have hsmono : Monotone s := monotone_splitLast_symm
    (listArrivalChamber_monotone hp.1 hordered)
    (fun i ↦ (listArrivalChamber_upper hp.1 hend i).trans hp.2.le)
  have hsnonneg : ∀ i, 0 ≤ s i := by
    intro i
    by_cases hi : i.val < blockTotal bs
    · let i' : Fin (blockTotal bs) := ⟨i.val, hi⟩
      have hii : i'.castSucc = i := Fin.ext rfl
      change 0 ≤ (splitLastMeasurableEquiv (blockTotal bs)).symm p i
      rw [← hii, splitLastMeasurableEquiv_symm_castSucc]
      exact listArrivalChamber_lower hp.1 hstart i'
    · have hii : i = Fin.last (blockTotal bs) := Fin.ext (by simp; omega)
      change 0 ≤ (splitLastMeasurableEquiv (blockTotal bs)).symm p i
      rw [hii, splitLastMeasurableEquiv_symm_last]
      exact hT.trans hp.2.le
  have hgap : ∀ i, 0 ≤ (cumulativeLinearEquiv (blockTotal bs + 1)).symm s i :=
    cumulativeLinearEquiv_symm_nonneg hsmono hsnonneg
  change (∏ i, exponentialPDF r
    ((cumulativeLinearEquiv (blockTotal bs + 1)).symm s i)) = _
  rw [prod_exponentialPDF_of_nonneg hr _ hgap]
  have hsum : ∑ i, (cumulativeLinearEquiv (blockTotal bs + 1)).symm s i = p.2 := by
    rw [sum_cumulativeLinearEquiv_symm]
    change (splitLastMeasurableEquiv (blockTotal bs)).symm p
      (Fin.last (blockTotal bs)) = p.2
    rw [splitLastMeasurableEquiv_symm_last]
  rw [hsum]

/-- Gap vectors whose cumulative arrival times realize the prescribed blocks and whose next
arrival lies strictly after `T`. -/
def exponentialArrivalGapEvent (bs : List (ℕ × ℝ × ℝ)) (T : ℝ) :
    Set (Fin (blockTotal bs + 1) → ℝ) :=
  exponentialArrivalMeasurableEquiv (blockTotal bs) ⁻¹'
    (listArrivalChamber bs ×ˢ Ioi T)

lemma measurableSet_exponentialArrivalGapEvent (bs : List (ℕ × ℝ × ℝ)) (T : ℝ) :
    MeasurableSet (exponentialArrivalGapEvent bs T) :=
  ((measurableSet_listArrivalChamber bs).prod measurableSet_Ioi).preimage
    (exponentialArrivalMeasurableEquiv (blockTotal bs)).measurable

/-- The first `K + 1` exponential gaps assign the prescribed counts to every block and put the
next arrival after `T` with the expected exponential-density mass. -/
theorem pi_expMeasure_arrivalGapEvent {bs : List (ℕ × ℝ × ℝ)}
    {T : ℝ} (rate : NNReal) (hr : 0 < rate) (hT : 0 ≤ T)
    (hstart : ∀ b ∈ bs, 0 ≤ b.2.1)
    (hend : ∀ b ∈ bs, b.2.1 + b.2.2 ≤ T)
    (hordered : OrderedArrivalBlocks bs) :
    (Measure.pi fun _ : Fin (blockTotal bs + 1) ↦ expMeasure rate)
        (exponentialArrivalGapEvent bs T) =
      ENNReal.ofReal
          ((rate : ℝ) ^ blockTotal bs * Real.exp (-((rate : ℝ) * T))) *
        volume (listArrivalChamber bs) := by
  rw [pi_expMeasure_eq_withDensity (blockTotal bs + 1) (r := (rate : ℝ))
    (by exact_mod_cast hr)]
  let e := exponentialArrivalMeasurableEquiv (blockTotal bs)
  let S := listArrivalChamber bs ×ˢ Ioi T
  have hS : MeasurableSet S := (measurableSet_listArrivalChamber bs).prod measurableSet_Ioi
  change (volume.withDensity (fun x : Fin (blockTotal bs + 1) → ℝ ↦
    ∏ i, exponentialPDF rate (x i))) (e ⁻¹' S) = _
  rw [← Measure.map_apply e.measurable hS]
  rw [(measurePreserving_exponentialArrivalMeasurableEquiv
    (blockTotal bs)).map_withDensity_equiv e]
  rw [withDensity_apply _ hS]
  change (∫⁻ p in S, ∏ i, exponentialPDF (rate : ℝ)
    ((exponentialArrivalMeasurableEquiv (blockTotal bs)).symm p i)) = _
  have hdensity : Set.EqOn
      (fun p ↦ ∏ i, exponentialPDF (rate : ℝ)
        ((exponentialArrivalMeasurableEquiv (blockTotal bs)).symm p i))
      (fun p ↦ ENNReal.ofReal ((rate : ℝ) ^ (blockTotal bs + 1) *
        Real.exp (-((rate : ℝ) * p.2)))) S :=
    fun p hp ↦ exponentialArrival_density_on_chamber
      hr.le hT hstart hend hordered hp
  rw [setLIntegral_congr_fun (μ := volume) hS hdensity]
  have hinner : ∫⁻ z in Ioi T,
      ENNReal.ofReal
        ((rate : ℝ) ^ (blockTotal bs + 1) * Real.exp (-((rate : ℝ) * z))) =
      ENNReal.ofReal
        ((rate : ℝ) ^ blockTotal bs * Real.exp (-((rate : ℝ) * T))) := by
    have hpoint : Set.EqOn
        (fun z ↦ ENNReal.ofReal ((rate : ℝ) ^ (blockTotal bs + 1) *
          Real.exp (-((rate : ℝ) * z))))
        (fun z ↦ ENNReal.ofReal ((rate : ℝ) ^ blockTotal bs) *
          exponentialPDF rate z) (Ioi T) := by
      intro z hz
      change ENNReal.ofReal ((rate : ℝ) ^ (blockTotal bs + 1) *
          Real.exp (-((rate : ℝ) * z))) =
        ENNReal.ofReal ((rate : ℝ) ^ blockTotal bs) * exponentialPDF rate z
      rw [show (rate : ℝ) ^ (blockTotal bs + 1) *
          Real.exp (-((rate : ℝ) * z)) =
          (rate : ℝ) ^ blockTotal bs *
            ((rate : ℝ) * Real.exp (-((rate : ℝ) * z))) by ring]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← exponentialPDF_of_nonneg (hT.trans hz.le)]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpoint]
    change (∫⁻ x, ENNReal.ofReal ((rate : ℝ) ^ blockTotal bs) *
      exponentialPDF rate x ∂(volume.restrict (Ioi T))) = _
    rw [lintegral_const_mul (μ := volume.restrict (Ioi T))
      (f := fun x ↦ exponentialPDF (rate : ℝ) x)
      (ENNReal.ofReal ((rate : ℝ) ^ blockTotal bs))
      (measurable_exponentialPDFReal rate).ennreal_ofReal]
    change ENNReal.ofReal ((rate : ℝ) ^ blockTotal bs) *
      (∫⁻ x in Ioi T, exponentialPDF rate x) = _
    rw [lintegral_exponentialPDF_Ioi (r := (rate : ℝ))
      (by exact_mod_cast hr) hT]
    rw [← ENNReal.ofReal_mul (by positivity)]
  change (∫⁻ x in listArrivalChamber bs ×ˢ Ioi T,
    ENNReal.ofReal ((rate : ℝ) ^ (blockTotal bs + 1) *
      Real.exp (-((rate : ℝ) * x.2))) ∂(volume.prod volume)) = _
  rw [setLIntegral_prod (μ := volume) (ν := volume) _ (by fun_prop)]
  simp_rw [hinner]
  rw [setLIntegral_const]

/-- Blocks determined by a finite time grid and the desired interval counts. -/
def partitionBlocks {n : ℕ} (k : Fin n → ℕ) (t : Fin (n + 1) → NNReal) :
    List (ℕ × ℝ × ℝ) :=
  List.ofFn fun i ↦
    (k i, (t i.castSucc : ℝ), ((t i.succ - t i.castSucc : NNReal) : ℝ))

lemma blockTotal_map {S : Type*} (l : List S) (f : S → ℕ × ℝ × ℝ) :
    blockTotal (l.map f) = (l.map fun s ↦ (f s).1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [blockTotal, ih]

lemma blockTotal_partitionBlocks {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) :
    blockTotal (partitionBlocks k t) = ∑ i, k i := by
  rw [partitionBlocks, List.ofFn_eq_map, blockTotal_map]
  rw [← List.ofFn_eq_map]
  exact List.sum_ofFn

lemma partitionBlocks_start_nonneg {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) :
    ∀ b ∈ partitionBlocks k t, 0 ≤ b.2.1 := by
  rw [partitionBlocks, List.forall_mem_ofFn_iff]
  intro i
  positivity

lemma partitionBlocks_duration_nonneg {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) :
    ∀ b ∈ partitionBlocks k t, 0 ≤ b.2.2 := by
  rw [partitionBlocks, List.forall_mem_ofFn_iff]
  intro i
  positivity

lemma partitionBlocks_end_le_last {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) (ht : Monotone t) :
    ∀ b ∈ partitionBlocks k t, b.2.1 + b.2.2 ≤ (t (Fin.last n) : ℝ) := by
  rw [partitionBlocks, List.forall_mem_ofFn_iff]
  intro i
  have hstep : t i.castSucc ≤ t i.succ := ht (by
    change i.val ≤ i.val + 1
    omega)
  change (t i.castSucc : ℝ) + ((t i.succ - t i.castSucc : NNReal) : ℝ) ≤ _
  rw [NNReal.coe_sub hstep]
  have hlast : (t i.succ : ℝ) ≤ (t (Fin.last n) : ℝ) := by
    exact_mod_cast ht (Fin.le_last i.succ)
  linarith

lemma orderedArrivalBlocks_of_pairwise {bs : List (ℕ × ℝ × ℝ)}
    (h : bs.Pairwise (fun b c ↦ b.2.1 + b.2.2 ≤ c.2.1)) :
    OrderedArrivalBlocks bs := by
  induction bs with
  | nil => trivial
  | cons b bs ih =>
      rw [List.pairwise_cons] at h
      exact ⟨h.1, ih h.2⟩

lemma partitionBlocks_ordered {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) (ht : Monotone t) :
    OrderedArrivalBlocks (partitionBlocks k t) := by
  apply orderedArrivalBlocks_of_pairwise
  rw [partitionBlocks, List.pairwise_ofFn]
  intro i j hij
  have hstep : t i.castSucc ≤ t i.succ := ht (by
    change i.val ≤ i.val + 1
    omega)
  change (t i.castSucc : ℝ) + ((t i.succ - t i.castSucc : NNReal) : ℝ) ≤
    (t j.castSucc : ℝ)
  rw [NNReal.coe_sub hstep]
  have hij' : (t i.succ : ℝ) ≤ (t j.castSucc : ℝ) := by
    exact_mod_cast ht (show i.succ ≤ j.castSucc by
      change i.val + 1 ≤ j.val
      omega)
  linarith

lemma sum_partition_durations {n : ℕ} (t : Fin (n + 1) → NNReal)
    (ht : Monotone t) (hzero : t 0 = 0) :
    ∑ i : Fin n, ((t i.succ - t i.castSucc : NNReal) : ℝ) = (t (Fin.last n) : ℝ) := by
  have hstep : ∀ i : Fin n, t i.castSucc ≤ t i.succ := fun i ↦ ht (by
    change i.val ≤ i.val + 1
    omega)
  simp_rw [NNReal.coe_sub (hstep _)]
  rw [Finset.sum_sub_distrib]
  have hsucc := Fin.sum_univ_succ (f := fun j : Fin (n + 1) ↦ (t j : ℝ))
  have hcast := Fin.sum_univ_castSucc (f := fun j : Fin (n + 1) ↦ (t j : ℝ))
  simp only [hzero, NNReal.coe_zero, zero_add] at hsucc
  linarith

lemma volume_partitionBlocks {n : ℕ} (k : Fin n → ℕ)
    (t : Fin (n + 1) → NNReal) :
    volume (listArrivalChamber (partitionBlocks k t)) =
      ∏ i, ENNReal.ofReal
        (((t i.succ - t i.castSucc : NNReal) : ℝ) ^ k i / (k i).factorial) := by
  rw [volume_listArrivalChamber _ (partitionBlocks_duration_nonneg k t)]
  rw [partitionBlocks, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The all-finite-partitions exponential-arrival calculation, already simplified to the product
of Poisson atom probabilities. -/
theorem pi_expMeasure_partitionGapEvent {n : ℕ} (rate : NNReal) (hr : 0 < rate)
    (k : Fin n → ℕ) (t : Fin (n + 1) → NNReal) (ht : Monotone t)
    (hzero : t 0 = 0) :
    (Measure.pi fun _ : Fin (blockTotal (partitionBlocks k t) + 1) ↦
      expMeasure rate) (exponentialArrivalGapEvent (partitionBlocks k t)
        (t (Fin.last n) : ℝ)) =
      ∏ i, poissonMeasure (rate * (t i.succ - t i.castSucc)) {k i} := by
  rw [pi_expMeasure_arrivalGapEvent rate hr (by positivity)
    (partitionBlocks_start_nonneg k t)
    (partitionBlocks_end_le_last k t ht)
    (partitionBlocks_ordered k t ht)]
  rw [volume_partitionBlocks, blockTotal_partitionBlocks]
  have hdsum := sum_partition_durations t ht hzero
  rw [← hdsum]
  simp_rw [poissonMeasure_singleton]
  let d : Fin n → ℝ := fun i ↦ ((t i.succ - t i.castSucc : NNReal) : ℝ)
  have hfac :
      (rate : ℝ) ^ (∑ i, k i) * Real.exp (-((rate : ℝ) * ∑ i, d i)) *
          (∏ i, d i ^ k i / (k i).factorial) =
        ∏ i, Real.exp (-((rate : ℝ) * d i)) *
          ((rate : ℝ) * d i) ^ k i / (k i).factorial := by
    rw [show -((rate : ℝ) * ∑ i, d i) =
      ∑ i, -((rate : ℝ) * d i) by simp [Finset.mul_sum]]
    rw [Real.exp_sum]
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ k (rate : ℝ)]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow]
    ring
  change ENNReal.ofReal
      ((rate : ℝ) ^ (∑ i, k i) * Real.exp (-((rate : ℝ) * ∑ i, d i))) *
      (∏ i, ENNReal.ofReal (d i ^ k i / (k i).factorial)) = _
  calc
    _ = ENNReal.ofReal
        (((rate : ℝ) ^ (∑ i, k i) * Real.exp (-((rate : ℝ) * ∑ i, d i))) *
          (∏ i, d i ^ k i / (k i).factorial)) := by
          rw [← ENNReal.ofReal_prod_of_nonneg]
          · rw [← ENNReal.ofReal_mul (by positivity)]
          · intro i _
            positivity
    _ = ENNReal.ofReal (∏ i, Real.exp (-((rate : ℝ) * d i)) *
          ((rate : ℝ) * d i) ^ k i / (k i).factorial) := by rw [hfac]
    _ = ∏ i, ENNReal.ofReal (Real.exp (-((rate : ℝ) * d i)) *
          ((rate : ℝ) * d i) ^ k i / (k i).factorial) := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          intro i _
          positivity
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      norm_num [d]

private lemma exp_mul_pow_block_factorization {n : ℕ} (r : ℝ) (k : Fin n → ℕ)
    (d : Fin n → ℝ) :
    Real.exp (-(r * ∑ j, d j)) * r ^ (∑ j, k j) *
        (∏ j, d j ^ k j / (k j).factorial) =
      ∏ j, Real.exp (-(r * d j)) * (r * d j) ^ k j / (k j).factorial := by
  rw [show -(r * ∑ j, d j) = ∑ j, -(r * d j) by simp [Finset.mul_sum]]
  rw [Real.exp_sum]
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ k r]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [mul_pow]
  ring

/-- The exponential density mass of an arbitrary finite arrival chamber is the product of the
Poisson atom probabilities for its block counts.  This is the all-finite-partitions calculation,
not the two-increment special case displayed in the textbook proof. -/
theorem exponentialArrivalChamberMass {n : ℕ} (rate : NNReal) (k : Fin n → ℕ)
    (d : Fin n → NNReal) :
    (∫⁻ _ in MeasureTheory.orderedBlockChamber k (fun j ↦ (d j : ℝ)),
        ENNReal.ofReal
          (Real.exp (-((rate : ℝ) * ∑ j, (d j : ℝ))) *
            (rate : ℝ) ^ (∑ j, k j))) =
      ∏ j, poissonMeasure (rate * d j) {k j} := by
  rw [setLIntegral_const]
  rw [MeasureTheory.volume_orderedBlockChamber]
  · simp_rw [poissonMeasure_singleton]
    calc
      ENNReal.ofReal
          (Real.exp (-((rate : ℝ) * ∑ j, (d j : ℝ))) *
            (rate : ℝ) ^ (∑ j, k j)) *
          ∏ j, ENNReal.ofReal ((d j : ℝ) ^ k j / (k j).factorial) =
          ENNReal.ofReal
              (Real.exp (-((rate : ℝ) * ∑ j, (d j : ℝ))) *
                (rate : ℝ) ^ (∑ j, k j)) *
            ENNReal.ofReal (∏ j, (d j : ℝ) ^ k j / (k j).factorial) := by
              congr 1
              exact (ENNReal.ofReal_prod_of_nonneg fun j _ ↦ by positivity).symm
      _ = ENNReal.ofReal
            ((Real.exp (-((rate : ℝ) * ∑ j, (d j : ℝ))) *
                (rate : ℝ) ^ (∑ j, k j)) *
              ∏ j, (d j : ℝ) ^ k j / (k j).factorial) := by
            exact (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal
          (∏ j, Real.exp (-((rate : ℝ) * (d j : ℝ))) *
            ((rate : ℝ) * (d j : ℝ)) ^ k j / (k j).factorial) := by
          congr 1
          exact exp_mul_pow_block_factorization (rate : ℝ) k (fun j ↦ (d j : ℝ))
      _ = ∏ j, ENNReal.ofReal
          (Real.exp (-((rate : ℝ) * (d j : ℝ))) *
            ((rate : ℝ) * (d j : ℝ)) ^ k j / (k j).factorial) := by
          apply ENNReal.ofReal_prod_of_nonneg
          intro j _
          positivity
      _ = ∏ j, ENNReal.ofReal
          (Real.exp (-(rate * d j : NNReal)) *
            (rate * d j : NNReal) ^ k j / (k j).factorial) := by
          apply Finset.prod_congr rfl
          intro j _
          norm_num
  · intro j
    positivity

end

end ProbabilityTheory.PoissonProcess
