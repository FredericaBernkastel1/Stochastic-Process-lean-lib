/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.StrongMarkov
public import StochLean.Probability.Brownian.PathFunctionals
public import Mathlib.Probability.IdentDistribIndep

/-!
# Brownian reflection principle

This module proves the real Brownian reflection principle entirely inside StochLean.  It first
establishes reflection invariance at countable-valued stopping times, constructs capped dyadic
first-passage times, proves that their stopped values converge to the barrier, and passes the
resulting laws to the continuous first-passage reflection by dominated convergence of
characteristic functions.  Gaussian atomlessness is used explicitly at the strict/non-strict
boundary.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

theorem identDistrib_increment_neg [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    (s T : ℝ≥0) :
    IdentDistrib (fun ω ↦ B T ω - B s ω) (fun ω ↦ -(B T ω - B s ω)) P P := by
  have hR := hB.hasLaw_sub T s
  have hnegMap : HasLaw (fun x : ℝ ↦ -x)
      (gaussianReal 0 (nndist (T : ℝ) (s : ℝ)))
      (gaussianReal 0 (nndist (T : ℝ) (s : ℝ))) := by
    refine ⟨measurable_neg.aemeasurable, ?_⟩
    simpa using (gaussianReal_map_neg (μ := 0)
      (v := nndist (T : ℝ) (s : ℝ)))
  have hneg := hnegMap.comp hR
  exact hR.identDistrib (by simpa [Function.comp_def] using hneg)

theorem reflection_slice [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P)
    (hBm : ∀ u, Measurable (B u)) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (hτcount : (Set.range τ).Countable) (s : ℝ≥0) (hsT : s ≤ T) :
    IdentDistrib
      (fun ω ↦ (B T ω, {ω | τ ω = s}.indicator (fun _ ↦ (1 : ℝ)) ω))
      (fun ω ↦ (2 * B s ω - B T ω,
        {ω | τ ω = s}.indicator (fun _ ↦ (1 : ℝ)) ω)) P P := by
  let ℱ := Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)
  let A : Set Ω := {ω | τ ω = s}
  let M : Ω → ℝ := A.indicator (fun _ ↦ (1 : ℝ))
  let R : Ω → ℝ := fun ω ↦ B T ω - B s ω
  let Y : Ω → ℝ × ℝ := fun ω ↦ (B s ω, M ω)
  have hτrange : (Set.range (fun ω ↦ (τ ω : WithTop ℝ≥0))).Countable := by
    refine (hτcount.image fun u : ℝ≥0 ↦ (u : WithTop ℝ≥0)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩
  have hA : MeasurableSet[ℱ s] A := by
    simpa only [ℱ, A, WithTop.coe_eq_coe] using
      hτ.measurableSet_eq_of_countable_range hτrange s
  have hBs : @Measurable Ω ℝ (ℱ s) _ (B s) :=
    (Filtration.stronglyAdapted_natural (fun u ↦ (hBm u).stronglyMeasurable) s).measurable
  have hM : @Measurable Ω ℝ (ℱ s) _ M := by
    exact measurable_const.indicator hA
  have hY : @Measurable Ω (ℝ × ℝ) (ℱ s) _ Y := hBs.prodMk hM
  let e : (Unit → ℝ) → ℝ := fun x ↦ x ()
  have he : Measurable e := measurable_pi_apply ()
  have hi0 := hB.indepFun_brownianFutureIncrements_past s
    (fun _ : Unit ↦ T - s)
  have hiR : IndepFun R (fun ω (u : Set.Iic s) ↦ B u ω) P := by
    have hi1 := hi0.comp he measurable_id
    convert hi1 using 1
    · funext ω
      simp only [Function.comp_apply, e, brownianFutureIncrements]
      rw [add_tsub_cancel_of_le hsT]
    · rfl
  have hiSigma : Indep (MeasurableSpace.comap R inferInstance) (ℱ s) P := by
    change Indep (MeasurableSpace.comap R inferInstance)
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable) s) P
    rw [Filtration.natural_eq_comap]
    exact (IndepFun_iff_Indep _ _ P).mp hiR
  have hiRY : IndepFun R Y P := by
    apply (IndepFun_iff_Indep _ _ P).2
    exact indep_of_indep_of_le_right hiSigma hY.comap_le
  have hYbase : Measurable Y := hY.mono (ℱ.le s) le_rfl
  have hRid : IdentDistrib R (fun ω ↦ -R ω) P P := by
    exact identDistrib_increment_neg hB s T
  have hYid : IdentDistrib Y Y P P := IdentDistrib.refl hYbase.aemeasurable
  have hiNegRY : IndepFun (fun ω ↦ -R ω) Y P :=
    hiRY.comp measurable_neg measurable_id
  have hpair := hRid.prodMk hYid hiRY hiNegRY
  let g : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun z ↦ (z.2.1 + z.1, z.2.2)
  have hg : Measurable g :=
    (measurable_snd.fst.add measurable_fst).prodMk measurable_snd.snd
  have hcomp := hpair.comp hg
  convert hcomp using 1 <;> funext ω <;>
    simp only [Function.comp_def, g, R, Y, M, A] <;> ring

theorem measurable_eval_of_countable {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (τ : Ω → ℝ≥0)
    (hτcount : (Set.range τ).Countable)
    (hτslice : ∀ s, MeasurableSet {ω | τ ω = s}) :
    Measurable (fun ω ↦ X (τ ω) ω) := by
  classical
  let R := Set.range τ
  let slices : R → Set Ω := fun r ↦ {ω | τ ω = r.1}
  let part : IndexedPartition slices :=
    { eq_of_mem := fun {_ r q} hr hq ↦ Subtype.ext (hr.symm.trans hq)
      some := fun r ↦ Classical.choose r.property
      some_mem := fun r ↦ Classical.choose_spec r.property
      index := fun ω ↦ ⟨τ ω, ⟨ω, rfl⟩⟩
      mem_index := fun _ ↦ rfl }
  letI : Countable R := hτcount.to_subtype
  have hpw : Measurable (part.piecewise fun r ↦ X r.1) :=
    part.measurable_piecewise (fun r ↦ hτslice r.1) (fun r ↦ hX r.1)
  have heq : part.piecewise (fun r ↦ X r.1) = fun ω ↦ X (τ ω) ω := by
    funext ω
    simp only [IndexedPartition.piecewise_apply, part]
  exact heq ▸ hpw

def reflectedEndpoint (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  2 * X (τ ω) ω - X T ω

theorem identDistrib_reflectedEndpoint_countable [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (hτcount : (Set.range τ).Countable) (hτT : ∀ ω, τ ω ≤ T) :
    IdentDistrib (B T) (reflectedEndpoint B T τ) P P := by
  classical
  let ℱ := Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)
  let R := Set.range τ
  letI : Countable R := hτcount.to_subtype
  have hτrange : (Set.range (fun ω ↦ (τ ω : WithTop ℝ≥0))).Countable := by
    refine (hτcount.image fun u : ℝ≥0 ↦ (u : WithTop ℝ≥0)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩
  have hsliceFilt (s : ℝ≥0) : MeasurableSet[ℱ s] {ω | τ ω = s} := by
    simpa only [ℱ, WithTop.coe_eq_coe] using
      hτ.measurableSet_eq_of_countable_range hτrange s
  have hslice (s : ℝ≥0) : MeasurableSet {ω | τ ω = s} :=
    ℱ.le s _ (hsliceFilt s)
  have hBτ : Measurable (fun ω ↦ B (τ ω) ω) :=
    measurable_eval_of_countable hBm τ hτcount hslice
  have href : Measurable (reflectedEndpoint B T τ) := by
    exact (hBτ.const_mul 2).sub (hBm T)
  refine ⟨(hBm T).aemeasurable, href.aemeasurable, ?_⟩
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply_of_aemeasurable (hBm T).aemeasurable hC,
    Measure.map_apply_of_aemeasurable href.aemeasurable hC]
  let EL : R → Set Ω := fun r ↦ {ω | τ ω = r.1} ∩ (B T) ⁻¹' C
  let ER : R → Set Ω := fun r ↦ {ω | τ ω = r.1} ∩
    (fun ω ↦ 2 * B r.1 ω - B T ω) ⁻¹' C
  have hELmeas (r : R) : MeasurableSet (EL r) :=
    (hslice r.1).inter ((hBm T) hC)
  have hERmeas (r : R) : MeasurableSet (ER r) :=
    (hslice r.1).inter (((hBm r.1).const_mul 2).sub (hBm T) hC)
  have hdisjL : Pairwise (Function.onFun Disjoint EL) := by
    intro r q hrq
    change Disjoint (EL r) (EL q)
    rw [Set.disjoint_left]
    intro ω hωr hωq
    exact hrq (Subtype.ext (hωr.1.symm.trans hωq.1))
  have hdisjR : Pairwise (Function.onFun Disjoint ER) := by
    intro r q hrq
    change Disjoint (ER r) (ER q)
    rw [Set.disjoint_left]
    intro ω hωr hωq
    exact hrq (Subtype.ext (hωr.1.symm.trans hωq.1))
  have hL : (B T) ⁻¹' C = ⋃ r : R, EL r := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, EL, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    exact ⟨fun h ↦ ⟨⟨τ ω, ⟨ω, rfl⟩⟩, rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩
  have hR : (reflectedEndpoint B T τ) ⁻¹' C = ⋃ r : R, ER r := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, ER, Set.mem_inter_iff,
      Set.mem_setOf_eq, reflectedEndpoint]
    constructor
    · intro h
      exact ⟨⟨τ ω, ⟨ω, rfl⟩⟩, rfl, h⟩
    · rintro ⟨r, hr, h⟩
      simpa only [hr] using h
  rw [hL, hR, measure_iUnion hdisjL hELmeas, measure_iUnion hdisjR hERmeas]
  congr 1
  funext r
  have hp := reflection_slice hB hBm T τ hτ hτcount r.1
    (by obtain ⟨ω, hω⟩ := r.property; rw [← hω]; exact hτT ω)
  have hm := hp.measure_mem_eq (hC.prod (measurableSet_singleton (1 : ℝ)))
  have hpreL :
      (fun ω ↦ (B T ω, {ω | τ ω = r.1}.indicator (fun _ ↦ (1 : ℝ)) ω)) ⁻¹'
          (C ×ˢ ({1} : Set ℝ)) = EL r := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, EL, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    by_cases h : τ ω = r.1 <;> simp [h, and_comm]
  have hpreR :
      (fun ω ↦ (2 * B r.1 ω - B T ω,
        {ω | τ ω = r.1}.indicator (fun _ ↦ (1 : ℝ)) ω)) ⁻¹'
          (C ×ˢ ({1} : Set ℝ)) = ER r := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, ER, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    by_cases h : τ ω = r.1 <;> simp [h, and_comm]
  rw [← hpreL, ← hpreR]
  exact hm

/-- The regular dyadic grid, capped at the deterministic horizon. -/
noncomputable def dyadicTimeUpTo (T : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  min T ((k : ℝ≥0) / ((2 ^ n : ℕ) : ℝ≥0))

theorem dyadicTimeUpTo_mono (T : ℝ≥0) (n : ℕ) :
    Monotone (dyadicTimeUpTo T n) := by
  intro k l hkl
  apply min_le_min_left
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hkl) (by positivity)

theorem dyadicTimeUpTo_le (T : ℝ≥0) (n k : ℕ) :
    dyadicTimeUpTo T n k ≤ T :=
  min_le_left _ _

theorem dist_dyadicTimeUpTo_pred_le (T : ℝ≥0) (n k : ℕ) (hk : 0 < k) :
    dist (dyadicTimeUpTo T n k) (dyadicTimeUpTo T n (k - 1)) ≤
      (((2 ^ n : ℕ) : ℝ≥0))⁻¹ := by
  rw [NNReal.dist_eq]
  simp only [dyadicTimeUpTo, NNReal.coe_min, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_inv]
  calc
    |min (T : ℝ) (k / (2 ^ n : ℕ)) -
        min (T : ℝ) (((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ))| ≤
        max |(T : ℝ) - T|
          |(k : ℝ) / (2 ^ n : ℕ) - ((k - 1 : ℕ) : ℝ) / (2 ^ n : ℕ)| :=
      abs_min_sub_min_le_max _ _ _ _
    _ = (((2 ^ n : ℕ) : ℝ≥0) : ℝ)⁻¹ := by
      have hpow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
      have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) hk)
      simp only [sub_self, abs_zero, NNReal.coe_natCast]
      rw [hkcast]
      have hinv : 0 < ((2 ^ n : ℕ) : ℝ)⁻¹ := inv_pos.mpr hpow
      have hfrac : (k : ℝ) / (2 ^ n : ℕ) - ((k : ℝ) - 1) / (2 ^ n : ℕ) =
          ((2 ^ n : ℕ) : ℝ)⁻¹ := by
        field_simp
        ring
      rw [hfrac, abs_of_pos hinv, max_eq_right hinv.le]

noncomputable def dyadicTerminalIndex (T : ℝ≥0) (n : ℕ) : ℕ :=
  Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * T)

@[simp]
theorem dyadicTimeUpTo_terminal (T : ℝ≥0) (n : ℕ) :
    dyadicTimeUpTo T n (dyadicTerminalIndex T n) = T := by
  rw [dyadicTimeUpTo, min_eq_left]
  apply (le_div_iff₀ (by positivity : (0 : ℝ≥0) < ((2 ^ n : ℕ) : ℝ≥0))).2
  simpa only [dyadicTerminalIndex, mul_comm] using
    (Nat.le_ceil (((2 ^ n : ℕ) : ℝ≥0) * T))

noncomputable def dyadicCandidateIndex (n : ℕ) (s : ℝ≥0) : ℕ :=
  Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * s)

theorem dyadicTimeUpTo_candidate (T s : ℝ≥0) (n : ℕ) :
    dyadicTimeUpTo T n (dyadicCandidateIndex n s) =
      min T (dyadicRightGrid n s) := by
  rw [dyadicTimeUpTo, dyadicRightGrid_eq]
  rfl

theorem tendsto_dyadicTimeUpTo_candidate {T s : ℝ≥0} (hsT : s ≤ T) :
    Tendsto (fun n ↦ dyadicTimeUpTo T n (dyadicCandidateIndex n s))
      atTop (nhds s) := by
  have hcont : Continuous (fun x : ℝ≥0 ↦ min T x) := continuous_const.min continuous_id
  have h := hcont.continuousAt.tendsto.comp
    (tendsto_dyadicRightGrid s)
  rw [show (fun n ↦ dyadicTimeUpTo T n (dyadicCandidateIndex n s)) =
      fun n ↦ min T (dyadicRightGrid n s) by
    funext n
    exact dyadicTimeUpTo_candidate T s n]
  simpa only [Function.comp_def, min_eq_right hsT] using h

theorem exists_exceedance_before_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {a : ℝ} (h0 : f 0 < a) {T : ℝ≥0}
    (hcross : ∃ t : ℝ≥0, t ≤ T ∧ a < f t) :
    ∃ s : ℝ≥0, s < T ∧ a < f s := by
  obtain ⟨t, htT, hat⟩ := hcross
  by_cases hlt : t < T
  · exact ⟨t, hlt, hat⟩
  · have hteq : t = T := le_antisymm htT (not_lt.mp hlt)
    subst t
    have hTpos : 0 < T := by
      by_contra h
      have hT0 : T = 0 := le_antisymm (not_lt.mp h) T.property
      rw [hT0] at hat
      exact (not_lt_of_ge h0.le) hat
    let U : Set ℝ≥0 := f ⁻¹' Ioi a
    have hUopen : IsOpen U := isOpen_Ioi.preimage hf
    have hTU : T ∈ U := hat
    have hclosure : T ∈ closure (Iio T) := by
      have hnon : (Iio T : Set ℝ≥0).Nonempty := ⟨0, hTpos⟩
      rw [closure_Iio' hnon]
      exact Set.mem_Iic.mpr le_rfl
    obtain ⟨s, hsU, hsT⟩ := (mem_closure_iff.mp hclosure) U hUopen hTU
    exact ⟨s, hsT, hsU⟩

noncomputable def firstIndexBefore (hit : ℕ → Ω → Prop) (N : ℕ) (ω : Ω) : ℕ := by
  classical
  exact if h : ∃ k, k < N ∧ hit k ω then Nat.find h else N

theorem firstIndexBefore_eq_iff (hit : ℕ → Ω → Prop) (N k : ℕ) (ω : Ω)
    (hk : k < N) :
    firstIndexBefore hit N ω = k ↔ hit k ω ∧ ∀ j < k, ¬ hit j ω := by
  classical
  unfold firstIndexBefore
  split_ifs with h
  · constructor
    · intro heq
      have hspec := Nat.find_spec h
      rw [heq] at hspec
      exact ⟨hspec.2, fun j hj hjhit ↦ by
        have hmin := Nat.find_min' h ⟨Nat.lt_trans hj hk, hjhit⟩
        omega⟩
    · rintro ⟨hkhit, hprev⟩
      apply le_antisymm
      · exact Nat.find_min' h ⟨hk, hkhit⟩
      · by_contra hnle
        have hlt : Nat.find h < k := Nat.lt_of_not_ge hnle
        exact hprev _ hlt (Nat.find_spec h).2
  · constructor
    · intro heq
      omega
    · rintro ⟨hkhit, _⟩
      exact False.elim (h ⟨k, hk, hkhit⟩)

theorem firstIndexBefore_terminal_iff (hit : ℕ → Ω → Prop) (N : ℕ) (ω : Ω) :
    firstIndexBefore hit N ω = N ↔ ∀ k < N, ¬ hit k ω := by
  classical
  unfold firstIndexBefore
  split_ifs with h
  · have hspec := Nat.find_spec h
    constructor
    · intro heq
      omega
    · intro hnone
      exact False.elim (hnone _ hspec.1 hspec.2)
  · constructor
    · intro _
      push Not at h
      exact h
    · intro _
      rfl

theorem firstIndexBefore_le (hit : ℕ → Ω → Prop) (N : ℕ) (ω : Ω) :
    firstIndexBefore hit N ω ≤ N := by
  classical
  unfold firstIndexBefore
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem firstIndexBefore_lt_of_exists (hit : ℕ → Ω → Prop) (N : ℕ) (ω : Ω)
    (h : ∃ k, k < N ∧ hit k ω) :
    firstIndexBefore hit N ω < N := by
  classical
  unfold firstIndexBefore
  rw [dif_pos h]
  exact (Nat.find_spec h).1

noncomputable def dyadicFirstPassageIndex (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (n : ℕ) : Ω → ℕ :=
  firstIndexBefore
    (fun k ω ↦ a < X (dyadicTimeUpTo T n k) ω)
    (dyadicTerminalIndex T n)

noncomputable def dyadicFirstPassageTime (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (n : ℕ) : Ω → ℝ≥0 :=
  fun ω ↦ dyadicTimeUpTo T n (dyadicFirstPassageIndex X a T n ω)

theorem dyadicFirstPassageTime_le (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    dyadicFirstPassageTime X a T n ω ≤ T :=
  dyadicTimeUpTo_le T n _

theorem countable_range_dyadicFirstPassageTime (X : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    (Set.range (dyadicFirstPassageTime X a T n)).Countable := by
  refine (Set.countable_range (dyadicTimeUpTo T n)).mono ?_
  rintro y ⟨ω, rfl⟩
  exact ⟨dyadicFirstPassageIndex X a T n ω, rfl⟩

theorem stoppingTime_dyadicFirstPassageTime (hBm : ∀ u, Measurable (B u))
    (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (dyadicFirstPassageTime B a T n ω : WithTop ℝ≥0)) := by
  let ℱ := Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)
  let κ := dyadicFirstPassageIndex B a T n
  let N := dyadicTerminalIndex T n
  let hit : ℕ → Ω → Prop := fun k ω ↦ a < B (dyadicTimeUpTo T n k) ω
  have hcoord (k : ℕ) : @Measurable Ω ℝ (ℱ (dyadicTimeUpTo T n k)) _
      (B (dyadicTimeUpTo T n k)) :=
    (Filtration.stronglyAdapted_natural (fun u ↦ (hBm u).stronglyMeasurable)
      (dyadicTimeUpTo T n k)).measurable
  have hhit (k : ℕ) : MeasurableSet[ℱ (dyadicTimeUpTo T n k)] {ω | hit k ω} :=
    measurableSet_lt measurable_const (hcoord k)
  have hslice (k : ℕ) :
      MeasurableSet[ℱ (dyadicTimeUpTo T n k)] {ω | κ ω = k} := by
    rcases lt_trichotomy k N with hkN | rfl | hNk
    · have heq : {ω | κ ω = k} =
          {ω | hit k ω} ∩ ⋂ j : {j : ℕ // j < k}, {ω | ¬ hit j.1 ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [show κ ω = firstIndexBefore hit N ω by rfl,
          firstIndexBefore_eq_iff hit N k ω hkN]
        constructor
        · rintro ⟨hkHit, hprev⟩
          exact ⟨hkHit, fun j ↦ hprev j.1 j.2⟩
        · rintro ⟨hkHit, hprev⟩
          exact ⟨hkHit, fun j hj ↦ hprev ⟨j, hj⟩⟩
      rw [heq]
      apply (hhit k).inter
      exact MeasurableSet.iInter fun j ↦
        (ℱ.mono (dyadicTimeUpTo_mono T n j.2.le) _ (hhit j.1)).compl
    · have heq : {ω | κ ω = N} = ⋂ j : {j : ℕ // j < N}, {ω | ¬ hit j.1 ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        rw [show κ ω = firstIndexBefore hit N ω by rfl,
          firstIndexBefore_terminal_iff hit N ω]
        exact ⟨fun h j ↦ h j.1 j.2, fun h j hj ↦ h ⟨j, hj⟩⟩
      rw [heq]
      exact MeasurableSet.iInter fun j ↦
        (ℱ.mono (dyadicTimeUpTo_mono T n j.2.le) _ (hhit j.1)).compl
    · have heq : {ω | κ ω = k} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun heq ↦ by
          have hle : κ ω ≤ N := firstIndexBefore_le hit N ω
          rw [heq] at hle
          omega
      rw [heq]
      exact @MeasurableSet.empty Ω (ℱ (dyadicTimeUpTo T n k))
  intro u
  have hevent :
      {ω | (dyadicFirstPassageTime B a T n ω : WithTop ℝ≥0) ≤ u} =
        ⋃ k : {k : ℕ // dyadicTimeUpTo T n k ≤ u}, {ω | κ ω = k.1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h' : dyadicTimeUpTo T n (κ ω) ≤ u := WithTop.coe_le_coe.mp h
      exact ⟨⟨κ ω, h'⟩, rfl⟩
    · rintro ⟨k, hk⟩
      apply WithTop.coe_le_coe.mpr
      change dyadicTimeUpTo T n (κ ω) ≤ u
      rw [hk]
      exact k.2
  rw [hevent]
  exact MeasurableSet.iUnion fun k ↦
    ℱ.mono k.2 _ (hslice k.1)

theorem eventually_dyadicFirstPassage_bracket {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {a : ℝ} (h0 : f 0 < a) {T : ℝ≥0}
    (hcross : ∃ t : ℝ≥0, t ≤ T ∧ a < f t) :
    ∀ᶠ n in atTop,
      let κ := dyadicFirstPassageIndex (fun t (_ : Unit) ↦ f t) a T n ()
      let N := dyadicTerminalIndex T n
      κ < N ∧ 0 < κ ∧
        a < f (dyadicTimeUpTo T n κ) ∧
        f (dyadicTimeUpTo T n (κ - 1)) ≤ a := by
  obtain ⟨s, hsT, has⟩ := exists_exceedance_before_of_continuous hf h0 hcross
  have htend := tendsto_dyadicTimeUpTo_candidate (T := T) hsT.le
  have htime : ∀ᶠ n in atTop,
      dyadicTimeUpTo T n (dyadicCandidateIndex n s) < T :=
    htend.eventually_lt_const hsT
  have hvalue : ∀ᶠ n in atTop,
      a < f (dyadicTimeUpTo T n (dyadicCandidateIndex n s)) :=
    (hf.continuousAt.tendsto.comp htend).eventually_const_lt has
  filter_upwards [htime, hvalue] with n hnT hna
  let hit : ℕ → Unit → Prop :=
    fun k _ ↦ a < f (dyadicTimeUpTo T n k)
  let N := dyadicTerminalIndex T n
  let κ := firstIndexBefore hit N ()
  have hcandN : dyadicCandidateIndex n s < N := by
    by_contra hnot
    have hmono := dyadicTimeUpTo_mono T n (Nat.le_of_not_gt hnot)
    rw [show N = dyadicTerminalIndex T n by rfl,
      dyadicTimeUpTo_terminal] at hmono
    exact (not_le_of_gt hnT) hmono
  have hex : ∃ k, k < N ∧ hit k () :=
    ⟨dyadicCandidateIndex n s, hcandN, hna⟩
  have hκN : κ < N := firstIndexBefore_lt_of_exists hit N () hex
  have hspec : hit κ () ∧ ∀ j < κ, ¬ hit j () := by
    exact (firstIndexBefore_eq_iff hit N κ () hκN).mp rfl
  have hκpos : 0 < κ := by
    by_contra hnot
    have hκzero : κ = 0 := Nat.eq_zero_of_not_pos hnot
    have hhit0 := hspec.1
    rw [hκzero] at hhit0
    simp only [hit, dyadicTimeUpTo, Nat.cast_zero, zero_div, min_zero] at hhit0
    exact (not_lt_of_ge h0.le) hhit0
  have hpred : f (dyadicTimeUpTo T n (κ - 1)) ≤ a := by
    exact not_lt.mp (hspec.2 (κ - 1) (Nat.sub_lt hκpos (by omega)))
  exact ⟨hκN, hκpos, hspec.1, hpred⟩

theorem tendsto_dyadicFirstPassage_value {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {a : ℝ} (h0 : f 0 < a) {T : ℝ≥0}
    (hcross : ∃ t : ℝ≥0, t ≤ T ∧ a < f t) :
    Tendsto
      (fun n ↦ f (dyadicFirstPassageTime (fun t (_ : Unit) ↦ f t) a T n ()))
      atTop (nhds a) := by
  have hbracket := eventually_dyadicFirstPassage_bracket hf h0 hcross
  have hmeshNN : Tendsto (fun n : ℕ ↦ (((2 ^ n : ℕ) : ℝ≥0))⁻¹) atTop
      (nhds (0 : ℝ≥0)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow] using
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := ((2 : ℝ≥0)⁻¹)) (by norm_num))
  have hmesh : Tendsto (fun n : ℕ ↦ ((((2 ^ n : ℕ) : ℝ≥0))⁻¹).1)
      atTop (nhds (0 : ℝ)) := NNReal.tendsto_coe.mpr hmeshNN
  have huc : UniformContinuousOn f (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := huc ε hε
  have hmeshδ : ∀ᶠ n in atTop, ((((2 ^ n : ℕ) : ℝ≥0))⁻¹).1 < δ :=
    hmesh.eventually_lt_const hδ
  filter_upwards [hbracket, hmeshδ] with n hn hnmesh
  dsimp only at hn ⊢
  let κ := dyadicFirstPassageIndex (fun t (_ : Unit) ↦ f t) a T n ()
  let tκ := dyadicTimeUpTo T n κ
  let tprev := dyadicTimeUpTo T n (κ - 1)
  have htκ : tκ ∈ Icc (0 : ℝ≥0) T :=
    ⟨bot_le, dyadicTimeUpTo_le T n κ⟩
  have htprev : tprev ∈ Icc (0 : ℝ≥0) T :=
    ⟨bot_le, dyadicTimeUpTo_le T n (κ - 1)⟩
  have htimeDist : dist tκ tprev < δ :=
    lt_of_le_of_lt (dist_dyadicTimeUpTo_pred_le T n κ hn.2.1) hnmesh
  have hvalueDist : dist (f tκ) (f tprev) < ε :=
    hmod tκ htκ tprev htprev htimeDist
  have htoBarrier : dist (f tκ) a ≤ dist (f tκ) (f tprev) := by
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hn.2.2.1.le),
      abs_of_nonneg (sub_nonneg.mpr (hn.2.2.2.trans hn.2.2.1.le))]
    linarith
  exact lt_of_le_of_lt htoBarrier hvalueDist

/-- Reflection at the first strict crossing of `a` before `T`, expressed only through
the terminal endpoint.  On paths with no crossing it is the original endpoint. -/
noncomputable def reflectedFirstPassageEndpoint (X : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (T : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω then 2 * a - X T ω else X T ω

theorem tendsto_dyadic_reflectedEndpoint (X : ℝ≥0 → Ω → ℝ)
    (hXcont : ∀ ω, Continuous fun t ↦ X t ω) {a : ℝ}
    (T : ℝ≥0) (ω : Ω) (h0 : X 0 ω < a) :
    Tendsto
      (fun n ↦ reflectedEndpoint X T (dyadicFirstPassageTime X a T n) ω)
      atTop (nhds (reflectedFirstPassageEndpoint X a T ω)) := by
  classical
  by_cases hcross : ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω
  · have hvalue := tendsto_dyadicFirstPassage_value (hXcont ω) h0 hcross
    have hvalue' : Tendsto
        (fun n ↦ X (dyadicFirstPassageTime X a T n ω) ω)
        atTop (nhds a) := by
      convert hvalue using 1 <;> rfl
    have hscaled := hvalue'.const_mul 2
    have hlimit := hscaled.sub (tendsto_const_nhds (x := X T ω))
    simpa only [reflectedEndpoint, reflectedFirstPassageEndpoint,
      if_pos hcross] using hlimit
  · have hterminal (n : ℕ) :
        dyadicFirstPassageTime X a T n ω = T := by
      have hnone : ∀ k < dyadicTerminalIndex T n,
          ¬ a < X (dyadicTimeUpTo T n k) ω := by
        intro k _ hk
        exact hcross ⟨dyadicTimeUpTo T n k,
          dyadicTimeUpTo_le T n k, hk⟩
      have hindex : dyadicFirstPassageIndex X a T n ω =
          dyadicTerminalIndex T n := by
        exact (firstIndexBefore_terminal_iff
          (fun k ω ↦ a < X (dyadicTimeUpTo T n k) ω)
          (dyadicTerminalIndex T n) ω).2 hnone
      rw [dyadicFirstPassageTime, hindex, dyadicTimeUpTo_terminal]
    have heq : (fun n ↦ reflectedEndpoint X T
        (dyadicFirstPassageTime X a T n) ω) = fun _ : ℕ ↦ X T ω := by
      funext n
      simp only [reflectedEndpoint, hterminal]
      ring
    rw [heq, reflectedFirstPassageEndpoint, if_neg hcross]
    exact tendsto_const_nhds

theorem identDistrib_reflectedFirstPassageEndpoint_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    IdentDistrib (hB.mk B T)
      (reflectedFirstPassageEndpoint (hB.mk B) a T) P P := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let R : ℕ → Ω → ℝ := fun n ↦
    reflectedEndpoint X T (dyadicFirstPassageTime X a T n)
  have hXpre : IsPreBrownianReal X P := hB.isBrownianReal_mk.toIsPreBrownianReal
  have hXm : ∀ t, Measurable (X t) := hB.measurable_mk
  have hID (n : ℕ) : IdentDistrib (X T) (R n) P P := by
    exact identDistrib_reflectedEndpoint_countable hXpre hXm T
      (dyadicFirstPassageTime X a T n)
      (stoppingTime_dyadicFirstPassageTime hXm a T n)
      (countable_range_dyadicFirstPassageTime X a T n)
      (dyadicFirstPassageTime_le X a T n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ R n ω) atTop
      (nhds (reflectedFirstPassageEndpoint X a T ω)) := by
    filter_upwards [hXpre.eval_zero_ae_eq_zero] with ω hzero
    exact tendsto_dyadic_reflectedEndpoint X hB.continuous_mk T ω (by
      rw [hzero]
      exact ha)
  have hRaem (n : ℕ) : AEMeasurable (R n) P := (hID n).aemeasurable_snd
  have hrefAem : AEMeasurable (reflectedFirstPassageEndpoint X a T) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop hRaem hlim
  refine ⟨(hXm T).aemeasurable, hrefAem, ?_⟩
  apply Measure.ext_of_charFun
  funext u
  let φ : ℝ → ℂ := fun x ↦ (Real.probChar (x * u) : ℂ)
  have hφ : Measurable φ := by fun_prop
  have hφcont : Continuous φ := by fun_prop
  have hDCT : Tendsto (fun n ↦ ∫ ω, φ (R n ω) ∂P) atTop
      (nhds (∫ ω, φ (reflectedFirstPassageEndpoint X a T ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n
      exact hφ.aestronglyMeasurable.comp_aemeasurable (hRaem n)
    · exact integrable_const 1
    · intro n
      filter_upwards [] with ω
      simp only [φ, Circle.norm_coe, norm_one, le_refl]
    · filter_upwards [hlim] with ω hω
      exact hφcont.continuousAt.tendsto.comp hω
  have hInt (n : ℕ) : (∫ ω, φ (X T ω) ∂P) = ∫ ω, φ (R n ω) ∂P := by
    exact ((hID n).comp hφ).integral_eq
  have hDCT' : Tendsto (fun _ : ℕ ↦ ∫ ω, φ (X T ω) ∂P) atTop
      (nhds (∫ ω, φ (reflectedFirstPassageEndpoint X a T ω) ∂P)) := by
    convert hDCT using 1
    funext n
    exact hInt n
  have hIntegral : (∫ ω, φ (X T ω) ∂P) =
      ∫ ω, φ (reflectedFirstPassageEndpoint X a T ω) ∂P :=
    tendsto_nhds_unique tendsto_const_nhds hDCT'
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (hXm T).aemeasurable (by fun_prop),
    integral_map hrefAem (by fun_prop)]
  simpa only [φ, Real.probChar_apply, Complex.ofReal_mul, mul_comm, mul_left_comm]
    using hIntegral

theorem reflection_joint_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a b : ℝ} (ha : 0 < a) (hb : b < a)
    (T : ℝ≥0) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ a < hB.mk B t ω) ∧ hB.mk B T ω ≤ b} =
      P {ω | 2 * a - b ≤ hB.mk B T ω} := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let R : Ω → ℝ := reflectedFirstPassageEndpoint X a T
  have hID : IdentDistrib (X T) R P P :=
    identDistrib_reflectedFirstPassageEndpoint_mk hB ha T
  have hpre : R ⁻¹' Ici (2 * a - b) =
      {ω | (∃ t : ℝ≥0, t ≤ T ∧ a < X t ω) ∧ X T ω ≤ b} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq, R]
    by_cases hcross : ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω
    · rw [reflectedFirstPassageEndpoint, if_pos hcross]
      constructor <;> intro h
      · exact ⟨hcross, by linarith⟩
      · linarith [h.2]
    · rw [reflectedFirstPassageEndpoint, if_neg hcross]
      have hterminal : X T ω ≤ a := by
        exact not_lt.mp (fun h ↦ hcross ⟨T, le_rfl, h⟩)
      constructor
      · intro h
        exfalso
        linarith
      · exact fun h ↦ False.elim (hcross h.1)
  have hm := hID.measure_mem_eq (measurableSet_Ici : MeasurableSet (Ici (2 * a - b)))
  change P ((X T) ⁻¹' Ici (2 * a - b)) = P (R ⁻¹' Ici (2 * a - b)) at hm
  rw [hpre] at hm
  exact hm.symm

theorem measure_mk_terminal_eq_zero [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | hB.mk B T ω = a} = 0 := by
  have hLaw := hB.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_eval T
  have hm := hLaw.measure_eq (p := fun x : ℝ ↦ x = a) (measurableSet_singleton a)
  rw [hm]
  change gaussianReal 0 T ({a} : Set ℝ) = 0
  by_cases hT : T = 0
  · simp only [hT, gaussianReal_zero_var, Measure.dirac_apply_of_mem,
      MeasurableSet.singleton, Set.mem_singleton_iff]
    simp [ha.ne']
  · letI : NullSingletonClass (gaussianReal 0 T) :=
      nullSingletonClass_gaussianReal hT
    exact measure_singleton a

theorem reflection_strict_lower_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | (∃ t : ℝ≥0, t ≤ T ∧ a < hB.mk B t ω) ∧ hB.mk B T ω < a} =
      P {ω | a < hB.mk B T ω} := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let b : ℕ → ℝ := fun n ↦ a - 1 / (n + 1 : ℝ)
  let L : ℕ → Set Ω := fun n ↦
    {ω | (∃ t : ℝ≥0, t ≤ T ∧ a < X t ω) ∧ X T ω ≤ b n}
  let U : ℕ → Set Ω := fun n ↦ {ω | 2 * a - b n ≤ X T ω}
  have hb (n : ℕ) : b n < a := by
    dsimp only [b]
    have : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hLU (n : ℕ) : P (L n) = P (U n) := by
    exact reflection_joint_mk hB ha (hb n) T
  have hbmono : Monotone b := by
    intro n m hnm
    dsimp only [b]
    have hposn : 0 < (n + 1 : ℝ) := by positivity
    have hcast : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact sub_le_sub_left (one_div_le_one_div_of_le hposn hcast) a
  have hLmono : Monotone L := by
    intro n m hnm ω hω
    exact ⟨hω.1, hω.2.trans (hbmono hnm)⟩
  have hUmono : Monotone U := by
    intro n m hnm ω hω
    change 2 * a - b m ≤ X T ω
    exact (sub_le_sub_left (hbmono hnm) (2 * a)).trans hω
  have hiL : (⋃ n, L n) =
      {ω | (∃ t : ℝ≥0, t ≤ T ∧ a < X t ω) ∧ X T ω < a} := by
    ext ω
    simp only [Set.mem_iUnion, L, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hcross, hle⟩
      exact ⟨hcross, hle.trans_lt (hb n)⟩
    · rintro ⟨hcross, hlt⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      refine ⟨n, hcross, ?_⟩
      dsimp only [b]
      linarith
  have hiU : (⋃ n, U n) = {ω | a < X T ω} := by
    ext ω
    simp only [Set.mem_iUnion, U, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      dsimp only [b] at hn
      linarith
    · intro hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      refine ⟨n, ?_⟩
      dsimp only [b]
      linarith
  have htL := tendsto_measure_iUnion_atTop (μ := P) hLmono
  have htU := tendsto_measure_iUnion_atTop (μ := P) hUmono
  rw [hiL] at htL
  rw [hiU] at htU
  have hfun : P ∘ L = P ∘ U := by
    funext n
    exact hLU n
  rw [hfun] at htL
  exact tendsto_nhds_unique htL htU

theorem reflection_principle_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < hB.mk B t ω} =
      2 * P {ω | a < hB.mk B T ω} := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let C : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < X t ω}
  let Dlt : Set Ω := {ω | X T ω < a}
  let Deq : Set Ω := {ω | X T ω = a}
  let Dgt : Set Ω := {ω | a < X T ω}
  have hXm : ∀ t, Measurable (X t) := hB.measurable_mk
  have hCeq : C = {ω | ENNReal.ofReal a < denseRunningSupremum X T ω} := by
    ext ω
    exact (hB.lt_denseRunningSupremum_mk_iff ha.le ω).symm
  have hCmeas : MeasurableSet C := by
    rw [hCeq]
    exact measurableSet_denseRunningSupremum_gt hXm T a
  have hDltmeas : MeasurableSet Dlt :=
    measurableSet_lt (hXm T) measurable_const
  have hDeqmeas : MeasurableSet Deq :=
    measurableSet_eq_fun (hXm T) measurable_const
  have hDgtmeas : MeasurableSet Dgt :=
    measurableSet_lt measurable_const (hXm T)
  have hDgtC : Dgt ⊆ C := by
    intro ω hω
    exact ⟨T, le_rfl, hω⟩
  have hdecomp : C = (C ∩ Dlt) ∪ (C ∩ Deq) ∪ Dgt := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hC
      rcases lt_trichotomy (X T ω) a with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hC, hlt⟩)
      · exact Or.inl (Or.inr ⟨hC, heq⟩)
      · exact Or.inr hgt
    · rintro (⟨⟨hC, _⟩ | ⟨hC, _⟩⟩ | hgt)
      · exact hC
      · exact hC
      · exact hDgtC hgt
  have hdisjLE : Disjoint (C ∩ Dlt) (C ∩ Deq) := by
    rw [Set.disjoint_left]
    intro ω hlt heq
    exact (ne_of_lt hlt.2) heq.2
  have hdisjLEG : Disjoint ((C ∩ Dlt) ∪ (C ∩ Deq)) Dgt := by
    rw [Set.disjoint_left]
    intro ω hle hgt
    change a < X T ω at hgt
    rcases hle with hlt | heq
    · have hlt' : X T ω < a := hlt.2
      exact (not_lt_of_ge hgt.le) hlt'
    · have heq' : X T ω = a := heq.2
      exact (ne_of_lt hgt) heq'.symm
  have hEqZero : P (C ∩ Deq) = 0 := by
    apply measure_mono_null (inter_subset_right) ?_
    exact measure_mk_terminal_eq_zero hB ha T
  have hLower : P (C ∩ Dlt) = P Dgt := by
    exact reflection_strict_lower_mk hB ha T
  rw [show {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < hB.mk B t ω} = C by rfl,
    show {ω | a < hB.mk B T ω} = Dgt by rfl,
    hdecomp, measure_union hdisjLEG hDgtmeas,
    measure_union hdisjLE (hCmeas.inter hDeqmeas), hEqZero, add_zero, hLower,
    two_mul]

/-- Closed-barrier Brownian reflection principle for the canonical continuous representative. -/
theorem reflection_principle_ge_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ hB.mk B t ω} =
      2 * P {ω | a ≤ hB.mk B T ω} := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let b : ℕ → ℝ := fun n ↦
    a * (((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))
  let C : ℕ → Set Ω := fun n ↦ {ω | ∃ t : ℝ≥0, t ≤ T ∧ b n < X t ω}
  let D : ℕ → Set Ω := fun n ↦ {ω | b n < X T ω}
  let Cge : Set Ω := {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ X t ω}
  let Dge : Set Ω := {ω | a ≤ X T ω}
  have hbpos (n : ℕ) : 0 < b n := by
    dsimp only [b]
    positivity
  have hblt (n : ℕ) : b n < a := by
    dsimp only [b]
    have hrat : ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).2 (by linarith)
    simpa only [mul_one] using mul_lt_mul_of_pos_left hrat ha
  have hbmono : Monotone b := by
    intro n m hnm
    dsimp only [b]
    apply mul_le_mul_of_nonneg_left _ ha.le
    have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ hn0 hm0]
    have hcast : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    nlinarith
  have hbT : Tendsto b atTop (𝓝 a) := by
    have hratio : Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((Filter.tendsto_add_atTop_iff_nat
          (f := fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) 1).2
            (tendsto_natCast_div_add_atTop (1 : ℝ)))
    simpa only [b, mul_one] using hratio.const_mul a
  have hCmeas (n : ℕ) : MeasurableSet (C n) := by
    have hCeq : C n = {ω | ENNReal.ofReal (b n) < denseRunningSupremum X T ω} := by
      ext ω
      exact (hB.lt_denseRunningSupremum_mk_iff (hbpos n).le ω).symm
    rw [hCeq]
    exact measurableSet_denseRunningSupremum_gt hB.measurable_mk T (b n)
  have hDmeas (n : ℕ) : MeasurableSet (D n) :=
    measurableSet_lt measurable_const (hB.measurable_mk T)
  have hCanti : Antitone C := by
    intro n m hnm ω hω
    obtain ⟨t, htT, hbt⟩ := hω
    exact ⟨t, htT, (hbmono hnm).trans_lt hbt⟩
  have hDanti : Antitone D := by
    intro n m hnm ω hω
    exact (hbmono hnm).trans_lt hω
  have hCi : (⋂ n, C n) = Cge := by
    ext ω
    constructor
    · intro hω
      obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
        (nonempty_Icc.2 bot_le) (hB.continuous_mk ω).continuousOn
      refine ⟨t, ht.2, ?_⟩
      apply le_of_tendsto' hbT
      intro n
      obtain ⟨tn, htnT, hn⟩ := Set.mem_iInter.mp hω n
      exact hn.le.trans (hmax ⟨bot_le, htnT⟩)
    · rintro ⟨t, htT, hat⟩
      apply Set.mem_iInter.mpr
      intro n
      exact ⟨t, htT, (hblt n).trans_le hat⟩
  have hDi : (⋂ n, D n) = Dge := by
    ext ω
    constructor
    · intro hω
      apply le_of_tendsto' hbT
      intro n
      exact (Set.mem_iInter.mp hω n).le
    · intro hω
      apply Set.mem_iInter.mpr
      intro n
      exact (hblt n).trans_le hω
  have htC := tendsto_measure_iInter_atTop
    (μ := P) (fun n ↦ (hCmeas n).nullMeasurableSet) hCanti
      ⟨0, measure_ne_top P _⟩
  have htD := tendsto_measure_iInter_atTop
    (μ := P) (fun n ↦ (hDmeas n).nullMeasurableSet) hDanti
      ⟨0, measure_ne_top P _⟩
  rw [hCi] at htC
  rw [hDi] at htD
  have hstrict (n : ℕ) : P (C n) = 2 * P (D n) :=
    reflection_principle_mk hB (hbpos n) T
  have ht2D : Tendsto (fun n ↦ 2 * P (D n)) atTop (𝓝 (2 * P Dge)) :=
    ENNReal.Tendsto.const_mul htD (by right; norm_num)
  have htC' : Tendsto (fun n ↦ P (C n)) atTop (𝓝 (2 * P Dge)) := by
    simpa only [hstrict] using ht2D
  exact tendsto_nhds_unique htC htC'

theorem IsBrownianReal.reflection_principle [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < B t ω} =
      2 * P {ω | a < B T ω} := by
  have hCross :
      P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < B t ω} =
        P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a < hB.toIsPreBrownianReal.mk B t ω} := by
    apply measure_congr
    filter_upwards [hB.mk_ae_forall_eq] with ω hω
    apply propext
    constructor
    · rintro ⟨t, ht, hBt⟩
      exact ⟨t, ht, by rwa [hω t]⟩
    · rintro ⟨t, ht, hBt⟩
      exact ⟨t, ht, by rwa [hω t] at hBt⟩
  have hTerminal : P {ω | a < B T ω} =
      P {ω | a < hB.toIsPreBrownianReal.mk B T ω} := by
    apply measure_congr
    filter_upwards [hB.mk_ae_forall_eq] with ω hω
    apply propext
    change (a < B T ω) ↔ (a < hB.toIsPreBrownianReal.mk B T ω)
    rw [hω T]
  rw [hCross, hTerminal]
  exact reflection_principle_mk hB.toIsPreBrownianReal ha T

/-- Closed-barrier Brownian reflection principle. -/
theorem IsBrownianReal.reflection_principle_ge [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {a : ℝ} (ha : 0 < a) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ B t ω} =
      2 * P {ω | a ≤ B T ω} := by
  have hCross :
      P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ B t ω} =
        P {ω | ∃ t : ℝ≥0, t ≤ T ∧ a ≤ hB.toIsPreBrownianReal.mk B t ω} := by
    apply measure_congr
    filter_upwards [hB.mk_ae_forall_eq] with ω hω
    apply propext
    constructor
    · rintro ⟨t, ht, hBt⟩
      exact ⟨t, ht, by rwa [hω t]⟩
    · rintro ⟨t, ht, hBt⟩
      exact ⟨t, ht, by rwa [hω t] at hBt⟩
  have hTerminal : P {ω | a ≤ B T ω} =
      P {ω | a ≤ hB.toIsPreBrownianReal.mk B T ω} := by
    apply measure_congr
    filter_upwards [hB.mk_ae_forall_eq] with ω hω
    apply propext
    change (a ≤ B T ω) ↔ (a ≤ hB.toIsPreBrownianReal.mk B T ω)
    rw [hω T]
  rw [hCross, hTerminal]
  exact reflection_principle_ge_mk hB.toIsPreBrownianReal ha T

end ProbabilityTheory
