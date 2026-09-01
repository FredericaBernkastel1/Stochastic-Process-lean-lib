/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.PathFunctionals
public import StochLean.Probability.Brownian.Transformations
public import StochLean.Probability.Process.Stopping

import Mathlib.MeasureTheory.Function.Piecewise

/-!
# Brownian Markov foundations

This module begins the stopping-time proof at its required deterministic-time base.  For the
canonical continuous representative, the present value together with all rational coordinates in
the past is a standard-Borel state variable.  The exact regular conditional law of a future value
given that entire state is the Gaussian transition law `N(current,t)`.

The countable past state is used because regular conditional distributions require a
standard-Borel conditioning variable.  Path continuity is what later identifies its generated
information with the full natural past modulo the Brownian law.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

/-- The source-standard upper dyadic approximation `2⁻ⁿ ⌈2ⁿ t⌉`. -/
noncomputable def dyadicRightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  rightGrid (2 ^ n - 1) t

theorem dyadicRightGrid_eq (n : ℕ) (t : ℝ≥0) :
    dyadicRightGrid n t =
      (Nat.ceil (((2 ^ n : ℕ) : ℝ≥0) * t) : ℝ≥0) / (2 ^ n : ℕ) := by
  simp only [dyadicRightGrid, rightGrid]
  rw [Nat.sub_add_cancel (Nat.one_le_pow n 2 (by norm_num))]

theorem le_dyadicRightGrid (n : ℕ) (t : ℝ≥0) : t ≤ dyadicRightGrid n t := by
  exact le_rightGrid (2 ^ n - 1) t

theorem countable_range_dyadicRightGrid (n : ℕ) :
    (Set.range (dyadicRightGrid n)).Countable := by
  exact countable_range_rightGrid (2 ^ n - 1)

theorem tendsto_dyadicRightGrid (t : ℝ≥0) :
    Tendsto (fun n ↦ dyadicRightGrid n t) atTop (nhds t) := by
  apply (tendsto_rightGrid t).comp
  exact (tendsto_sub_atTop_nat 1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℕ)) (by norm_num))

/-- Upper right-grid approximation preserves the stopping-time property for finite
`ℝ≥0`-valued stopping times. -/
theorem stoppingTime_rightGridFinite
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ (rightGrid n (τ ω) : WithTop ℝ≥0)) := by
  intro u
  let m : ℕ := n + 1
  have hm : (0 : ℝ≥0) < (m : ℝ≥0) := by positivity
  have hevent : {ω | (rightGrid n (τ ω) : WithTop ℝ≥0) ≤ u} =
      ⋃ k : {k : ℕ // (k : ℝ≥0) / m ≤ u},
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((k.1 : ℝ≥0) / m : ℝ≥0)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      have h' : rightGrid n (τ ω) ≤ u := WithTop.coe_le_coe.mp h
      refine ⟨⟨Nat.ceil ((m : ℝ≥0) * τ ω), ?_⟩, ?_⟩
      · simpa only [m, rightGrid] using h'
      · exact_mod_cast le_rightGrid n (τ ω)
    · rintro ⟨k, hk⟩
      have hk' : τ ω ≤ (k.1 : ℝ≥0) / m := WithTop.coe_le_coe.mp hk
      have hmul : (m : ℝ≥0) * τ ω ≤ k.1 := by
        have h := (le_div_iff₀ hm).mp hk'
        simpa [mul_comm] using h
      have hceil : Nat.ceil ((m : ℝ≥0) * τ ω) ≤ k.1 := Nat.ceil_le.mpr hmul
      apply WithTop.coe_le_coe.mpr
      calc
        rightGrid n (τ ω) =
            (Nat.ceil ((m : ℝ≥0) * τ ω) : ℝ≥0) / m := by rfl
        _ ≤ (k.1 : ℝ≥0) / m := by gcongr
        _ ≤ u := k.2
  rw [hevent]
  exact MeasurableSet.iUnion fun k ↦
    ℱ.mono k.2 _ (hτ ((k.1 : ℝ≥0) / m))

theorem stoppingTime_dyadicRightGridFinite
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω ↦ (dyadicRightGrid n (τ ω) : WithTop ℝ≥0)) := by
  exact stoppingTime_rightGridFinite hτ (2 ^ n - 1)

/-- A finite collection of increments after a deterministic time.  This is the cylinder-level
future object used throughout the strong-Markov argument; no uncountable product path space is
introduced. -/
def brownianFutureIncrements {I : Type*} (X : ℝ≥0 → Ω → ℝ)
    (s : ℝ≥0) (t : I → ℝ≥0) : Ω → I → ℝ :=
  fun ω i ↦ X (s + t i) ω - X s ω

/-- A finite future-increment vector evaluated after a finite random time. -/
def brownianFutureIncrementsAfter {I : Type*} (X : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (t : I → ℝ≥0) : Ω → I → ℝ :=
  fun ω i ↦ X (τ ω + t i) ω - X (τ ω) ω

theorem measurable_brownianFutureIncrements {I : Type*} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ u, Measurable (X u)) (s : ℝ≥0) (t : I → ℝ≥0) :
    Measurable (brownianFutureIncrements X s t) := by
  exact measurable_pi_lambda _ fun i ↦ (hX (s + t i)).sub (hX s)

/-- Countable pasting makes evaluation after a countable-range random time measurable using only
coordinate measurability. -/
theorem measurable_brownianFutureIncrementsAfter_of_countable
    {I : Type*} {X : ℝ≥0 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (τ : Ω → ℝ≥0) (hτcount : (Set.range τ).Countable)
    (hτslice : ∀ s, MeasurableSet {ω | τ ω = s}) (t : I → ℝ≥0) :
    Measurable (brownianFutureIncrementsAfter X τ t) := by
  classical
  let R := Set.range τ
  let slices : R → Set Ω := fun r ↦ {ω | τ ω = r.1}
  let part : IndexedPartition slices :=
    { eq_of_mem := fun {_ r q} hr hq ↦ Subtype.ext (hr.symm.trans hq)
      some := fun (r : R) ↦ Classical.choose r.property
      some_mem := fun (r : R) ↦ Classical.choose_spec r.property
      index := fun ω ↦ ⟨τ ω, ⟨ω, rfl⟩⟩
      mem_index := fun _ ↦ rfl }
  letI : Countable R := hτcount.to_subtype
  have hpw : Measurable (part.piecewise fun r ↦ brownianFutureIncrements X r.1 t) :=
    part.measurable_piecewise (fun r ↦ hτslice r.1) fun r ↦
      measurable_brownianFutureIncrements hX r.1 t
  have heq : part.piecewise (fun r ↦ brownianFutureIncrements X r.1 t) =
      brownianFutureIncrementsAfter X τ t := by
    funext ω
    simp only [IndexedPartition.piecewise_apply, part]
    rfl
  exact heq ▸ hpw

/-- A finite vector of post-`s` increments has the same law as the corresponding vector starting
at zero.  The proof compares the canonical finite-dimensional Brownian laws, so repeated times
and singular covariance matrices are allowed. -/
theorem IsPreBrownianReal.identDistrib_brownianFutureIncrements
    {I : Type*} [Finite I] (hB : IsPreBrownianReal B P) (s : ℝ≥0)
    (t : I → ℝ≥0) :
    IdentDistrib (brownianFutureIncrements B s t) (fun ω i ↦ B (t i) ω) P P := by
  classical
  letI := Fintype.ofFinite I
  let J : Finset ℝ≥0 := Finset.univ.image t
  let e (y : J → ℝ) (i : I) : ℝ := y ⟨t i, by
    simp only [J, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩⟩
  have hid : IdentDistrib
      (fun ω ↦ J.restrict (fun u ↦ B (s + u) ω - B s ω))
      (fun ω ↦ J.restrict (fun u ↦ B u ω)) P P :=
    ((hB.shift s).hasLaw J).identDistrib (hB.hasLaw J)
  have he : Measurable e := measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hcomp := hid.comp he
  change IdentDistrib (fun ω i ↦ B (s + t i) ω - B s ω) (fun ω i ↦ B (t i) ω) P P
  simpa [e, Function.comp_def] using hcomp

/-- Every finite future-increment vector is independent of the entire coordinate past at the
deterministic time `s`. -/
theorem IsPreBrownianReal.indepFun_brownianFutureIncrements_past
    {I : Type*} (hB : IsPreBrownianReal B P) (s : ℝ≥0) (t : I → ℝ≥0) :
    IndepFun (brownianFutureIncrements B s t)
      (fun ω (u : Set.Iic s) ↦ B u ω) P := by
  let φ : (ℝ≥0 → ℝ) → (I → ℝ) := fun y i ↦ y (t i)
  have hφ : Measurable φ := measurable_pi_lambda _ fun i ↦ measurable_pi_apply (t i)
  have hcomp := (hB.indepFun_shift s).comp hφ measurable_id
  convert hcomp using 1 <;>
    ext ω <;>
    rfl

/-- Deterministic-time Markov identity for every measurable finite-cylinder functional of the
future increments.  The right side is the unconditional Brownian expectation and therefore does
not depend on the present or the past. -/
theorem IsPreBrownianReal.condExp_futureIncrements_natural
    {I : Type*} [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (s : ℝ≥0) (t : I → ℝ≥0) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    P[(f ∘ brownianFutureIncrements B s t) |
        Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable) s] =ᵐ[P]
      fun _ ↦ P[f ∘ brownianFutureIncrements B s t] := by
  let Z : Ω → ℝ := f ∘ brownianFutureIncrements B s t
  have hZ : Measurable Z := hf.comp (measurable_brownianFutureIncrements hBm s t)
  have hindFun : IndepFun Z (fun ω (u : Set.Iic s) ↦ B u ω) P :=
    (hB.indepFun_brownianFutureIncrements_past s t).comp hf measurable_id
  have hind : Indep (MeasurableSpace.comap Z inferInstance)
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable) s) P := by
    rw [Filtration.natural_eq_comap]
    exact (IndepFun_iff_Indep _ _ _).mp hindFun
  change P[Z | Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable) s] =ᵐ[P]
    fun _ ↦ P[Z]
  exact condExp_indep_eq hZ.comap_le (Filtration.le _ _)
    (comap_measurable Z).stronglyMeasurable hind

/-- Countable-range Brownian strong Markov identity for finite future cylinders.  The random time
is genuinely finite (`ℝ≥0`-valued); it is embedded into Mathlib's `WithTop` stopping-time API
without introducing an arbitrary value at infinity. -/
theorem IsPreBrownianReal.condExp_futureIncrementsAfter_countable
    {I : Type*} [Finite I] [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (t : I → ℝ≥0) (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (ℱ : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (hτcount : (Set.range τ).Countable)
    (hℱ : ℱ = Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)) :
    P[(f ∘ brownianFutureIncrementsAfter B τ t) | hτ.measurableSpace] =ᵐ[P]
      fun _ ↦ P[f ∘ brownianFutureIncrements B 0 t] := by
  classical
  let τ' : Ω → WithTop ℝ≥0 := fun ω ↦ τ ω
  let R := Set.range τ
  let slices : R → Set Ω := fun r ↦ {ω | τ' ω = (r.1 : WithTop ℝ≥0)}
  let part : IndexedPartition slices :=
    { eq_of_mem := fun {_ r q} hr hq ↦ Subtype.ext <| WithTop.coe_eq_coe.mp (hr.symm.trans hq)
      some := fun (r : R) ↦ Classical.choose r.property
      some_mem := fun (r : R) ↦ by
        change τ' (Classical.choose r.property) = (r.1 : WithTop ℝ≥0)
        simpa only [τ'] using congrArg (fun u : ℝ≥0 ↦ (u : WithTop ℝ≥0))
          (Classical.choose_spec r.property)
      index := fun ω ↦ ⟨τ ω, ⟨ω, rfl⟩⟩
      mem_index := fun _ ↦ rfl }
  let Z : Ω → ℝ := f ∘ brownianFutureIncrementsAfter B τ t
  let Zs (s : ℝ≥0) : Ω → ℝ := f ∘ brownianFutureIncrements B s t
  have hτ'range : (Set.range τ').Countable := by
    refine (hτcount.image fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨τ ω, ⟨ω, rfl⟩, rfl⟩
  have hslices (r : R) : MeasurableSet (slices r) := by
    have hset := ℱ.le r.1 _ (hτ.measurableSet_eq_of_countable_range hτ'range r.1)
    simpa only [slices] using hset
  letI : Countable R := hτcount.to_subtype
  have hZ : Measurable Z := by
    have hpw : Measurable (part.piecewise fun r ↦ Zs r.1) :=
      part.measurable_piecewise hslices fun r ↦
        hf.comp (measurable_brownianFutureIncrements hBm r.1 t)
    have heq : part.piecewise (fun r ↦ Zs r.1) = Z := by
      funext ω
      simp only [IndexedPartition.piecewise_apply, part]
      rfl
    exact heq ▸ hpw
  have hZint : Integrable Z P := by
    apply (integrable_const C).mono' hZ.aestronglyMeasurable
    exact ae_of_all _ fun ω ↦ by
      change |f (brownianFutureIncrementsAfter B τ t ω)| ≤ C
      exact hbound _
  have hslice (s : ℝ≥0) :
      P[Z | hτ.measurableSpace] =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}]
        fun _ ↦ P[Zs 0] := by
    have hset : MeasurableSet {ω | τ' ω = (s : WithTop ℝ≥0)} := by
      have hset' := ℱ.le s _ (hτ.measurableSet_eq_of_countable_range hτ'range s)
      exact hset'
    have hfun : Z =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}] Zs s := by
      apply (ae_restrict_iff' hset).2
      exact Filter.Eventually.of_forall fun ω hω ↦ by
        have hτs : τ ω = s := WithTop.coe_eq_coe.mp hω
        subst s
        rfl
    have hlocal :
        P[Z | ℱ s] =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}]
          P[Zs s | ℱ s] := by
      calc
        P[Z | ℱ s] =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}]
            (P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)})[Z | ℱ s] :=
          (condExp_restrict_ae_eq_restrict (ℱ.le s)
            (hτ.measurableSet_eq_of_countable_range hτ'range s) hZint).symm
        _ =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}]
            (P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)})[Zs s | ℱ s] :=
          condExp_congr_ae hfun
        _ =ᵐ[P.restrict {ω | τ' ω = (s : WithTop ℝ≥0)}] P[Zs s | ℱ s] :=
          condExp_restrict_ae_eq_restrict (ℱ.le s)
            (hτ.measurableSet_eq_of_countable_range hτ'range s)
            ((integrable_const C).mono'
              (hf.comp (measurable_brownianFutureIncrements hBm s t)).aestronglyMeasurable
              (ae_of_all _ fun ω ↦ by
                change |f (brownianFutureIncrements B s t ω)| ≤ C
                exact hbound _))
    have hstop : P[Z | hτ.measurableSpace] =ᵐ[P.restrict
        {ω | τ' ω = (s : WithTop ℝ≥0)}]
        P[Z | ℱ s] :=
      condExp_stopping_time_ae_eq_restrict_eq_of_countable_range hτ hτ'range s
    have hdet : P[Zs s | ℱ s] =ᵐ[P] fun _ ↦ P[Zs s] := by
      rw [hℱ]
      exact hB.condExp_futureIncrements_natural hBm s t f hf
    have hlaw : P[Zs s] = P[Zs 0] := by
      have hids := (hB.identDistrib_brownianFutureIncrements s t).comp hf
      have hid0 := (hB.identDistrib_brownianFutureIncrements 0 t).comp hf
      exact hids.integral_eq.trans hid0.integral_eq.symm
    exact hstop.trans (hlocal.trans ((hdet.restrict).trans <| by
      filter_upwards [] with ω
      rw [hlaw]))
  have hsliceAll : ∀ᵐ ω ∂P, ∀ r : R, τ' ω = (r.1 : WithTop ℝ≥0) →
      P[Z | hτ.measurableSpace] ω = P[Zs 0] := by
    rw [ae_all_iff]
    intro r
    exact (ae_restrict_iff' (hslices r)).mp (hslice r.1)
  change P[Z | hτ.measurableSpace] =ᵐ[P] fun _ ↦ P[Zs 0]
  filter_upwards [hsliceAll] with ω hω
  exact hω ⟨τ ω, ⟨ω, rfl⟩⟩ rfl

/-- Limit step from countable upper approximations to an arbitrary finite stopping time.  This is
the analytic core of Brownian strong Markov: continuity gives convergence of the stopped future
cylinders, while the tower property moves the countable-time identity from each approximating
stopping field down to the target stopping field. -/
theorem IsPreBrownianReal.condExp_futureIncrementsAfter_of_countable_approx
    {I : Type*} [Finite I] [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (hcont : ∀ᵐ ω ∂P, Continuous (B · ω))
    (t : I → ℝ≥0) (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (hfcont : Continuous f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (hτ : IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (hτn : ∀ n, IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τn n ω : WithTop ℝ≥0)))
    (hτn_count : ∀ n, (Set.range (τn n)).Countable)
    (hτ_le : ∀ n ω, τ ω ≤ τn n ω)
    (hτn_lim : ∀ ω, Tendsto (fun n ↦ τn n ω) atTop (nhds (τ ω))) :
    P[(f ∘ brownianFutureIncrementsAfter B τ t) | hτ.measurableSpace] =ᵐ[P]
      fun _ ↦ P[f ∘ brownianFutureIncrements B 0 t] := by
  classical
  let ℱ := Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable)
  let Z := fun (n : ℕ) (ω : Ω) ↦ f (brownianFutureIncrementsAfter B (τn n) t ω)
  let Zlim : Ω → ℝ := fun ω ↦ f (brownianFutureIncrementsAfter B τ t ω)
  let c : ℝ := P[f ∘ brownianFutureIncrements B 0 t]
  have hτn_range (n : ℕ) :
      (Set.range (fun ω ↦ (τn n ω : WithTop ℝ≥0))).Countable := by
    refine ((hτn_count n).image fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0)).mono ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨τn n ω, ⟨ω, rfl⟩, rfl⟩
  have hτn_slice (n : ℕ) (s : ℝ≥0) : MeasurableSet {ω | τn n ω = s} := by
    have hs := ℱ.le s _ ((hτn n).measurableSet_eq_of_countable_range (hτn_range n) s)
    have heq : {ω | τn n ω = s} =
        {ω | (τn n ω : WithTop ℝ≥0) = (s : WithTop ℝ≥0)} := by
      ext ω
      exact WithTop.coe_eq_coe.symm
    rw [heq]
    exact hs
  have hZmeas (n : ℕ) : Measurable (Z n) := by
    exact hf.comp (measurable_brownianFutureIncrementsAfter_of_countable hBm
      (τn n) (hτn_count n) (hτn_slice n) t)
  have hZint (n : ℕ) : Integrable (Z n) P := by
    apply (integrable_const C).mono' (hZmeas n).aestronglyMeasurable
    exact ae_of_all _ fun ω ↦ by
      change |f (brownianFutureIncrementsAfter B (τn n) t ω)| ≤ C
      exact hbound _
  have hZlim_tendsto : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Z n ω) atTop (nhds (Zlim ω)) := by
    filter_upwards [hcont] with ω hBω
    apply hfcont.continuousAt.tendsto.comp
    rw [tendsto_pi_nhds]
    intro i
    have hplus : Tendsto (fun n ↦ τn n ω + t i) atTop (nhds (τ ω + t i)) :=
      (hτn_lim ω).add tendsto_const_nhds
    have hevalPlus : Tendsto (fun n ↦ B (τn n ω + t i) ω) atTop
        (nhds (B (τ ω + t i) ω)) := hBω.continuousAt.tendsto.comp hplus
    have heval : Tendsto (fun n ↦ B (τn n ω) ω) atTop
        (nhds (B (τ ω) ω)) := hBω.continuousAt.tendsto.comp (hτn_lim ω)
    exact hevalPlus.sub heval
  have hc_le : |c| ≤ C := by
    have hnorm := norm_integral_le_of_norm_le_const
      (μ := P) (f := f ∘ brownianFutureIncrements B 0 t) (C := C)
      (ae_of_all P fun ω ↦ by
        simpa only [Function.comp_apply, Real.norm_eq_abs] using
          hbound (brownianFutureIncrements B 0 t ω))
    simpa only [c, Real.norm_eq_abs, probReal_univ, mul_one] using hnorm
  have hcond (n : ℕ) :
      P[Z n | (hτn n).measurableSpace] =ᵐ[P] fun _ ↦ c := by
    exact hB.condExp_futureIncrementsAfter_countable hBm t f hf C hC hbound ℱ
      (τn n) (hτn n) (hτn_count n) rfl
  have hfg (n : ℕ) : P[Z n | hτ.measurableSpace] =ᵐ[P]
      P[(fun _ : Ω ↦ c) | hτ.measurableSpace] := by
    have hleTop : (fun ω ↦ (τ ω : WithTop ℝ≥0)) ≤
        (fun ω ↦ (τn n ω : WithTop ℝ≥0)) := fun ω ↦ by
      exact WithTop.coe_le_coe.mpr (hτ_le n ω)
    have hmspace : hτ.measurableSpace ≤ (hτn n).measurableSpace :=
      hτ.measurableSpace_mono (hτn n) hleTop
    have htower : P[P[Z n | (hτn n).measurableSpace] | hτ.measurableSpace] =ᵐ[P]
        P[Z n | hτ.measurableSpace] :=
      condExp_condExp_of_le hmspace (hτn n).measurableSpace_le
    exact htower.symm.trans (condExp_congr_ae (hcond n))
  have hlimit := tendsto_condExp_unique Z (fun _ _ ↦ c) Zlim (fun _ ↦ c)
    hZint (fun _ ↦ integrable_const c) hZlim_tendsto
    (ae_of_all _ fun _ ↦ tendsto_const_nhds) (fun _ ↦ C) (integrable_const C)
    (fun _ ↦ C) (integrable_const C)
    (fun n ↦ ae_of_all _ fun ω ↦ by
      change |f (brownianFutureIncrementsAfter B (τn n) t ω)| ≤ C
      exact hbound _)
    (fun _ ↦ ae_of_all _ fun _ ↦ by simpa [Real.norm_eq_abs] using hc_le)
    hfg
  change P[Zlim | hτ.measurableSpace] =ᵐ[P] fun _ ↦ c
  rw [condExp_const hτ.measurableSpace_le c] at hlimit
  exact hlimit

/-- Brownian strong Markov identity at an arbitrary finite stopping time, for every bounded
continuous finite-cylinder functional of the post-stopping increments.  The proof instantiates
the source-standard upper dyadic stopping-time approximation. -/
theorem IsBrownianReal.condExp_futureIncrementsAfter
    {I : Type*} [Finite I] [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hBm : ∀ u, Measurable (B u))
    (t : I → ℝ≥0) (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (hfcont : Continuous f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime
      (Filtration.natural B (fun u ↦ (hBm u).stronglyMeasurable))
      (fun ω ↦ (τ ω : WithTop ℝ≥0))) :
    P[(f ∘ brownianFutureIncrementsAfter B τ t) | hτ.measurableSpace] =ᵐ[P]
      fun _ ↦ P[f ∘ brownianFutureIncrements B 0 t] := by
  let τn : ℕ → Ω → ℝ≥0 := fun n ω ↦ dyadicRightGrid n (τ ω)
  apply hB.toIsPreBrownianReal.condExp_futureIncrementsAfter_of_countable_approx
    hBm hB.cont t f hf hfcont C hC hbound τ τn hτ
  · intro n
    exact stoppingTime_dyadicRightGridFinite hτ n
  · intro n
    exact (countable_range_dyadicRightGrid n).mono fun y hy ↦ by
      obtain ⟨ω, rfl⟩ := hy
      exact ⟨τ ω, rfl⟩
  · exact fun n ω ↦ le_dyadicRightGrid n (τ ω)
  · exact fun ω ↦ tendsto_dyadicRightGrid (τ ω)

/-- Current position together with a fixed countable dense grid of past coordinates. -/
noncomputable def brownianPastState (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
    Ω → ℝ × (ℕ → ℝ) :=
  fun ω ↦ (X s ω, fun n ↦ X (denseTimeUpTo s n) ω)

theorem measurable_brownianPastState {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (s : ℝ≥0) :
    Measurable (brownianPastState X s) := by
  exact (hX s).prodMk (measurable_pi_lambda _ fun n ↦ hX (denseTimeUpTo s n))

/-- A deterministic future increment of the canonical Brownian representative is independent of
the standard-Borel countable past state. -/
theorem IsPreBrownianReal.indepFun_increment_brownianPastState_mk
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    IndepFun
      (fun ω ↦ hB.mk B (s + t) ω - hB.mk B s ω)
      (brownianPastState (hB.mk B) s) P := by
  let C := hB.mk B
  have hC : IsPreBrownianReal C P := hB.isBrownianReal_mk.toIsPreBrownianReal
  have hi := hC.indepFun_shift s
  let φ : (ℝ≥0 → ℝ) → ℝ := fun y ↦ y t
  let is : Set.Iic s := ⟨s, by simp⟩
  let iDense (n : ℕ) : Set.Iic s := ⟨denseTimeUpTo s n, by
    change denseTimeUpTo s n ≤ s
    exact min_le_left _ _⟩
  let ψ : (Set.Iic s → ℝ) → ℝ × (ℕ → ℝ) :=
    fun y ↦ (y is, fun n ↦ y (iDense n))
  have hφ : Measurable φ := measurable_pi_apply t
  have hψ : Measurable ψ := by
    exact (measurable_pi_apply is).prodMk
      (measurable_pi_lambda _ fun n ↦ measurable_pi_apply (iDense n))
  have hcomp := hi.comp hφ hψ
  convert hcomp using 1 <;>
    ext ω <;>
    rfl

/-- The future increment of the canonical representative has the centered Gaussian law with
variance equal to the elapsed time. -/
theorem IsPreBrownianReal.map_increment_mk
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    P.map (fun ω ↦ hB.mk B (s + t) ω - hB.mk B s ω) = gaussianReal 0 t := by
  have hC : IsPreBrownianReal (hB.mk B) P := hB.isBrownianReal_mk.toIsPreBrownianReal
  refine (hC.hasLaw_sub (s + t) s).map_eq.trans (congrArg (gaussianReal 0) ?_)
  rw [Real.nndist_eq]
  apply NNReal.eq
  simp

/-- Exact deterministic-time Brownian transition law given all current and rational-past
coordinates of the canonical continuous representative. -/
theorem IsPreBrownianReal.condDistrib_mk_future_given_pastState
    [IsProbabilityMeasure P] (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    condDistrib (hB.mk B (s + t)) (brownianPastState (hB.mk B) s) P =ᵐ[
      P.map (brownianPastState (hB.mk B) s)]
        GaussianConditioning.translateNoiseKernel
          (fun y : ℝ × (ℕ → ℝ) ↦ y.1) (gaussianReal 0 t) := by
  let C := hB.mk B
  let R : Ω → ℝ := fun ω ↦ C (s + t) ω - C s ω
  let Y : Ω → ℝ × (ℕ → ℝ) := brownianPastState C s
  have hR : Measurable R := (hB.measurable_mk (s + t)).sub (hB.measurable_mk s)
  have hY : Measurable Y := measurable_brownianPastState hB.measurable_mk s
  have hRY : IndepFun R Y P := hB.indepFun_increment_brownianPastState_mk s t
  have hcond := GaussianConditioning.condDistrib_add_state_of_indepFun
    hR hY hRY (fun y : ℝ × (ℕ → ℝ) ↦ y.1) measurable_fst
  have hmap : P.map R = gaussianReal 0 t := hB.map_increment_mk s t
  rw [hmap] at hcond
  have heq : C (s + t) = fun ω ↦ (Y ω).1 + R ω := by
    funext ω
    simp only [C, Y, R, brownianPastState]
    ring
  change condDistrib (C (s + t)) Y P =ᵐ[P.map Y]
    GaussianConditioning.translateNoiseKernel
      (fun y : ℝ × (ℕ → ℝ) ↦ y.1) (gaussianReal 0 t)
  rw [heq]
  exact hcond

/-- Pointwise form of the Brownian transition kernel: at past state `y` the future law is
`N(y.1,t)`. -/
theorem translateNoiseKernel_brownian_apply (t : ℝ≥0)
    (y : ℝ × (ℕ → ℝ)) :
    GaussianConditioning.translateNoiseKernel
        (fun z : ℝ × (ℕ → ℝ) ↦ z.1) (gaussianReal 0 t) y =
      gaussianReal y.1 t := by
  rw [GaussianConditioning.translateNoiseKernel_apply _ measurable_fst]
  simpa using gaussianReal_map_const_add (μ := 0) (v := t) y.1

end ProbabilityTheory
