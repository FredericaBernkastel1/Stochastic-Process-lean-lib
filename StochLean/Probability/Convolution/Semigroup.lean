/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Metrizable.Basic

/-!
# Convolution semigroups of probability laws

The basic predicate contains only the semigroup equation.  In particular it does not silently
assert an identity law at time zero or continuity.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Additive convolution, closed in the canonical probability-measure subtype. -/
noncomputable def conv (μ ν : ProbabilityMeasure G) : ProbabilityMeasure G :=
  ⟨(μ : Measure G) ∗ (ν : Measure G), inferInstance⟩

@[simp, norm_cast]
theorem coe_conv (μ ν : ProbabilityMeasure G) :
    ((conv μ ν : ProbabilityMeasure G) : Measure G) = (μ : Measure G) ∗ (ν : Measure G) :=
  rfl

/-- Canonical Dirac probability law. -/
noncomputable def pointMass (x : G) : ProbabilityMeasure G :=
  ⟨Measure.dirac x, inferInstance⟩

omit [AddCommMonoid G] [MeasurableAdd₂ G] in
@[simp, norm_cast]
theorem coe_pointMass (x : G) :
    ((pointMass x : ProbabilityMeasure G) : Measure G) = Measure.dirac x :=
  rfl

@[simp]
theorem conv_assoc (μ ν ρ : ProbabilityMeasure G) :
    conv (conv μ ν) ρ = conv μ (conv ν ρ) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv]
  exact Measure.conv_assoc _ _ _

@[simp]
theorem conv_comm (μ ν : ProbabilityMeasure G) : conv μ ν = conv ν μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv]
  exact Measure.conv_comm (μ : Measure G) (ν : Measure G)

@[simp]
theorem pointMass_zero_conv (μ : ProbabilityMeasure G) : conv (pointMass 0) μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv, coe_pointMass]
  exact Measure.dirac_zero_conv _

@[simp]
theorem conv_pointMass_zero (μ : ProbabilityMeasure G) : conv μ (pointMass 0) = μ := by
  rw [conv_comm, pointMass_zero_conv]

@[simp]
theorem pointMass_conv_pointMass (x y : G) :
    conv (pointMass x) (pointMass y) = pointMass (x + y) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv, coe_pointMass]
  exact Measure.dirac_conv_dirac x y

section Topology

open TopologicalSpace

variable [TopologicalSpace G] [PseudoMetrizableSpace G] [SecondCountableTopology G]
  [BorelSpace G] [ContinuousAdd G]

/-- Convolution of probability laws is jointly continuous for the canonical weak topology on a
second-countable pseudo-metrizable additive space. -/
theorem continuous_conv :
    Continuous (fun p : ProbabilityMeasure G × ProbabilityMeasure G ↦ conv p.1 p.2) := by
  let add : G × G → G := fun p ↦ p.1 + p.2
  have hadd : Continuous add := by
    exact continuous_fst.add continuous_snd
  have heq : (fun p : ProbabilityMeasure G × ProbabilityMeasure G ↦ conv p.1 p.2) =
      (fun p ↦ (p.1.prod p.2).map hadd.measurable.aemeasurable) := by
    funext p
    apply ProbabilityMeasure.toMeasure_injective
    rfl
  rw [heq]
  exact (ProbabilityMeasure.continuous_map hadd).comp ProbabilityMeasure.continuous_prod

end Topology

/-- The `n`-fold convolution power, including the canonical zeroth power `δ₀`. -/
noncomputable def convPow (μ : ProbabilityMeasure G) : ℕ → ProbabilityMeasure G
  | 0 => pointMass (G := G) 0
  | n + 1 => conv (convPow μ n) μ

@[simp]
theorem convPow_zero (μ : ProbabilityMeasure G) : convPow μ 0 = pointMass (G := G) 0 := rfl

@[simp]
theorem convPow_succ (μ : ProbabilityMeasure G) (n : ℕ) :
    convPow μ (n + 1) = conv (convPow μ n) μ := rfl

@[simp]
theorem convPow_one (μ : ProbabilityMeasure G) : convPow μ 1 = μ := by
  simp [convPow]

theorem convPow_add (μ : ProbabilityMeasure G) (m n : ℕ) :
    convPow μ (m + n) = conv (convPow μ m) (convPow μ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, convPow_succ, convPow_succ, ih, conv_assoc]

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {T G : Type*} [Add T] [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The law-level convolution semigroup property, with no identity or continuity bundled in. -/
def IsConvolutionSemigroup (ν : T → ProbabilityMeasure G) : Prop :=
  ∀ s t, ν (s + t) = ProbabilityMeasure.conv (ν s) (ν t)

theorem IsConvolutionSemigroup.add {ν : T → ProbabilityMeasure G}
    (hν : IsConvolutionSemigroup ν) (s t : T) :
    ν (s + t) = ProbabilityMeasure.conv (ν s) (ν t) :=
  hν s t

/-- On the real line, even the basic semigroup law forces the time-zero law to be `δ₀`.
This is derived rather than bundled into `IsConvolutionSemigroup`: the characteristic function of
an idempotent real probability law is a continuous `{0,1}`-valued function, hence is identically
one on the connected frequency line. -/
theorem IsConvolutionSemigroup.zero_eq_pointMass_real
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsConvolutionSemigroup ν) :
    ν 0 = ProbabilityMeasure.pointMass 0 := by
  have hzero : ν 0 = ProbabilityMeasure.conv (ν 0) (ν 0) := by
    simpa using hν 0 0
  have hcf (t : ℝ) : charFun (ν 0 : Measure ℝ) t =
      charFun (ν 0 : Measure ℝ) t * charFun (ν 0 : Measure ℝ) t := by
    have h := congrArg (fun μ : ProbabilityMeasure ℝ ↦ charFun (μ : Measure ℝ) t) hzero
    simpa only [ProbabilityMeasure.coe_conv, charFun_conv] using h
  have hroot (t : ℝ) :
      charFun (ν 0 : Measure ℝ) t = 0 ∨ charFun (ν 0 : Measure ℝ) t = 1 := by
    have hprod : charFun (ν 0 : Measure ℝ) t *
        (charFun (ν 0 : Measure ℝ) t - 1) = 0 := by
      calc
        _ = charFun (ν 0 : Measure ℝ) t * charFun (ν 0 : Measure ℝ) t -
            charFun (ν 0 : Measure ℝ) t := by ring
        _ = 0 := sub_eq_zero.mpr (hcf t).symm
    exact (mul_eq_zero.mp hprod).imp_right sub_eq_zero.mp
  let S : Set ℝ := {t | charFun (ν 0 : Measure ℝ) t = 1}
  have hclosed : IsClosed S := by
    exact isClosed_eq continuous_charFun continuous_const
  have hcomp : Sᶜ = {t | charFun (ν 0 : Measure ℝ) t = 0} := by
    ext t
    simp only [S, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · intro ht
      exact (hroot t).resolve_right ht
    · intro ht hOne
      rw [ht] at hOne
      exact zero_ne_one hOne
  have hopen : IsOpen S := by
    rw [← isClosed_compl_iff, hcomp]
    exact isClosed_eq continuous_charFun continuous_const
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  have hSuniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hnonempty
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  change charFun (ν 0 : Measure ℝ) t = charFun (Measure.dirac 0) t
  simpa [S, charFun_dirac] using ht

section Continuous

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- Continuous refinement on nonnegative real time.  The limit is explicitly from positive times. -/
def IsContinuousConvolutionSemigroup (ν : ℝ≥0 → ProbabilityMeasure G) : Prop :=
  IsConvolutionSemigroup ν ∧
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi (0 : ℝ≥0)))
      (𝓝 (ProbabilityMeasure.pointMass (G := G) (0 : G)))

theorem IsContinuousConvolutionSemigroup.isConvolutionSemigroup
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    IsConvolutionSemigroup ν :=
  hν.1

theorem IsContinuousConvolutionSemigroup.tendsto_zero
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi (0 : ℝ≥0)))
      (𝓝 (ProbabilityMeasure.pointMass (G := G) (0 : G))) :=
  hν.2

/-- Positive-time convolution roots supplied by a continuous semigroup converge to `δ₀`. -/
theorem IsContinuousConvolutionSemigroup.roots_tendsto_zero
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ ν (t / (n + 1))) atTop
      (𝓝 (ProbabilityMeasure.pointMass (G := G) 0)) := by
  apply hν.tendsto_zero.comp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hden : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hreal : Tendsto (fun n : ℕ ↦ (t : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hnn := tendsto_real_toNNReal hreal
    convert hnn using 1
    · funext n
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (by positivity)]
      simp
    · simp
  · filter_upwards [] with n
    exact div_pos ht (by positivity)

section Metrizable

open TopologicalSpace

variable [PseudoMetrizableSpace G] [SecondCountableTopology G] [BorelSpace G]
  [ContinuousAdd G]

/-- Continuity at zero forces the semigroup's time-zero law to be the convolution identity.  This
is derived and is intentionally not part of the basic semigroup predicate. -/
theorem IsContinuousConvolutionSemigroup.zero_eq_pointMass
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    ν 0 = ProbabilityMeasure.pointMass (G := G) 0 := by
  let l := nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)
  letI : NeBot l := nhdsWithin_Ioi_neBot le_rfl
  have hpair : Tendsto (fun t ↦ (ν 0, ν t)) l
      (𝓝 (ν 0, ProbabilityMeasure.pointMass (G := G) 0)) :=
    Tendsto.prodMk_nhds tendsto_const_nhds hν.tendsto_zero
  have hconv : Tendsto (fun t ↦ ProbabilityMeasure.conv (ν 0) (ν t)) l
      (𝓝 (ProbabilityMeasure.conv (ν 0) (ProbabilityMeasure.pointMass (G := G) 0))) :=
    ProbabilityMeasure.continuous_conv.continuousAt.tendsto.comp hpair
  have hν' : Tendsto ν l
      (𝓝 (ProbabilityMeasure.conv (ν 0) (ProbabilityMeasure.pointMass (G := G) 0))) := by
    convert hconv using 1
    funext t
    rw [← hν.isConvolutionSemigroup.add, zero_add]
  have hu := tendsto_nhds_unique hν.tendsto_zero hν'
  simpa using hu.symm

/-- The one-sided source condition at zero, together with the derived identity law, gives ordinary
continuity at zero in nonnegative time. -/
theorem IsContinuousConvolutionSemigroup.continuousAt_zero
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν) :
    ContinuousAt ν 0 := by
  rw [continuousAt_def]
  intro s hs
  have hz : Tendsto ν (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) (nhds (ν 0)) := by
    simpa [hν.zero_eq_pointMass] using hν.tendsto_zero
  have hsWithin := hz hs
  obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hsWithin
  filter_upwards [hu] with x hx
  by_cases hzero : x = 0
  · simpa [hzero] using mem_of_mem_nhds hs
  · exact hus ⟨hx, pos_iff_ne_zero.mpr hzero⟩

/-- A continuous convolution semigroup is weakly right-continuous at every time. -/
theorem IsContinuousConvolutionSemigroup.continuousWithinAt_Ici
    {ν : ℝ≥0 → ProbabilityMeasure G} (hν : IsContinuousConvolutionSemigroup ν)
    (t : ℝ≥0) : ContinuousWithinAt ν (Set.Ici t) t := by
  have hdiff : Tendsto (fun u : ℝ≥0 ↦ u - t) (nhdsWithin t (Set.Ici t)) (𝓝 0) := by
    have hcont : Continuous (fun u : ℝ≥0 ↦ u - t) :=
      continuous_id.sub continuous_const
    have htend : Tendsto (fun u : ℝ≥0 ↦ u - t) (nhds t) (nhds (t - t)) :=
      hcont.continuousAt
    simpa only [tsub_self] using htend.mono_left
      (show nhdsWithin t (Set.Ici t) ≤ nhds t from inf_le_left)
  have hsmall := hν.continuousAt_zero.tendsto.comp hdiff
  have hpair : Tendsto (fun u : ℝ≥0 ↦ (ν t, ν (u - t)))
      (nhdsWithin t (Set.Ici t)) (𝓝 (ν t, ν 0)) :=
    Tendsto.prodMk_nhds tendsto_const_nhds hsmall
  have hconv := ProbabilityMeasure.continuous_conv.continuousAt.tendsto.comp hpair
  have hlimit : ProbabilityMeasure.conv (ν t) (ν 0) = ν t := by
    rw [hν.zero_eq_pointMass, ProbabilityMeasure.conv_pointMass_zero]
  rw [hlimit] at hconv
  refine hconv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp only [Function.comp_apply]
  rw [← hν.isConvolutionSemigroup.add, add_tsub_cancel_of_le hu]

end Metrizable

section Real

/-- A real continuous convolution semigroup is weakly continuous on all nonnegative times, not
merely right-continuous.  The left-hand argument uses characteristic functions and the semigroup
identity; no subtraction outside its natural ordered domain is used. -/
theorem IsContinuousConvolutionSemigroup.continuous_real
    {ν : ℝ≥0 → ProbabilityMeasure ℝ} (hν : IsContinuousConvolutionSemigroup ν) :
    Continuous ν := by
  rw [continuous_iff_seqContinuous]
  intro u t hut
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro z
  let d : ℕ → ℝ≥0 := fun n ↦ max (u n) t - min (u n) t
  have hmax : Tendsto (fun n ↦ max (u n) t) atTop (𝓝 t) := by
    simpa using hut.max (tendsto_const_nhds (x := t))
  have hmin : Tendsto (fun n ↦ min (u n) t) atTop (𝓝 t) := by
    simpa using hut.min (tendsto_const_nhds (x := t))
  have hd : Tendsto d atTop (𝓝 0) := by
    have hsub := hmax.sub hmin
    simpa [d] using hsub
  have hmeasure : Tendsto (fun n ↦ ν (d n)) atTop (𝓝 (ν 0)) :=
    hν.continuousAt_zero.tendsto.comp hd
  have hchar : Tendsto (fun n ↦ charFun (ν (d n) : Measure ℝ) z) atTop (𝓝 1) := by
    have hz := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hmeasure z
    simpa [hν.zero_eq_pointMass, ProbabilityMeasure.coe_pointMass, charFun_dirac] using hz
  have hbound : ∀ n,
      ‖charFun (ν (u n) : Measure ℝ) z - charFun (ν t : Measure ℝ) z‖ ≤
        ‖charFun (ν (d n) : Measure ℝ) z - 1‖ := by
    intro n
    by_cases htu : t ≤ u n
    · have hd_eq : d n = u n - t := by simp [d, htu]
      have hsemigroup := hν.isConvolutionSemigroup.add t (u n - t)
      rw [add_tsub_cancel_of_le htu] at hsemigroup
      have hcf := congrArg (fun ρ : ProbabilityMeasure ℝ ↦
        charFun (ρ : Measure ℝ) z) hsemigroup
      rw [ProbabilityMeasure.coe_conv, charFun_conv] at hcf
      rw [hd_eq, hcf]
      rw [show charFun (ν t : Measure ℝ) z * charFun (ν (u n - t) : Measure ℝ) z -
          charFun (ν t : Measure ℝ) z =
          charFun (ν t : Measure ℝ) z *
            (charFun (ν (u n - t) : Measure ℝ) z - 1) by ring, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_charFun_le_one (μ := (ν t : Measure ℝ)) z)
    · have hut' : u n ≤ t := le_of_not_ge htu
      have hd_eq : d n = t - u n := by simp [d, hut']
      have hsemigroup := hν.isConvolutionSemigroup.add (u n) (t - u n)
      rw [add_tsub_cancel_of_le hut'] at hsemigroup
      have hcf := congrArg (fun ρ : ProbabilityMeasure ℝ ↦
        charFun (ρ : Measure ℝ) z) hsemigroup
      rw [ProbabilityMeasure.coe_conv, charFun_conv] at hcf
      rw [hd_eq, hcf]
      rw [show charFun (ν (u n) : Measure ℝ) z -
          charFun (ν (u n) : Measure ℝ) z * charFun (ν (t - u n) : Measure ℝ) z =
          -(charFun (ν (u n) : Measure ℝ) z *
            (charFun (ν (t - u n) : Measure ℝ) z - 1)) by ring, norm_neg, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (norm_charFun_le_one (μ := (ν (u n) : Measure ℝ)) z)
  have hnorm : Tendsto (fun n ↦ ‖charFun (ν (d n) : Measure ℝ) z - 1‖)
      atTop (𝓝 0) := by
    have hzero : Tendsto (fun n ↦ charFun (ν (d n) : Measure ℝ) z - 1)
        atTop (𝓝 0) := by
      simpa using hchar.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1))
    exact tendsto_norm_zero.comp hzero
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbound hnorm)

end Real

end Continuous

end ProbabilityTheory
