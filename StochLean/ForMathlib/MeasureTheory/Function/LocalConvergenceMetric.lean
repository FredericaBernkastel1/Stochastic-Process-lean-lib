/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Function.ConvergenceInMeasureLocal
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# A metric for local convergence in measure

This file formalizes the exhaustion pseudometric from Klenke, Theorem 6.7.  On raw strongly
measurable maps it is a pseudometric, while on `AEEqFun` it becomes a genuine metric.  Its
convergent sequences are exactly the sequences which converge locally in measure.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [PseudoMetricSpace F]

/-- The truncated distance `1 ∧ dist`, whose integral detects convergence in measure. -/
def truncatedDist (f g : α → F) (x : α) : ℝ := min 1 (dist (f x) (g x))

theorem truncatedDist_stronglyMeasurable {f g : α → F}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (truncatedDist f g) := by
  unfold truncatedDist
  fun_prop

/-- On a finite measure space, convergence in measure forces the integral of the truncated
distance to tend to zero. -/
theorem tendsto_truncatedDist_integral [IsFiniteMeasure μ]
    {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : TendstoInMeasure μ f atTop g) :
    Tendsto (fun n ↦ ∫ x, truncatedDist (f n) g x ∂μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := (hfg.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ ↦ (0 : ℝ))
      (fun _ ↦ (1 : ℝ))
      (fun n ↦ (truncatedDist_stronglyMeasurable (hf (ns (ms n))) hg).aestronglyMeasurable)
      (integrable_const 1) (fun n ↦ Eventually.of_forall fun x ↦ by
        unfold truncatedDist
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one dist_nonneg)]
        exact min_le_left _ _)
      (hae.mono fun x hx ↦ by
        have hd : Tendsto (fun i ↦ dist ((f ∘ ns) (ms i) x) (g x)) atTop (𝓝 0) := by
          simpa using hx.dist
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ g x) atTop (𝓝 (g x)))
        have h1 : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
        have hm := h1.min hd
        simpa [truncatedDist] using hm)

/-- Conversely, a vanishing truncated-distance integral implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_truncatedDist_integral [IsFiniteMeasure μ]
    {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : Tendsto (fun n ↦ ∫ x, truncatedDist (f n) g x ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  apply squeeze_zero
  · exact fun _ ↦ measureReal_nonneg
  · intro n
    have hsubset : {x | ε ≤ dist (f n x) (g x)} ⊆
        {x | δ ≤ truncatedDist (f n) g x} := by
      intro x hx
      change ε ≤ dist (f n x) (g x) at hx
      change min ε 1 ≤ min 1 (dist (f n x) (g x))
      simpa only [min_comm] using min_le_min hx (le_refl 1)
    calc
      μ.real {x | ε ≤ dist (f n x) (g x)}
          ≤ μ.real {x | δ ≤ truncatedDist (f n) g x} := measureReal_mono hsubset
      _ ≤ δ⁻¹ * ∫ x, truncatedDist (f n) g x ∂μ := by
        have hnonneg : 0 ≤ᵐ[μ] truncatedDist (f n) g :=
          Eventually.of_forall fun _ ↦ le_min zero_le_one dist_nonneg
        have hint : Integrable (truncatedDist (f n) g) μ := ⟨
          (truncatedDist_stronglyMeasurable (hf n) hg).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := 1) <|
            Eventually.of_forall fun x ↦ by
              unfold truncatedDist
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one dist_nonneg)]
              exact min_le_left _ _ ⟩
        have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hint δ
        have hdiv : μ.real {x | δ ≤ truncatedDist (f n) g x}
            ≤ (∫ x, truncatedDist (f n) g x ∂μ) / δ :=
          (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hm)
        simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · simpa using hfg.const_mul δ⁻¹

/-- On a finite measure space, convergence in measure is characterized by the truncated-distance
integral. -/
theorem tendstoInMeasure_iff_tendsto_truncatedDist_integral [IsFiniteMeasure μ]
    {f : ℕ → α → F} {g : α → F}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) :
    TendstoInMeasure μ f atTop g ↔
      Tendsto (fun n ↦ ∫ x, truncatedDist (f n) g x ∂μ) atTop (𝓝 0) :=
  ⟨tendsto_truncatedDist_integral hf hg,
    tendstoInMeasure_of_tendsto_truncatedDist_integral hf hg⟩

/-- On a sigma-finite space it suffices to test local convergence on the canonical spanning sets. -/
theorem tendstoLocallyInMeasure_iff_spanning [SigmaFinite μ]
    {f : ℕ → α → F} {g : α → F} :
    TendstoLocallyInMeasure μ f atTop g ↔
      ∀ k, TendstoInMeasure (μ.restrict (spanningSets μ k)) f atTop g := by
  constructor
  · intro h k
    exact h (spanningSets μ k) (measurableSet_spanningSets μ k)
      (measure_spanningSets_lt_top μ k).ne
  · intro h s hs hμs
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    apply ENNReal.tendsto_atTop_zero.mpr
    intro δ hδ
    have htail : Tendsto (fun k ↦ μ (s \ spanningSets μ k)) atTop (𝓝 0) := by
      have hmono : Monotone (fun k ↦ s ∩ spanningSets μ k) :=
        monotone_const.inter (monotone_spanningSets μ)
      have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
      have hunion : ⋃ k, s ∩ spanningSets μ k = s := by
        rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
      rw [hunion] at hlim
      have hc : Tendsto (fun _ : ℕ ↦ μ s) atTop (𝓝 (μ s)) := tendsto_const_nhds
      have hsub := ENNReal.Tendsto.sub hc hlim (Or.inl hμs)
      have heq : (fun k ↦ μ s - μ (s ∩ spanningSets μ k)) =
          fun k ↦ μ (s \ spanningSets μ k) := by
        funext k
        rw [show s \ spanningSets μ k = s \ (s ∩ spanningSets μ k) by
          ext x; simp]
        exact (measure_sdiff inter_subset_left
          (hs.inter (measurableSet_spanningSets μ k)).nullMeasurableSet
          (ne_top_of_le_ne_top hμs (measure_mono inter_subset_left))).symm
      change Tendsto (fun k ↦ μ s - μ (s ∩ spanningSets μ k)) atTop
        (𝓝 (μ s - μ s)) at hsub
      rw [heq] at hsub
      simpa using hsub
    have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
    obtain ⟨k, hk⟩ := ENNReal.tendsto_atTop_zero.mp htail (δ / 2) hhalf
    have hkconv := h k
    rw [tendstoInMeasure_iff_dist] at hkconv
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hkconv ε hε) (δ / 2) hhalf
    refine ⟨N, fun n hn ↦ ?_⟩
    let B := {x | ε ≤ dist (f n x) (g x)}
    have hsubset : B ∩ s ⊆ (B ∩ spanningSets μ k) ∪ (s \ spanningSets μ k) := by
      intro x hx
      by_cases hxspan : x ∈ spanningSets μ k
      · exact Or.inl ⟨hx.1, hxspan⟩
      · exact Or.inr ⟨hx.2, hxspan⟩
    have hN' := hN n hn
    rw [Measure.restrict_apply' (measurableSet_spanningSets μ k)] at hN'
    change (μ.restrict s) B ≤ δ
    rw [Measure.restrict_apply' hs]
    calc
      μ (B ∩ s) ≤ μ ((B ∩ spanningSets μ k) ∪
          (s \ spanningSets μ k)) := measure_mono hsubset
      _ ≤ μ (B ∩ spanningSets μ k) + μ (s \ spanningSets μ k) :=
        measure_union_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hN' (hk k le_rfl)
      _ = δ := ENNReal.add_halves δ

/-- A raw strongly measurable map, before quotienting by almost-everywhere equality. -/
structure StronglyMeasurableMap (X Y : Type*) [MeasurableSpace X] [TopologicalSpace Y] where
  toFun : X → Y
  stronglyMeasurable_toFun : StronglyMeasurable toFun

instance {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] :
    CoeFun (StronglyMeasurableMap X Y) (fun _ ↦ X → Y) := ⟨StronglyMeasurableMap.toFun⟩

@[ext]
theorem StronglyMeasurableMap.ext {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    {f g : StronglyMeasurableMap X Y} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      simp only [mk.injEq]
      funext x
      exact h x

/-- The normalized finite-measure component in Klenke's exhaustion pseudometric. -/
noncomputable def localConvergenceComponent [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (k : ℕ) : ℝ :=
  (∫ x in spanningSets μ k, truncatedDist f g x ∂μ) /
    (1 + μ.real (spanningSets μ k))

/-- The geometric coefficient for the `k`-th exhaustion component. -/
noncomputable def localConvergenceWeight (k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (k + 1)

/-- Klenke's weighted exhaustion pseudodistance on raw strongly measurable maps. -/
noncomputable def localConvergencePseudodist [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) : ℝ :=
  ∑' k, localConvergenceWeight k * localConvergenceComponent (μ := μ) f g k

theorem truncatedDist_nonneg (f g : α → F) (x : α) : 0 ≤ truncatedDist f g x :=
  le_min zero_le_one dist_nonneg

theorem truncatedDist_le_one (f g : α → F) (x : α) : truncatedDist f g x ≤ 1 :=
  min_le_left _ _

@[simp]
theorem truncatedDist_self (f : α → F) : truncatedDist f f = 0 := by
  funext x
  simp [truncatedDist]

theorem truncatedDist_comm (f g : α → F) : truncatedDist f g = truncatedDist g f := by
  funext x
  simp only [truncatedDist, dist_comm]

theorem truncatedDist_triangle (f g h : α → F) (x : α) :
    truncatedDist f h x ≤ truncatedDist f g x + truncatedDist g h x := by
  unfold truncatedDist
  by_cases hfg : 1 ≤ dist (f x) (g x)
  · rw [min_eq_left hfg]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min zero_le_one dist_nonneg))
  by_cases hgh : 1 ≤ dist (g x) (h x)
  · rw [min_eq_left hgh]
    exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min zero_le_one dist_nonneg))
  · rw [min_eq_right (not_le.mp hfg).le, min_eq_right (not_le.mp hgh).le]
    exact (min_le_right _ _).trans (dist_triangle _ _ _)

theorem truncatedDist_integrable_restrict [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (k : ℕ) :
    Integrable (truncatedDist f g) (μ.restrict (spanningSets μ k)) := by
  let _ : IsFiniteMeasure (μ.restrict (spanningSets μ k)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ k).ne
  exact ⟨(truncatedDist_stronglyMeasurable f.stronglyMeasurable_toFun
      g.stronglyMeasurable_toFun).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) <|
      Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (truncatedDist_nonneg f g x)]
        exact truncatedDist_le_one f g x⟩

theorem localConvergenceComponent_nonneg [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (k : ℕ) :
    0 ≤ localConvergenceComponent (μ := μ) f g k := by
  exact div_nonneg (integral_nonneg_of_ae <|
    Eventually.of_forall (truncatedDist_nonneg f g)) (by positivity)

theorem localConvergenceComponent_le_one [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (k : ℕ) :
    localConvergenceComponent (μ := μ) f g k ≤ 1 := by
  let _ : IsFiniteMeasure (μ.restrict (spanningSets μ k)) :=
    isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ k).ne
  have hle := integral_mono_ae (truncatedDist_integrable_restrict (μ := μ) f g k)
    (integrable_const 1) (Eventually.of_forall (truncatedDist_le_one f g))
  rw [localConvergenceComponent, div_le_one (by positivity)]
  calc
    ∫ x in spanningSets μ k, truncatedDist f g x ∂μ
        ≤ ∫ _ : α, (1 : ℝ) ∂(μ.restrict (spanningSets μ k)) := hle
    _ = μ.real (spanningSets μ k) := by simp
    _ ≤ 1 + μ.real (spanningSets μ k) := le_add_of_nonneg_left zero_le_one

@[simp]
theorem localConvergenceComponent_self [SigmaFinite μ]
    (f : StronglyMeasurableMap α F) (k : ℕ) :
    localConvergenceComponent (μ := μ) f f k = 0 := by
  simp [localConvergenceComponent]

theorem localConvergenceComponent_comm [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (k : ℕ) :
    localConvergenceComponent (μ := μ) f g k =
      localConvergenceComponent (μ := μ) g f k := by
  simp only [localConvergenceComponent, truncatedDist_comm]

theorem localConvergenceComponent_triangle [SigmaFinite μ]
    (f g h : StronglyMeasurableMap α F) (k : ℕ) :
    localConvergenceComponent (μ := μ) f h k ≤
      localConvergenceComponent (μ := μ) f g k +
        localConvergenceComponent (μ := μ) g h k := by
  have hle := integral_mono_ae (truncatedDist_integrable_restrict (μ := μ) f h k)
    ((truncatedDist_integrable_restrict (μ := μ) f g k).add
      (truncatedDist_integrable_restrict (μ := μ) g h k))
    (Eventually.of_forall (truncatedDist_triangle f g h))
  have hle' : (∫ x in spanningSets μ k, truncatedDist f h x ∂μ) ≤
      (∫ x in spanningSets μ k, truncatedDist f g x ∂μ) +
        ∫ x in spanningSets μ k, truncatedDist g h x ∂μ := by
    calc
      _ ≤ ∫ x in spanningSets μ k,
          truncatedDist f g x + truncatedDist g h x ∂μ := by
        simpa only [Pi.add_apply] using hle
      _ = _ := integral_add (truncatedDist_integrable_restrict (μ := μ) f g k)
        (truncatedDist_integrable_restrict (μ := μ) g h k)
  unfold localConvergenceComponent
  calc
    (∫ x in spanningSets μ k, truncatedDist f h x ∂μ) /
        (1 + μ.real (spanningSets μ k))
      ≤ ((∫ x in spanningSets μ k, truncatedDist f g x ∂μ) +
          ∫ x in spanningSets μ k, truncatedDist g h x ∂μ) /
          (1 + μ.real (spanningSets μ k)) :=
        div_le_div_of_nonneg_right hle' (by positivity)
    _ = (∫ x in spanningSets μ k, truncatedDist f g x ∂μ) /
          (1 + μ.real (spanningSets μ k)) +
        (∫ x in spanningSets μ k, truncatedDist g h x ∂μ) /
          (1 + μ.real (spanningSets μ k)) := by ring

theorem localConvergenceWeight_pos (k : ℕ) : 0 < localConvergenceWeight k := by
  unfold localConvergenceWeight
  positivity

theorem localConvergenceWeight_nonneg (k : ℕ) : 0 ≤ localConvergenceWeight k :=
  (localConvergenceWeight_pos k).le

theorem summable_localConvergenceWeight : Summable localConvergenceWeight := by
  refine (summable_geometric_two.mul_left (2 : ℝ)⁻¹).congr (fun k ↦ ?_)
  simp [localConvergenceWeight, pow_succ', one_div]

theorem summable_localConvergenceTerms [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) :
    Summable (fun k ↦ localConvergenceWeight k *
      localConvergenceComponent (μ := μ) f g k) := by
  exact Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (localConvergenceWeight_nonneg k)
      (localConvergenceComponent_nonneg f g k))
    (fun k ↦ by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (localConvergenceComponent_le_one f g k) (localConvergenceWeight_nonneg k))
    summable_localConvergenceWeight

theorem localConvergencePseudodist_nonneg [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) :
    0 ≤ localConvergencePseudodist (μ := μ) f g := by
  exact tsum_nonneg fun k ↦ mul_nonneg (localConvergenceWeight_nonneg k)
    (localConvergenceComponent_nonneg f g k)

@[simp]
theorem localConvergencePseudodist_self [SigmaFinite μ]
    (f : StronglyMeasurableMap α F) :
    localConvergencePseudodist (μ := μ) f f = 0 := by
  simp [localConvergencePseudodist]

theorem localConvergencePseudodist_comm [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) :
    localConvergencePseudodist (μ := μ) f g =
      localConvergencePseudodist (μ := μ) g f := by
  unfold localConvergencePseudodist
  apply congrArg tsum
  funext k
  rw [localConvergenceComponent_comm]

/-- The raw exhaustion pseudodistance identifies almost-everywhere equal maps. -/
theorem localConvergencePseudodist_eq_zero_of_ae_eq [SigmaFinite μ]
    (f g : StronglyMeasurableMap α F) (hfg : (f : α → F) =ᵐ[μ] g) :
    localConvergencePseudodist (μ := μ) f g = 0 := by
  unfold localConvergencePseudodist
  have hcomponent (k : ℕ) : localConvergenceComponent (μ := μ) f g k = 0 := by
    unfold localConvergenceComponent
    have htrunc : truncatedDist f g =ᵐ[μ.restrict (spanningSets μ k)] (fun _ ↦ 0) :=
      ae_restrict_of_ae (hfg.mono fun x hx ↦ by simp [truncatedDist, hx])
    rw [show (∫ x in spanningSets μ k, truncatedDist f g x ∂μ) = 0 by
      calc
        _ = ∫ _x in spanningSets μ k, (0 : ℝ) ∂μ := integral_congr_ae htrunc
        _ = 0 := by simp]
    exact zero_div _
  simp only [hcomponent, mul_zero, tsum_zero]

theorem localConvergencePseudodist_triangle [SigmaFinite μ]
    (f g h : StronglyMeasurableMap α F) :
    localConvergencePseudodist (μ := μ) f h ≤
      localConvergencePseudodist (μ := μ) f g +
        localConvergencePseudodist (μ := μ) g h := by
  unfold localConvergencePseudodist
  calc
    ∑' k, localConvergenceWeight k * localConvergenceComponent (μ := μ) f h k
      ≤ ∑' k, (localConvergenceWeight k * localConvergenceComponent (μ := μ) f g k +
          localConvergenceWeight k * localConvergenceComponent (μ := μ) g h k) := by
        exact (summable_localConvergenceTerms f h).tsum_le_tsum
          (fun k ↦
            calc
              localConvergenceWeight k * localConvergenceComponent (μ := μ) f h k ≤
                  localConvergenceWeight k *
                    (localConvergenceComponent (μ := μ) f g k +
                      localConvergenceComponent (μ := μ) g h k) :=
                mul_le_mul_of_nonneg_left (localConvergenceComponent_triangle f g h k)
                  (localConvergenceWeight_nonneg k)
              _ = localConvergenceWeight k * localConvergenceComponent (μ := μ) f g k +
                  localConvergenceWeight k * localConvergenceComponent (μ := μ) g h k :=
                mul_add _ _ _)
          ((summable_localConvergenceTerms f g).add (summable_localConvergenceTerms g h))
    _ = (∑' k, localConvergenceWeight k * localConvergenceComponent (μ := μ) f g k) +
        ∑' k, localConvergenceWeight k * localConvergenceComponent (μ := μ) g h k :=
      Summable.tsum_add (f := fun k ↦ localConvergenceWeight k *
        localConvergenceComponent (μ := μ) f g k)
        (g := fun k ↦ localConvergenceWeight k *
          localConvergenceComponent (μ := μ) g h k)
        (summable_localConvergenceTerms f g) (summable_localConvergenceTerms g h)

@[instance_reducible]
noncomputable def localConvergencePseudoMetricSpace [SigmaFinite μ] :
    PseudoMetricSpace (StronglyMeasurableMap α F) where
  dist := localConvergencePseudodist (μ := μ)
  dist_self := fun f ↦ localConvergencePseudodist_self (μ := μ) f
  dist_comm := fun f g ↦ localConvergencePseudodist_comm (μ := μ) f g
  dist_triangle := fun f g h ↦ localConvergencePseudodist_triangle (μ := μ) f g h

theorem localConvergencePseudodist_tendsto_iff [SigmaFinite μ]
    {f : ℕ → StronglyMeasurableMap α F} {g : StronglyMeasurableMap α F} :
    Tendsto (fun n ↦ localConvergencePseudodist (μ := μ) (f n) g) atTop (𝓝 0) ↔
      TendstoLocallyInMeasure μ (fun n ↦ f n) atTop g := by
  constructor
  · intro hdist
    rw [tendstoLocallyInMeasure_iff_spanning]
    intro k
    have hterm_nonneg (n : ℕ) : 0 ≤ localConvergenceWeight k *
        localConvergenceComponent (μ := μ) (f n) g k :=
      mul_nonneg (localConvergenceWeight_nonneg k)
        (localConvergenceComponent_nonneg (f n) g k)
    have hterm_le (n : ℕ) : localConvergenceWeight k *
        localConvergenceComponent (μ := μ) (f n) g k ≤
          localConvergencePseudodist (μ := μ) (f n) g := by
      have hs := (summable_localConvergenceTerms (μ := μ) (f n) g).sum_le_tsum {k}
        (fun i _ ↦ mul_nonneg (localConvergenceWeight_nonneg i)
          (localConvergenceComponent_nonneg (f n) g i))
      simpa only [Finset.sum_singleton, localConvergencePseudodist] using hs
    have hterm : Tendsto (fun n ↦ localConvergenceWeight k *
        localConvergenceComponent (μ := μ) (f n) g k) atTop (𝓝 0) :=
      squeeze_zero hterm_nonneg hterm_le hdist
    have hcomponent : Tendsto (fun n ↦
        localConvergenceComponent (μ := μ) (f n) g k) atTop (𝓝 0) := by
      have hscaled := hterm.const_mul (localConvergenceWeight k)⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ (localConvergenceWeight_pos k).ne',
        one_mul, mul_zero] using hscaled
    have hintegral : Tendsto (fun n ↦
        ∫ x in spanningSets μ k, truncatedDist (f n) g x ∂μ) atTop (𝓝 0) := by
      have hscaled := hcomponent.const_mul (1 + μ.real (spanningSets μ k))
      have hdenom : (1 + μ.real (spanningSets μ k) : ℝ) ≠ 0 := by positivity
      have heq (n : ℕ) : (1 + μ.real (spanningSets μ k)) *
          localConvergenceComponent (μ := μ) (f n) g k =
            ∫ x in spanningSets μ k, truncatedDist (f n) g x ∂μ := by
        rw [localConvergenceComponent]
        field_simp
      simpa only [heq, mul_zero] using hscaled
    let _ : IsFiniteMeasure (μ.restrict (spanningSets μ k)) :=
      isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ k).ne
    exact tendstoInMeasure_of_tendsto_truncatedDist_integral
      (fun n ↦ (f n).stronglyMeasurable_toFun) g.stronglyMeasurable_toFun hintegral
  · intro hlocal
    have hcomponent (k : ℕ) : Tendsto (fun n ↦
        localConvergenceComponent (μ := μ) (f n) g k) atTop (𝓝 0) := by
      let _ : IsFiniteMeasure (μ.restrict (spanningSets μ k)) :=
        isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top μ k).ne
      have hintegral := tendsto_truncatedDist_integral
        (fun n ↦ (f n).stronglyMeasurable_toFun) g.stronglyMeasurable_toFun
        (hlocal (spanningSets μ k) (measurableSet_spanningSets μ k)
          (measure_spanningSets_lt_top μ k).ne)
      simpa only [localConvergenceComponent, zero_div] using
        hintegral.div_const (1 + μ.real (spanningSets μ k))
    have hterms (k : ℕ) : Tendsto (fun n ↦ localConvergenceWeight k *
        localConvergenceComponent (μ := μ) (f n) g k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (hcomponent k).const_mul (localConvergenceWeight k)
    simpa only [localConvergencePseudodist, tsum_zero] using
      tendsto_tsum_of_dominated_convergence summable_localConvergenceWeight hterms
        (Eventually.of_forall fun n k ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg <| mul_nonneg
            (localConvergenceWeight_nonneg k)
            (localConvergenceComponent_nonneg (f n) g k)]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (localConvergenceComponent_le_one (f n) g k)
            (localConvergenceWeight_nonneg k))

theorem tendsto_localConvergencePseudoMetricSpace_iff [SigmaFinite μ]
    {f : ℕ → StronglyMeasurableMap α F} {g : StronglyMeasurableMap α F} :
    letI := localConvergencePseudoMetricSpace (μ := μ) (F := F)
    Tendsto f atTop (𝓝 g) ↔ TendstoLocallyInMeasure μ (fun n ↦ f n) atTop g := by
  let _ := localConvergencePseudoMetricSpace (μ := μ) (F := F)
  rw [tendsto_iff_dist_tendsto_zero]
  exact localConvergencePseudodist_tendsto_iff

section QuotientMetric

variable {G : Type*} [MetricSpace G]

/-- The canonical strongly measurable representative of an almost-everywhere equivalence class. -/
noncomputable def AEEqFun.toStronglyMeasurableMap (f : α →ₘ[μ] G) :
    StronglyMeasurableMap α G := ⟨f, f.stronglyMeasurable⟩

/-- The exhaustion distance on almost-everywhere equivalence classes. -/
noncomputable def AEEqFun.localConvergenceDist [SigmaFinite μ]
    (f g : α →ₘ[μ] G) : ℝ :=
  localConvergencePseudodist (μ := μ) f.toStronglyMeasurableMap g.toStronglyMeasurableMap

theorem AEEqFun.localConvergenceDist_eq_zero_imp [SigmaFinite μ]
    {f g : α →ₘ[μ] G} (hzero : f.localConvergenceDist g = 0) : f = g := by
  apply AEEqFun.ext
  have hrestricted (k : ℕ) : f =ᵐ[μ.restrict (spanningSets μ k)] g := by
    let f' := f.toStronglyMeasurableMap
    let g' := g.toStronglyMeasurableMap
    have hterm_le : localConvergenceWeight k *
        localConvergenceComponent (μ := μ) f' g' k ≤ 0 := by
      have hs := (summable_localConvergenceTerms (μ := μ) f' g').sum_le_tsum {k}
        (fun i _ ↦ mul_nonneg (localConvergenceWeight_nonneg i)
          (localConvergenceComponent_nonneg f' g' i))
      calc
        localConvergenceWeight k * localConvergenceComponent (μ := μ) f' g' k ≤
            localConvergencePseudodist (μ := μ) f' g' := by
          simpa only [Finset.sum_singleton, localConvergencePseudodist] using hs
        _ = 0 := by simpa only [AEEqFun.localConvergenceDist, f', g'] using hzero
    have hterm_zero : localConvergenceWeight k *
        localConvergenceComponent (μ := μ) f' g' k = 0 :=
      le_antisymm hterm_le (mul_nonneg (localConvergenceWeight_nonneg k)
        (localConvergenceComponent_nonneg f' g' k))
    have hcomponent_zero : localConvergenceComponent (μ := μ) f' g' k = 0 :=
      (mul_eq_zero.mp hterm_zero).resolve_left (localConvergenceWeight_pos k).ne'
    have hintegral_zero :
        (∫ x in spanningSets μ k, truncatedDist f g x ∂μ) = 0 := by
      rw [localConvergenceComponent, div_eq_zero_iff] at hcomponent_zero
      exact hcomponent_zero.resolve_right (by positivity)
    have htrunc : truncatedDist f g =ᵐ[μ.restrict (spanningSets μ k)] 0 :=
      (integral_eq_zero_iff_of_nonneg (truncatedDist_nonneg f g)
        (truncatedDist_integrable_restrict (μ := μ) f' g' k)).mp hintegral_zero
    exact htrunc.mono fun x hx ↦ by
      have hdist : dist (f x) (g x) = 0 := by
        by_contra hd
        have hpos : 0 < dist (f x) (g x) :=
          lt_of_le_of_ne dist_nonneg (Ne.symm hd)
        have hmin : 0 < min 1 (dist (f x) (g x)) := lt_min zero_lt_one hpos
        change min 1 (dist (f x) (g x)) = 0 at hx
        linarith
      exact dist_eq_zero.mp hdist
  have hspan (k : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ k → f x = g x :=
    (ae_restrict_iff' (measurableSet_spanningSets μ k)).mp (hrestricted k)
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, x ∈ spanningSets μ k → f x = g x :=
    eventually_countable_forall.mpr hspan
  filter_upwards [hall] with x hx
  have hxunion : x ∈ ⋃ k, spanningSets μ k := by
    rw [iUnion_spanningSets]
    trivial
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxunion
  exact hx k hxk

/-- On the a.e. quotient, Klenke's exhaustion pseudodistance is a genuine metric. -/
noncomputable instance instMetricSpaceAEEqFunLocalConvergence [SigmaFinite μ] :
    MetricSpace (α →ₘ[μ] G) where
  dist := AEEqFun.localConvergenceDist
  dist_self := fun f ↦ localConvergencePseudodist_self (μ := μ) f.toStronglyMeasurableMap
  dist_comm := fun f g ↦ localConvergencePseudodist_comm (μ := μ)
    f.toStronglyMeasurableMap g.toStronglyMeasurableMap
  dist_triangle := fun f g h ↦ localConvergencePseudodist_triangle (μ := μ)
    f.toStronglyMeasurableMap g.toStronglyMeasurableMap h.toStronglyMeasurableMap
  eq_of_dist_eq_zero := AEEqFun.localConvergenceDist_eq_zero_imp

/-- Metric convergence on `AEEqFun` is precisely local convergence in measure. -/
theorem AEEqFun.tendsto_iff_tendstoLocallyInMeasure [SigmaFinite μ]
    {f : ℕ → α →ₘ[μ] G} {g : α →ₘ[μ] G} :
    Tendsto f atTop (𝓝 g) ↔ TendstoLocallyInMeasure μ (fun n ↦ f n) atTop g := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact localConvergencePseudodist_tendsto_iff

end QuotientMetric

end MeasureTheory
