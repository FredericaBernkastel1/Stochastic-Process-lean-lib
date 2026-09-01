/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Brownian.Reflection
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Lévy's arcsine law for the last Brownian zero

This module defines a measurable last-zero functional for continuous paths and proves Lévy's
arcsine law.  The proof is internal to StochLean: it combines deterministic-time independence,
the closed-barrier reflection principle, a polar-coordinate computation for two independent
Gaussian variables, and endpoint limiting arguments.  Arbitrary Brownian realizations are
transferred through StochLean's canonical continuous representative.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ}

/-- Retraction of the canonical dense sequence onto a compact time interval. -/
noncomputable def denseTimeOn (q T : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  max q (min T (TopologicalSpace.denseSeq ℝ≥0 n))

theorem denseTimeOn_mem_Icc {q T : ℝ≥0} (hqT : q ≤ T) (n : ℕ) :
    denseTimeOn q T n ∈ Icc q T := by
  constructor
  · exact le_max_left _ _
  · exact max_le hqT (min_le_left _ _)

theorem exists_denseTimeOn_mem {q T s : ℝ≥0} (hqT : q ≤ T)
    (hs : s ∈ Icc q T) {U : Set ℝ≥0} (hU : U ∈ nhds s) :
    ∃ n : ℕ, denseTimeOn q T n ∈ U := by
  let r : ℝ≥0 → ℝ≥0 := fun x ↦ max q (min T x)
  have hr : Continuous r := continuous_const.max (continuous_const.min continuous_id)
  have hrs : r s = s := by
    simp only [r, min_eq_right hs.2, max_eq_right hs.1]
  have hpre : r ⁻¹' U ∈ nhds s := by
    exact hr.continuousAt (by simpa only [hrs] using hU)
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).mem_nhds hpre
  exact ⟨n, by simpa only [Set.mem_preimage, r, denseTimeOn] using hn⟩

/-- Countable compact-interval infimum of the absolute path. -/
noncomputable def denseAbsInfOn (X : ℝ≥0 → Ω → ℝ) (q T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal |X (denseTimeOn q T n) ω|

theorem measurable_denseAbsInfOn {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (q T : ℝ≥0) :
    Measurable (denseAbsInfOn X q T) := by
  apply Measurable.iInf
  intro n
  exact ENNReal.measurable_ofReal.comp ((hX _).abs)

theorem zero_lt_denseAbsInfOn_iff {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {q T : ℝ≥0} (hqT : q ≤ T) :
    0 < (⨅ n : ℕ, ENNReal.ofReal |f (denseTimeOn q T n)|) ↔
      ∀ s ∈ Icc q T, f s ≠ 0 := by
  constructor
  · intro hinf s hs hzero
    let z : ℝ≥0∞ := ⨅ n : ℕ, ENNReal.ofReal |f (denseTimeOn q T n)|
    have hz_top : z ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      exact iInf_le_of_le 0 le_rfl
    have hzreal : 0 < z.toReal := ENNReal.toReal_pos hinf.ne' hz_top
    let U : Set ℝ≥0 := {x | |f x| < z.toReal}
    have hUopen : IsOpen U := isOpen_Iio.preimage hf.abs
    have hsU : s ∈ U := by
      simp only [U, Set.mem_setOf_eq, hzero, abs_zero]
      exact hzreal
    obtain ⟨n, hn⟩ := exists_denseTimeOn_mem hqT hs (hUopen.mem_nhds hsU)
    have hle : z ≤ ENNReal.ofReal |f (denseTimeOn q T n)| := iInf_le _ n
    have hlt : ENNReal.ofReal |f (denseTimeOn q T n)| < z := by
      have hn' : |f (denseTimeOn q T n)| < z.toReal := hn
      rw [← ENNReal.ofReal_toReal hz_top]
      exact ENNReal.ofReal_lt_ofReal_iff hzreal |>.2 hn'
    exact (not_lt_of_ge hle) hlt
  · intro hnozero
    obtain ⟨ε, hε, hbound⟩ := isCompact_Icc.exists_forall_le'
      (hf.abs.continuousOn) (fun s hs ↦ abs_pos.mpr (hnozero s hs))
    have hεof : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    refine hεof.trans_le ?_
    apply le_iInf
    intro n
    exact ENNReal.ofReal_le_ofReal (hbound _ (denseTimeOn_mem_Icc hqT n))

/-- Last zero of a path before the deterministic horizon `T`. -/
noncomputable def lastZeroBefore (X : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sSup {s : ℝ≥0 | s = 0 ∨ (s ≤ T ∧ X s ω = 0)}

theorem lastZeroBefore_le {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (ω : Ω) :
    lastZeroBefore X T ω ≤ T := by
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · intro s hs
    exact hs.elim (fun hs0 ↦ hs0.symm ▸ zero_le) fun hs ↦ hs.1

theorem lastZeroBefore_lt_iff_exists_dense {X : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ ω, Continuous (X · ω))
    {u T : ℝ≥0} (huT : u ≤ T) (ω : Ω) :
    lastZeroBefore X T ω < u ↔
      ∃ n : ℕ, TopologicalSpace.denseSeq ℝ≥0 n < u ∧
        TopologicalSpace.denseSeq ℝ≥0 n ≤ T ∧
        0 < denseAbsInfOn X (TopologicalSpace.denseSeq ℝ≥0 n) T ω := by
  let Z : Set ℝ≥0 := {s : ℝ≥0 | s = 0 ∨ (s ≤ T ∧ X s ω = 0)}
  have hZne : Z.Nonempty := ⟨0, Or.inl rfl⟩
  have hZbdd : BddAbove Z := ⟨T, fun s hs ↦
    hs.elim (fun hs0 ↦ hs0.symm ▸ zero_le) fun hs ↦ hs.1⟩
  constructor
  · intro hlast
    obtain ⟨q, ⟨n, rfl⟩, hq⟩ :=
      (TopologicalSpace.denseRange_denseSeq ℝ≥0).exists_between hlast
    refine ⟨n, hq.2, hq.2.le.trans huT, ?_⟩
    change 0 < (⨅ k : ℕ, ENNReal.ofReal
      |X (denseTimeOn (TopologicalSpace.denseSeq ℝ≥0 n) T k) ω|)
    rw [zero_lt_denseAbsInfOn_iff (hcont ω) (hq.2.le.trans huT)]
    intro s hs hs0
    have hsZ : s ∈ Z := Or.inr ⟨hs.2, hs0⟩
    exact (not_lt_of_ge (hs.1.trans (le_csSup hZbdd hsZ))) hq.1
  · rintro ⟨n, hnu, hnT, hninf⟩
    have hnozero : ∀ s ∈ Icc (TopologicalSpace.denseSeq ℝ≥0 n) T, X s ω ≠ 0 :=
      (zero_lt_denseAbsInfOn_iff (hcont ω) hnT).mp hninf
    calc
      lastZeroBefore X T ω ≤ TopologicalSpace.denseSeq ℝ≥0 n := by
        apply csSup_le hZne
        intro s hs
        apply le_of_not_gt
        intro hns
        rcases hs with hs0 | hs
        · exact (not_lt_of_ge zero_le) (hs0 ▸ hns)
        · exact hnozero s ⟨hns.le, hs.1⟩ hs.2
      _ < u := hnu

theorem measurable_lastZeroBefore {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (hcont : ∀ ω, Continuous (X · ω))
    (T : ℝ≥0) :
    Measurable (lastZeroBefore X T) := by
  apply measurable_of_Iio
  intro u
  by_cases hTu : T < u
  · have heq : lastZeroBefore X T ⁻¹' Iio u = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact (lastZeroBefore_le T ω).trans_lt hTu
    rw [heq]
    exact MeasurableSet.univ
  · have huT : u ≤ T := le_of_not_gt hTu
    have heq : lastZeroBefore X T ⁻¹' Iio u =
        ⋃ n : ℕ, {ω | TopologicalSpace.denseSeq ℝ≥0 n < u ∧
          TopologicalSpace.denseSeq ℝ≥0 n ≤ T ∧
          0 < denseAbsInfOn X (TopologicalSpace.denseSeq ℝ≥0 n) T ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq]
      exact lastZeroBefore_lt_iff_exists_dense hcont huT ω
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : TopologicalSpace.denseSeq ℝ≥0 n < u ∧
        TopologicalSpace.denseSeq ℝ≥0 n ≤ T
    · simpa only [hn, true_and] using
        (measurableSet_lt measurable_const
          (measurable_denseAbsInfOn hX (TopologicalSpace.denseSeq ℝ≥0 n) T))
    · have hempty : {ω | TopologicalSpace.denseSeq ℝ≥0 n < u ∧
          TopologicalSpace.denseSeq ℝ≥0 n ≤ T ∧
          0 < denseAbsInfOn X (TopologicalSpace.denseSeq ℝ≥0 n) T ω} = ∅ := by
        ext ω
        constructor
        · intro h
          exact False.elim (hn ⟨h.1, h.2.1⟩)
        · intro h
          exact False.elim h
      rw [hempty]
      exact MeasurableSet.empty

theorem sin_le_sin_on_zero_pi {α x : ℝ}
    (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2)
    (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi) :
    Real.sin x ≤ Real.sin α ↔ x ≤ α ∨ Real.pi - α ≤ x := by
  have hαmem : α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  constructor
  · intro hsin
    by_cases hxhalf : x ≤ Real.pi / 2
    · left
      exact (Real.strictMonoOn_sin.le_iff_le
        ⟨by linarith [Real.pi_pos], hxhalf⟩ hαmem).mp hsin
    · right
      have hy0 : 0 ≤ Real.pi - x := sub_nonneg.mpr hxpi
      have hyhalf : Real.pi - x ≤ Real.pi / 2 := by linarith
      have hrewrite : Real.sin (Real.pi - x) = Real.sin x := by
        rw [Real.sin_pi_sub]
      have hyα : Real.pi - x ≤ α :=
        (Real.strictMonoOn_sin.le_iff_le
          ⟨by linarith [Real.pi_pos], hyhalf⟩ hαmem).mp (by rwa [hrewrite])
      linarith
  · rintro (hxα | hαx)
    · exact Real.monotoneOn_sin
        ⟨by linarith [Real.pi_pos], by linarith⟩ hαmem hxα
    · have hy0 : 0 ≤ Real.pi - x := sub_nonneg.mpr hxpi
      have hyα : Real.pi - x ≤ α := by linarith
      have hyhalf : Real.pi - x ≤ Real.pi / 2 := hyα.trans hαhalf
      have hsin := Real.monotoneOn_sin
        ⟨by linarith [Real.pi_pos], hyhalf⟩ hαmem hyα
      rwa [Real.sin_pi_sub] at hsin

theorem abs_sin_le_sin_iff {α θ : ℝ}
    (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
    |Real.sin θ| ≤ Real.sin α ↔
      θ ∈ Icc (-α) α ∨ θ ∈ Icc (-Real.pi) (-Real.pi + α) ∨
        θ ∈ Icc (Real.pi - α) Real.pi := by
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (abs_le.mpr hθ)]
  rw [sin_le_sin_on_zero_pi hα0 hαhalf (abs_nonneg θ) (abs_le.mpr hθ)]
  constructor
  · rintro (habs | habs)
    · exact Or.inl (abs_le.mp habs)
    · rcases le_abs.mp habs with hpos | hneg
      · exact Or.inr (Or.inr ⟨hpos, hθ.2⟩)
      · exact Or.inr (Or.inl ⟨hθ.1, by linarith⟩)
  · rintro (hmid | hleft | hright)
    · exact Or.inl (abs_le.mpr hmid)
    · right
      exact le_abs.mpr (Or.inr (by linarith [hleft.2]))
    · right
      exact le_abs.mpr (Or.inl hright.1)

def angularSet (α : ℝ) : Set ℝ :=
  {θ | θ ∈ Ioo (-Real.pi) Real.pi ∧ |Real.sin θ| ≤ Real.sin α}

theorem angularSet_eq {α : ℝ} (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2) :
    angularSet α =
      Ioc (-Real.pi) (-Real.pi + α) ∪ Icc (-α) α ∪ Ico (Real.pi - α) Real.pi := by
  ext θ
  simp only [angularSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo,
    Set.mem_Ioc, Set.mem_Icc, Set.mem_Ico]
  constructor
  · rintro ⟨hθ, hsin⟩
    rcases (abs_sin_le_sin_iff hα0 hαhalf ⟨hθ.1.le, hθ.2.le⟩).mp hsin with
      hmid | hleft | hright
    · exact Or.inl (Or.inr hmid)
    · exact Or.inl (Or.inl ⟨hθ.1, hleft.2⟩)
    · exact Or.inr ⟨hright.1, hθ.2⟩
  · rintro ((hleft | hmid) | hright)
    · refine ⟨⟨hleft.1, ?_⟩, ?_⟩
      · linarith [Real.pi_pos]
      · exact (abs_sin_le_sin_iff hα0 hαhalf
          ⟨hleft.1.le, by linarith [Real.pi_pos]⟩).mpr
            (Or.inr (Or.inl ⟨hleft.1.le, hleft.2⟩))
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · exact (abs_sin_le_sin_iff hα0 hαhalf
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).mpr (Or.inl hmid)
    · refine ⟨⟨?_, hright.2⟩, ?_⟩
      · linarith [Real.pi_pos]
      · exact (abs_sin_le_sin_iff hα0 hαhalf
          ⟨by linarith [Real.pi_pos], hright.2.le⟩).mpr
            (Or.inr (Or.inr ⟨hright.1, hright.2.le⟩))

theorem volume_angularSet {α : ℝ} (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2) :
    volume (angularSet α) = 4 * ENNReal.ofReal α := by
  let A : Set ℝ := Ioc (-Real.pi) (-Real.pi + α)
  let M : Set ℝ := Icc (-α) α
  let C : Set ℝ := Ico (Real.pi - α) Real.pi
  have htwice : 2 * α ≤ Real.pi := by linarith
  have hAM : AEDisjoint volume A M := by
    apply measure_mono_null (t := ({-α} : Set ℝ))
    · intro x hx
      rcases hx with ⟨hxA, hxM⟩
      simp only [A, M, Set.mem_Ioc, Set.mem_Icc] at hxA hxM
      have hxEq : x = -α := by
        apply le_antisymm
        · linarith
        · exact hxM.1
      simpa only [Set.mem_singleton_iff] using hxEq
    · exact Real.volume_singleton
  have hAMC : AEDisjoint volume (A ∪ M) C := by
    apply measure_mono_null (t := ({α} : Set ℝ))
    · intro x hx
      rcases hx with ⟨hxAM, hxC⟩
      simp only [Set.mem_union] at hxAM
      simp only [A, M, C, Set.mem_Ioc, Set.mem_Icc, Set.mem_Ico] at hxAM hxC
      have hxle : x ≤ α := hxAM.elim (fun hxA ↦ by linarith) fun hxM ↦ hxM.2
      have hxge : α ≤ x := by linarith
      simpa only [Set.mem_singleton_iff] using le_antisymm hxle hxge
    · exact Real.volume_singleton
  rw [angularSet_eq hα0 hαhalf]
  change volume ((A ∪ M) ∪ C) = _
  have hCnull : NullMeasurableSet C volume := measurableSet_Ico.nullMeasurableSet
  have hMnull : NullMeasurableSet M volume := measurableSet_Icc.nullMeasurableSet
  rw [measure_union₀ hCnull hAMC, measure_union₀ hMnull hAM]
  simp only [A, M, C, Real.volume_Ioc, Real.volume_Icc, Real.volume_Ico]
  rw [show -Real.pi + α - -Real.pi = α by ring,
    show α - -α = 2 * α by ring,
    show Real.pi - (Real.pi - α) = α by ring,
    show 2 * α = α + α by ring,
    ENNReal.ofReal_add hα0 hα0]
  norm_num
  ring

def gaussianSector (α : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ^ 2 ≤ (Real.sin α) ^ 2 * (p.1 ^ 2 + p.2 ^ 2)}

theorem measurableSet_gaussianSector (α : ℝ) :
    MeasurableSet (gaussianSector α) := by
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem mem_gaussianSector_polar_iff {α r θ : ℝ}
    (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2) (hr : 0 < r) :
    polarCoord.symm (r, θ) ∈ gaussianSector α ↔
      |Real.sin θ| ≤ Real.sin α := by
  have hsinα : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0 (hαhalf.trans (by linarith [Real.pi_pos]))
  rw [← abs_of_nonneg hsinα, ← sq_le_sq]
  simp only [gaussianSector, Set.mem_setOf_eq, polarCoord_symm_apply,
    Prod.fst, Prod.snd]
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsum : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
      _ = r ^ 2 := by rw [htrig, mul_one]
  have hleft : (r * Real.sin θ) ^ 2 = r ^ 2 * Real.sin θ ^ 2 := by ring
  constructor <;> intro h
  · have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    rw [hsum, hleft] at h
    nlinarith
  · rw [hsum, hleft]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (sq_nonneg r)

theorem gaussianPDF_polar_mul (r θ : ℝ) :
    gaussianPDF 0 1 (r * Real.cos θ) * gaussianPDF 0 1 (r * Real.sin θ) =
      gaussianPDF 0 1 r * gaussianPDF 0 1 0 := by
  simp only [gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply congrArg ENNReal.ofReal
  have hexp :
      Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2) =
        Real.exp (-r ^ 2 / 2) * Real.exp (-0 ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply congrArg Real.exp
    have hsum : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
        _ = r ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
    nlinarith
  calc
    _ = (√(2 * Real.pi))⁻¹ ^ 2 *
        (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = (√(2 * Real.pi))⁻¹ ^ 2 *
        (Real.exp (-r ^ 2 / 2) * Real.exp (-0 ^ 2 / 2)) := by rw [hexp]
    _ = _ := by ring

noncomputable def standardGaussianRadialDensity (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r * (gaussianPDF 0 1 r * gaussianPDF 0 1 0)

noncomputable def standardGaussianRadialMass : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), standardGaussianRadialDensity r

theorem measurableSet_angularSet (α : ℝ) : MeasurableSet (angularSet α) := by
  exact (measurableSet_Ioo.inter
    (measurableSet_le Real.continuous_sin.measurable.abs measurable_const))

theorem standardGaussian_sector_factor {α : ℝ}
    (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2) :
    (gaussianReal 0 1).prod (gaussianReal 0 1) (gaussianSector α) =
      standardGaussianRadialMass * volume (angularSet α) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    withDensity_apply _ (measurableSet_gaussianSector α)]
  rw [← lintegral_indicator (measurableSet_gaussianSector α)]
  change (∫⁻ a : ℝ × ℝ,
    (gaussianSector α).indicator
      (fun a ↦ gaussianPDF 0 1 a.1 * gaussianPDF 0 1 a.2) a) = _
  rw [← lintegral_comp_polarCoord_symm]
  have hpoint : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 •
          (gaussianSector α).indicator
            (fun q ↦ gaussianPDF 0 1 q.1 * gaussianPDF 0 1 q.2)
            (polarCoord.symm p) =
        standardGaussianRadialDensity p.1 *
          (angularSet α).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Ioo (-Real.pi) Real.pi := hp.2
    have hmem : polarCoord.symm p ∈ gaussianSector α ↔
        p.2 ∈ angularSet α := by
      rw [mem_gaussianSector_polar_iff hα0 hαhalf hr]
      simp only [angularSet, Set.mem_setOf_eq, hθ, true_and]
    by_cases hs : polarCoord.symm p ∈ gaussianSector α
    · have ha : p.2 ∈ angularSet α := hmem.mp hs
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem ha]
      simp only [standardGaussianRadialDensity, mul_one, smul_eq_mul,
        polarCoord_symm_apply]
      rw [gaussianPDF_polar_mul]
    · have ha : p.2 ∉ angularSet α := fun ha ↦ hs (hmem.mpr ha)
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem ha, smul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpoint]
  change (∫⁻ p in (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi),
      standardGaussianRadialDensity p.1 *
        (angularSet α).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2) = _
  change (∫⁻ p,
      (standardGaussianRadialDensity p.1 *
        (angularSet α).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2)
        ∂((volume.prod volume).restrict
          (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi))) = _
  rw [← Measure.prod_restrict, lintegral_prod_mul]
  · rw [lintegral_indicator (measurableSet_angularSet α), setLIntegral_one]
    rw [Measure.restrict_apply (measurableSet_angularSet α)]
    change standardGaussianRadialMass *
      volume (angularSet α ∩ Ioo (-Real.pi) Real.pi) =
        standardGaussianRadialMass * volume (angularSet α)
    congr 1
    apply congrArg volume
    ext θ
    simp only [angularSet, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  · have hrad : Measurable standardGaussianRadialDensity := by
      unfold standardGaussianRadialDensity
      fun_prop
    exact hrad.aemeasurable
  · exact (measurable_const.indicator (measurableSet_angularSet α)).aemeasurable

theorem gaussianSector_pi_div_two :
    gaussianSector (Real.pi / 2) = Set.univ := by
  ext p
  simp only [gaussianSector, Set.mem_setOf_eq, Real.sin_pi_div_two, one_pow,
    one_mul, Set.mem_univ, iff_true]
  nlinarith [sq_nonneg p.1]

theorem standardGaussianRadialMass_eq :
    standardGaussianRadialMass = (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
  have hfactor := standardGaussian_sector_factor
    (α := Real.pi / 2) (by positivity) le_rfl
  rw [gaussianSector_pi_div_two, measure_univ,
    volume_angularSet (by positivity) le_rfl] at hfactor
  have hangle : 4 * ENNReal.ofReal (Real.pi / 2) =
      ENNReal.ofReal (2 * Real.pi) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  rw [hangle] at hfactor
  exact ENNReal.eq_inv_of_mul_eq_one_left hfactor.symm

theorem standardGaussian_sector {α : ℝ}
    (hα0 : 0 ≤ α) (hαhalf : α ≤ Real.pi / 2) :
    (gaussianReal 0 1).prod (gaussianReal 0 1) (gaussianSector α) =
      ENNReal.ofReal ((2 / Real.pi) * α) := by
  rw [standardGaussian_sector_factor hα0 hαhalf,
    volume_angularSet hα0 hαhalf, standardGaussianRadialMass_eq,
    ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

def absoluteWedge : Set (ℝ × ℝ) :=
  {p | p.2 ^ 2 ≤ p.1 ^ 2}

theorem measurableSet_absoluteWedge : MeasurableSet absoluteWedge := by
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem independentGaussian_absoluteWedge {q L : ℝ≥0}
    (hq : q ≠ 0) (hL : L ≠ 0) :
    (gaussianReal 0 q).prod (gaussianReal 0 L) absoluteWedge =
      ENNReal.ofReal ((2 / Real.pi) *
        Real.arcsin √((q : ℝ) / ((q : ℝ) + (L : ℝ)))) := by
  let cq : ℝ := √(q : ℝ)
  let cL : ℝ := √(L : ℝ)
  let r : ℝ := (q : ℝ) / ((q : ℝ) + (L : ℝ))
  let α : ℝ := Real.arcsin √r
  have hqpos : 0 < (q : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hq)
  have hLpos : 0 < (L : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
  have hsumpos : 0 < (q : ℝ) + (L : ℝ) := add_pos hqpos hLpos
  have hr0 : 0 ≤ r := div_nonneg hqpos.le hsumpos.le
  have hr1 : r ≤ 1 := (div_le_one hsumpos).mpr (by linarith)
  have hsqrt0 : 0 ≤ √r := Real.sqrt_nonneg _
  have hsqrt1 : √r ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hr1
  have hα0 : 0 ≤ α := Real.arcsin_nonneg.mpr hsqrt0
  have hαhalf : α ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsinα : Real.sin α = √r := Real.sin_arcsin (by linarith) hsqrt1
  have hsqrt_sq : (√r) ^ 2 = r := Real.sq_sqrt hr0
  have hqmap : (gaussianReal 0 1).map (cq * ·) = gaussianReal 0 q := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      simp only [cq, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
      exact Real.sq_sqrt hqpos.le
  have hLmap : (gaussianReal 0 1).map (cL * ·) = gaussianReal 0 L := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      simp only [cL, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
      exact Real.sq_sqrt hLpos.le
  have hpre : Prod.map (cq * ·) (cL * ·) ⁻¹' absoluteWedge =
      gaussianSector α := by
    ext p
    simp only [Set.mem_preimage, absoluteWedge, gaussianSector,
      Set.mem_setOf_eq, Prod.map_apply, Prod.fst, Prod.snd]
    have hcq : cq ^ 2 = (q : ℝ) := Real.sq_sqrt hqpos.le
    have hcL : cL ^ 2 = (L : ℝ) := Real.sq_sqrt hLpos.le
    change (cL * p.2) ^ 2 ≤ (cq * p.1) ^ 2 ↔
      Real.sin α ^ 2 * (p.1 ^ 2 + p.2 ^ 2) ≥ p.2 ^ 2
    rw [hsinα, hsqrt_sq]
    have hscaleL : (cL * p.2) ^ 2 = (L : ℝ) * p.2 ^ 2 := by
      rw [mul_pow, hcL]
    have hscaleq : (cq * p.1) ^ 2 = (q : ℝ) * p.1 ^ 2 := by
      rw [mul_pow, hcq]
    rw [hscaleL, hscaleq]
    dsimp only [r]
    rw [div_mul_eq_mul_div]
    change (L : ℝ) * p.2 ^ 2 ≤ (q : ℝ) * p.1 ^ 2 ↔
      p.2 ^ 2 ≤ (q : ℝ) * (p.1 ^ 2 + p.2 ^ 2) / ((q : ℝ) + (L : ℝ))
    rw [le_div_iff₀ hsumpos]
    constructor <;> intro h
    · nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    · nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  rw [← hqmap, ← hLmap, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) measurableSet_absoluteWedge, hpre,
    standardGaussian_sector hα0 hαhalf]

theorem brownian_avoid_zero_of_pos [IsProbabilityMeasure P]
    {D : ℝ≥0 → Ω → ℝ} (hD : IsBrownianReal D P)
    (hDm : ∀ t, Measurable (D t)) (hDc : ∀ ω, Continuous (D · ω))
    (hD0 : ∀ ω, D 0 ω = 0) {a : ℝ} (ha : 0 < a) (L : ℝ≥0) :
    P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, a + D s ω ≠ 0} =
      gaussianReal 0 L {x | x ^ 2 < a ^ 2} := by
  let A : Set Ω := {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, a + D s ω ≠ 0}
  let H : Set Ω := {ω | ∃ s : ℝ≥0, s ≤ L ∧ a ≤ -D s ω}
  let U : Set Ω := {ω | a ≤ -D L ω}
  let V : Set Ω := {ω | a ≤ D L ω}
  let G : Set Ω := {ω | (D L ω) ^ 2 < a ^ 2}
  have hAH : A = Hᶜ := by
    ext ω
    simp only [A, H, Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro hA hH
      obtain ⟨s, hsL, has⟩ := hH
      have hmem : a ∈ Icc (-D 0 ω) (-D s ω) := by
        rw [hD0 ω, neg_zero]
        exact ⟨ha.le, has⟩
      obtain ⟨t, ht, hteq⟩ :=
        intermediate_value_Icc (a := (0 : ℝ≥0)) (b := s) bot_le
          (hDc ω).neg.continuousOn hmem
      apply hA t ⟨ht.1, ht.2.trans hsL⟩
      change a + D t ω = 0
      change -D t ω = a at hteq
      linarith
    · intro hnotH s hs hzero
      apply hnotH
      exact ⟨s, hs.2, by linarith⟩
  let b : ℕ → ℝ := fun n ↦
    a * (((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))
  have hbpos (n : ℕ) : 0 < b n := by
    dsimp only [b]
    positivity
  have hblt (n : ℕ) : b n < a := by
    dsimp only [b]
    have hrat : ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).2 (by linarith)
    simpa only [mul_one] using mul_lt_mul_of_pos_left hrat ha
  have hbT : Tendsto b atTop (𝓝 a) := by
    have hratio : Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((Filter.tendsto_add_atTop_iff_nat
          (f := fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) 1).2
            (tendsto_natCast_div_add_atTop (1 : ℝ)))
    simpa only [b, mul_one] using hratio.const_mul a
  have hHmeas : MeasurableSet H := by
    have hEq : H = {ω | ENNReal.ofReal a ≤ denseRunningSupremum (-D) L ω} := by
      ext ω
      constructor
      · rintro ⟨s, hsL, has⟩
        apply le_of_tendsto' (ENNReal.tendsto_ofReal hbT)
        intro n
        exact ((lt_denseRunningSupremum_iff_exists_of_continuous
          (hbpos n).le (hDc ω).neg).2
            ⟨s, hsL, (hblt n).trans_le has⟩).le
      · intro hsup
        obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
          (nonempty_Icc.2 bot_le) (hDc ω).neg.continuousOn
        refine ⟨s, hs.2, ?_⟩
        have hsup' : denseRunningSupremum (-D) L ω ≤ ENNReal.ofReal (-D s ω) := by
          unfold denseRunningSupremum
          apply iSup_le
          intro n
          apply ENNReal.ofReal_le_ofReal
          exact hmax ⟨bot_le, min_le_left _ _⟩
        have hof : ENNReal.ofReal a ≤ ENNReal.ofReal (-D s ω) :=
          le_trans hsup hsup'
        rcases ENNReal.ofReal_le_ofReal_iff'.mp hof with h | h
        · exact h
        · linarith
    rw [hEq]
    exact measurableSet_le measurable_const (measurable_denseRunningSupremum (fun t ↦ (hDm t).neg) L)
  have hUmeas : MeasurableSet U := measurableSet_le measurable_const (hDm L).neg
  have hVmeas : MeasurableSet V := measurableSet_le measurable_const (hDm L)
  have hGmeas : MeasurableSet G := measurableSet_lt (by fun_prop) measurable_const
  have hHmeasure : P H = 2 * P U := by
    exact hD.neg.reflection_principle_ge ha L
  have hUVdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro ω hU hV
    change a ≤ -D L ω at hU
    change a ≤ D L ω at hV
    linarith
  have hsymm : P U = P V := by
    have hmapD : P.map (D L) = gaussianReal 0 L := (hD.hasLaw_eval L).map_eq
    have hmapNeg : P.map (fun ω ↦ -D L ω) = gaussianReal 0 L := by
      calc
        P.map (fun ω ↦ -D L ω) = (P.map (D L)).map (fun x : ℝ ↦ -x) := by
          change P.map ((fun x : ℝ ↦ -x) ∘ D L) = _
          exact (Measure.map_map measurable_neg (hDm L)).symm
        _ = (gaussianReal 0 L).map (fun x : ℝ ↦ -x) := by rw [hmapD]
        _ = gaussianReal 0 L := by rw [gaussianReal_map_neg, neg_zero]
    calc
      P U = (P.map (fun ω ↦ -D L ω)) (Ici a) := by
        have hmneg : Measurable (fun ω ↦ -D L ω) := (hDm L).neg
        change P ((fun ω ↦ -D L ω) ⁻¹' Ici a) = _
        exact (Measure.map_apply hmneg measurableSet_Ici).symm
      _ = gaussianReal 0 L (Ici a) := by rw [hmapNeg]
      _ = (P.map (D L)) (Ici a) := by rw [hmapD]
      _ = P V := by
        change (P.map (D L)) (Ici a) = P ((D L) ⁻¹' Ici a)
        exact Measure.map_apply (hDm L) measurableSet_Ici
  have hGc : Gᶜ = U ∪ V := by
    ext ω
    simp only [G, U, V, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_union]
    constructor <;> intro h
    · have hsq : a ^ 2 ≤ (D L ω) ^ 2 := le_of_not_gt h
      rcases le_total 0 (D L ω) with hx | hx
      · exact Or.inr (by nlinarith)
      · exact Or.inl (by nlinarith)
    · rcases h with h | h <;> nlinarith
  have hGcmeasure : P Gᶜ = 2 * P U := by
    rw [hGc, measure_union hUVdisj hVmeas, ← hsymm, two_mul]
  have hHGc : P H = P Gᶜ := hHmeasure.trans hGcmeasure.symm
  calc
    P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, a + D s ω ≠ 0} = P A := rfl
    _ = P Hᶜ := by rw [hAH]
    _ = P Set.univ - P H := measure_compl hHmeas (measure_ne_top P H)
    _ = P Set.univ - P Gᶜ := by rw [hHGc]
    _ = P G := by
      simpa only [compl_compl] using
        (measure_compl hGmeas.compl (measure_ne_top P Gᶜ)).symm
    _ = gaussianReal 0 L {x | x ^ 2 < a ^ 2} := by
      rw [← (hD.hasLaw_eval L).map_eq, Measure.map_apply (hDm L)]
      · rfl
      · exact measurableSet_lt (by fun_prop) measurable_const

theorem brownian_avoid_zero [IsProbabilityMeasure P]
    {D : ℝ≥0 → Ω → ℝ} (hD : IsBrownianReal D P)
    (hDm : ∀ t, Measurable (D t)) (hDc : ∀ ω, Continuous (D · ω))
    (hD0 : ∀ ω, D 0 ω = 0) (a : ℝ) (L : ℝ≥0) :
    P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, a + D s ω ≠ 0} =
      gaussianReal 0 L {x | x ^ 2 < a ^ 2} := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hpos : 0 < -a := neg_pos.mpr ha
    have hneg := brownian_avoid_zero_of_pos hD.neg
      (fun t ↦ (hDm t).neg) (fun ω ↦ (hDc ω).neg)
      (fun ω ↦ by simp only [Pi.neg_apply, hD0 ω, neg_zero]) hpos L
    convert hneg using 1
    · apply congrArg P
      ext ω
      simp only [Set.mem_setOf_eq, Pi.neg_apply]
      constructor <;> intro h s hs
      · have := h s hs
        intro hz
        apply this
        linarith
      · have := h s hs
        intro hz
        apply this
        linarith
    · apply congrArg (gaussianReal 0 L)
      ext x
      simp only [Set.mem_setOf_eq]
      ring_nf
  · subst a
    have hleft : {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, 0 + D s ω ≠ 0} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact h 0 ⟨bot_le, bot_le⟩ (by simpa only [zero_add] using hD0 ω)
    have hright : {x : ℝ | x ^ 2 < 0 ^ 2} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      nlinarith [sq_nonneg x]
    rw [hleft, hright, measure_empty, measure_empty]
  · exact brownian_avoid_zero_of_pos hD hDm hDc hD0 ha L

theorem gaussian_sq_lt_eq_le {L : ℝ≥0} (hL : L ≠ 0) (a : ℝ) :
    gaussianReal 0 L {x | x ^ 2 < a ^ 2} =
      gaussianReal 0 L {x | x ^ 2 ≤ a ^ 2} := by
  let E : Set ℝ := {x | x ^ 2 = a ^ 2}
  have hE : gaussianReal 0 L E = 0 := by
    letI : NullSingletonClass (gaussianReal 0 L) :=
      nullSingletonClass_gaussianReal hL
    apply measure_mono_null (t := ({a} : Set ℝ) ∪ {-a})
    · intro x hx
      simp only [E, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
      exact (sq_eq_sq_iff_eq_or_eq_neg).mp hx
    · exact measure_union_null (measure_singleton a) (measure_singleton (-a))
  have hset : {x : ℝ | x ^ 2 < a ^ 2} = {x | x ^ 2 ≤ a ^ 2} \ E := by
    ext x
    simp only [E, Set.mem_setOf_eq, Set.mem_diff, not_congr]
    constructor
    · intro h
      exact ⟨h.le, h.ne⟩
    · rintro ⟨hle, hne⟩
      exact hle.lt_of_ne hne
  rw [hset, measure_sdiff_null hE]

noncomputable def futurePath (X : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) :
    Ω → (ℝ≥0 → ℝ) :=
  fun ω s ↦ X (q + s) ω - X q ω

theorem measurable_futurePath {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (q : ℝ≥0) :
    Measurable (futurePath X q) := by
  exact measurable_pi_lambda _ fun s ↦ (hX (q + s)).sub (hX q)

def pathAvoidSet (L : ℝ≥0) : Set (ℝ × (ℝ≥0 → ℝ)) :=
  {p | 0 < denseAbsInfOn (fun s p ↦ p.1 + p.2 s) 0 L p}

theorem measurableSet_pathAvoidSet (L : ℝ≥0) :
    MeasurableSet (pathAvoidSet L) := by
  exact measurableSet_lt measurable_const
    (measurable_denseAbsInfOn
      (fun s ↦ measurable_fst.add ((measurable_pi_apply s).comp measurable_snd)) 0 L)

theorem brownian_noZero_after_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {q L : ℝ≥0} (hq : q ≠ 0) (hL : L ≠ 0) :
    P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, hB.mk B (q + s) ω ≠ 0} =
      ENNReal.ofReal ((2 / Real.pi) *
        Real.arcsin √((q : ℝ) / ((q : ℝ) + (L : ℝ)))) := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let Y : Ω → (ℝ≥0 → ℝ) := futurePath X q
  let A : Set (ℝ × (ℝ≥0 → ℝ)) := pathAvoidSet L
  have hXbrown : IsBrownianReal X P := hB.isBrownianReal_mk
  have hXm : ∀ t, Measurable (X t) := hB.measurable_mk
  have hYm : Measurable Y := measurable_futurePath hXm q
  have hYbrown : IsBrownianReal (fun s ω ↦ Y ω s) P := by
    simpa only [Y, futurePath, X] using hXbrown.shift q
  have hYc : ∀ ω, Continuous (fun s ↦ Y ω s) := by
    intro ω
    have htime : Continuous (fun s : ℝ≥0 ↦ q + s) := continuous_const.add continuous_id
    have hcomp : Continuous (fun s : ℝ≥0 ↦ X (q + s) ω) :=
      (hB.continuous_mk ω).comp htime
    have hc : Continuous (fun s : ℝ≥0 ↦ X (q + s) ω - X q ω) :=
      hcomp.sub continuous_const
    exact hc
  have hY0 : ∀ ω, Y ω 0 = 0 := by
    intro ω
    simp only [Y, futurePath, add_zero, sub_self]
  let iq : Set.Iic q := ⟨q, by simp⟩
  have hi0 := hXbrown.toIsPreBrownianReal.indepFun_shift q
  have hi1 := hi0.comp measurable_id (measurable_pi_apply iq)
  have hiYX : IndepFun Y (X q) P := by
    convert hi1 using 1 <;> ext ω <;> rfl
  have hiXY : IndepFun (X q) Y P := hiYX.symm
  have hPairMeas : Measurable (fun ω ↦ (X q ω, Y ω)) := (hXm q).prodMk hYm
  have hPairMap : P.map (fun ω ↦ (X q ω, Y ω)) =
      (P.map (X q)).prod (P.map Y) :=
    hiXY.map_prod_eq_prod_map_map (hXm q).aemeasurable hYm.aemeasurable
  have hAmeas : MeasurableSet A := measurableSet_pathAvoidSet L
  have hNset :
      {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, X (q + s) ω ≠ 0} =
        (fun ω ↦ (X q ω, Y ω)) ⁻¹' A := by
    ext ω
    change (∀ s ∈ Icc (0 : ℝ≥0) L, X (q + s) ω ≠ 0) ↔
      0 < denseAbsInfOn (fun s p ↦ p.1 + p.2 s) 0 L (X q ω, Y ω)
    unfold denseAbsInfOn
    simp only [Prod.fst, Prod.snd]
    rw [zero_lt_denseAbsInfOn_iff
      (f := fun s ↦ X q ω + Y ω s) (q := (0 : ℝ≥0)) (T := L)
        (continuous_const.add (hYc ω)) bot_le]
    simp only [Y, futurePath]
    constructor <;> intro h s hs hz
    · exact h s hs (by linarith)
    · exact h s hs (by linarith)
  have hMapX : P.map (X q) = gaussianReal 0 q :=
    hXbrown.toIsPreBrownianReal.hasLaw_eval q |>.map_eq
  have hFiber (a : ℝ) :
      (P.map Y) (Prod.mk a ⁻¹' A) =
        gaussianReal 0 L {x | x ^ 2 ≤ a ^ 2} := by
    have hFiberMeas : MeasurableSet (Prod.mk a ⁻¹' A) :=
      hAmeas.preimage (measurable_const.prodMk measurable_id)
    calc
      (P.map Y) (Prod.mk a ⁻¹' A) = P (Y ⁻¹' (Prod.mk a ⁻¹' A)) :=
        Measure.map_apply hYm hFiberMeas
      _ = P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, a + Y ω s ≠ 0} := by
        apply congrArg P
        ext ω
        change (0 < denseAbsInfOn (fun s p ↦ p.1 + p.2 s) 0 L (a, Y ω)) ↔ _
        unfold denseAbsInfOn
        simp only [Prod.fst, Prod.snd, Set.mem_setOf_eq]
        rw [zero_lt_denseAbsInfOn_iff
          (f := fun s ↦ a + Y ω s) (q := (0 : ℝ≥0)) (T := L)
            (continuous_const.add (hYc ω)) bot_le]
      _ = gaussianReal 0 L {x | x ^ 2 < a ^ 2} :=
        brownian_avoid_zero hYbrown (fun t ↦ (measurable_pi_apply t).comp hYm)
          hYc hY0 a L
      _ = gaussianReal 0 L {x | x ^ 2 ≤ a ^ 2} :=
        gaussian_sq_lt_eq_le hL a
  calc
    P {ω | ∀ s ∈ Icc (0 : ℝ≥0) L, hB.mk B (q + s) ω ≠ 0} =
        P ((fun ω ↦ (X q ω, Y ω)) ⁻¹' A) := by
          apply congrArg P
          exact hNset
    _ = P.map (fun ω ↦ (X q ω, Y ω)) A :=
      (Measure.map_apply hPairMeas hAmeas).symm
    _ = (P.map (X q)).prod (P.map Y) A := by rw [hPairMap]
    _ = (gaussianReal 0 q).prod (P.map Y) A := by rw [hMapX]
    _ = ∫⁻ a, (P.map Y) (Prod.mk a ⁻¹' A) ∂gaussianReal 0 q :=
      Measure.prod_apply hAmeas
    _ = ∫⁻ a, gaussianReal 0 L {x | x ^ 2 ≤ a ^ 2} ∂gaussianReal 0 q := by
      apply lintegral_congr
      exact hFiber
    _ = (gaussianReal 0 q).prod (gaussianReal 0 L) absoluteWedge := by
      rw [Measure.prod_apply measurableSet_absoluteWedge]
      rfl
    _ = ENNReal.ofReal ((2 / Real.pi) *
        Real.arcsin √((q : ℝ) / ((q : ℝ) + (L : ℝ)))) :=
      independentGaussian_absoluteWedge hq hL

theorem lastZeroBefore_cdf_mk_interior [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {q T : ℝ≥0} (hq : q ≠ 0) (hqT : q < T) :
    P {ω | lastZeroBefore (hB.mk B) T ω ≤ q} =
      ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) := by
  let X : ℝ≥0 → Ω → ℝ := hB.mk B
  let N : Set Ω := {ω | ∀ s ∈ Icc q T, X s ω ≠ 0}
  let Ns : Set Ω := {ω | ∀ s ∈ Icc (0 : ℝ≥0) (T - q), X (q + s) ω ≠ 0}
  have hqle : q ≤ T := hqT.le
  have hNshift : N = Ns := by
    ext ω
    constructor
    · intro hN s hs
      exact hN (q + s) ⟨le_add_right le_rfl, by
        calc
          q + s = s + q := add_comm _ _
          _ ≤ (T - q) + q := add_le_add_left hs.2 q
          _ = T := tsub_add_cancel_of_le hqle⟩
    · intro hN t ht
      let s : ℝ≥0 := t - q
      have hs0 : 0 ≤ s := bot_le
      have hsT : s ≤ T - q := tsub_le_tsub_right ht.2 q
      have hsum : q + s = t := by
        dsimp only [s]
        simpa only [add_comm] using tsub_add_cancel_of_le ht.1
      simpa only [hsum] using hN s ⟨hs0, hsT⟩
  have hqzero : P {ω | X q ω = 0} = 0 := by
    have hm := hB.isBrownianReal_mk.toIsPreBrownianReal.hasLaw_eval q
    have heq := hm.measure_eq (p := fun x : ℝ ↦ x = 0) (measurableSet_singleton 0)
    rw [heq]
    letI : NullSingletonClass (gaussianReal 0 q) :=
      nullSingletonClass_gaussianReal hq
    exact measure_singleton 0
  have hae : ∀ᵐ ω ∂P, X q ω ≠ 0 := by
    rw [ae_iff]
    have heq : {ω | ¬X q ω ≠ 0} = {ω | X q ω = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, not_ne_iff]
    rw [heq, hqzero]
  have hLastN (ω : Ω) (hω : X q ω ≠ 0) :
      lastZeroBefore X T ω ≤ q ↔ ω ∈ N := by
    let Z : Set ℝ≥0 := {s | s = 0 ∨ (s ≤ T ∧ X s ω = 0)}
    have hZne : Z.Nonempty := ⟨0, Or.inl rfl⟩
    have hZbdd : BddAbove Z := ⟨T, fun s hs ↦
      hs.elim (fun hs0 ↦ hs0.symm ▸ bot_le) fun hs ↦ hs.1⟩
    constructor
    · intro hlast s hs hzero
      have hsZ : s ∈ Z := Or.inr ⟨hs.2, hzero⟩
      have hsq : s ≤ q := (le_csSup hZbdd hsZ).trans hlast
      have hse : s = q := le_antisymm hsq hs.1
      exact hω (by rwa [hse] at hzero)
    · intro hN
      apply csSup_le hZne
      intro s hs
      rcases hs with hs0 | hs
      · exact hs0.symm ▸ bot_le
      · apply le_of_not_gt
        intro hqs
        exact hN s ⟨hqs.le, hs.1⟩ hs.2
  calc
    P {ω | lastZeroBefore (hB.mk B) T ω ≤ q} = P N := by
      apply measure_congr
      filter_upwards [hae] with ω hω
      exact propext (hLastN ω hω)
    _ = P Ns := by rw [hNshift]
    _ = ENNReal.ofReal ((2 / Real.pi) *
        Real.arcsin √((q : ℝ) / ((q : ℝ) + ((T - q : ℝ≥0) : ℝ)))) :=
      brownian_noZero_after_mk hB hq (ne_of_gt (tsub_pos_iff_lt.mpr hqT))
    _ = ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) := by
      rw [NNReal.coe_sub hqle]
      congr 4
      ring

theorem lastZeroBefore_cdf_mk_zero [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {T : ℝ≥0} (hT : T ≠ 0) :
    P {ω | lastZeroBefore (hB.mk B) T ω ≤ 0} = 0 := by
  let r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 2)
  let q : ℕ → ℝ≥0 := fun n ↦ ⟨(T : ℝ) * r n, mul_nonneg (NNReal.coe_nonneg T) (by
    dsimp only [r]
    positivity)⟩
  let F : ℕ → ℝ≥0∞ := fun n ↦
    ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √(r n))
  have hTpos : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp only [r]
    positivity
  have hrlt (n : ℕ) : r n < 1 := by
    dsimp only [r]
    rw [div_lt_one (by positivity)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hqpos (n : ℕ) : q n ≠ 0 := by
    apply pos_iff_ne_zero.mp
    apply NNReal.coe_pos.mp
    change 0 < (T : ℝ) * r n
    exact mul_pos hTpos (hrpos n)
  have hqT (n : ℕ) : q n < T := by
    apply NNReal.coe_lt_coe.mp
    change (T : ℝ) * r n < (T : ℝ)
    simpa only [mul_one] using mul_lt_mul_of_pos_left (hrlt n) hTpos
  have hformula (n : ℕ) :
      P {ω | lastZeroBefore (hB.mk B) T ω ≤ q n} = F n := by
    rw [lastZeroBefore_cdf_mk_interior hB (hqpos n) (hqT n)]
    dsimp only [F]
    rw [show ((q n : ℝ≥0) : ℝ) = (T : ℝ) * r n by rfl]
    congr 4
    field_simp [hTpos.ne']
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := ((Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) 1).2
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    convert h using 1
    funext n
    dsimp only [r]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  have hcont : ContinuousAt
      (fun x : ℝ ↦ (2 / Real.pi) * Real.arcsin √x) 0 := by
    fun_prop
  have hF : Tendsto F atTop (𝓝 0) := by
    have hreal := hcont.tendsto.comp hr
    have hof := ENNReal.tendsto_ofReal hreal
    simpa only [F, Function.comp_apply, Real.sqrt_zero, Real.arcsin_zero, mul_zero,
      ENNReal.ofReal_zero] using hof
  have hbound (n : ℕ) :
      P {ω | lastZeroBefore (hB.mk B) T ω ≤ 0} ≤ F n := by
    calc
      P {ω | lastZeroBefore (hB.mk B) T ω ≤ 0} ≤
          P {ω | lastZeroBefore (hB.mk B) T ω ≤ q n} := by
        apply measure_mono
        intro ω hω
        change lastZeroBefore (hB.mk B) T ω ≤ 0 at hω
        change lastZeroBefore (hB.mk B) T ω ≤ q n
        exact hω.trans bot_le
      _ = F n := hformula n
  exact bot_unique (ge_of_tendsto' hF hbound)

theorem lastZeroBefore_cdf_mk [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) {q T : ℝ≥0} (hT : T ≠ 0) (hqT : q ≤ T) :
    P {ω | lastZeroBefore (hB.mk B) T ω ≤ q} =
      ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) := by
  rcases eq_or_ne q 0 with rfl | hq
  · rw [lastZeroBefore_cdf_mk_zero hB hT]
    simp only [NNReal.coe_zero, zero_div, Real.sqrt_zero, Real.arcsin_zero, mul_zero,
      ENNReal.ofReal_zero]
  · rcases eq_or_ne q T with hqeq | hqne
    · have hset : {ω | lastZeroBefore (hB.mk B) T ω ≤ T} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ω
        exact lastZeroBefore_le T ω
      rw [hqeq, hset, measure_univ]
      have hTreal : (T : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hT
      rw [div_self hTreal, Real.sqrt_one, Real.arcsin_one]
      rw [show (2 / Real.pi) * (Real.pi / 2) = 1 by field_simp [Real.pi_ne_zero]]
      exact ENNReal.ofReal_one.symm
    · exact lastZeroBefore_cdf_mk_interior hB hq (lt_of_le_of_ne hqT hqne)

theorem IsBrownianReal.lastZeroBefore_ae_eq_mk
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    lastZeroBefore B T =ᵐ[P]
      lastZeroBefore (hB.toIsPreBrownianReal.mk B) T := by
  filter_upwards [hB.mk_ae_forall_eq] with ω hω
  unfold lastZeroBefore
  apply congrArg sSup
  ext s
  simp only [Set.mem_setOf_eq]
  rw [hω s]

theorem IsBrownianReal.aemeasurable_lastZeroBefore
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEMeasurable (lastZeroBefore B T) P := by
  have hm : Measurable
      (lastZeroBefore (hB.toIsPreBrownianReal.mk B) T) :=
    measurable_lastZeroBefore hB.toIsPreBrownianReal.measurable_mk
      hB.toIsPreBrownianReal.continuous_mk T
  exact hm.aemeasurable.congr (hB.lastZeroBefore_ae_eq_mk T).symm

theorem IsBrownianReal.lastZeroBefore_cdf [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {q T : ℝ≥0} (hT : T ≠ 0) (hqT : q ≤ T) :
    P {ω | lastZeroBefore B T ω ≤ q} =
      ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) := by
  calc
    P {ω | lastZeroBefore B T ω ≤ q} =
        P {ω | lastZeroBefore (hB.toIsPreBrownianReal.mk B) T ω ≤ q} := by
      apply measure_congr
      filter_upwards [hB.lastZeroBefore_ae_eq_mk T] with ω hω
      apply propext
      change (lastZeroBefore B T ω ≤ q) ↔
        (lastZeroBefore (hB.toIsPreBrownianReal.mk B) T ω ≤ q)
      rw [hω]
    _ = ENNReal.ofReal ((2 / Real.pi) * Real.arcsin √((q : ℝ) / (T : ℝ))) :=
      lastZeroBefore_cdf_mk hB.toIsPreBrownianReal hT hqT

end ProbabilityTheory

