/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.ForMathlib.MeasureTheory.Measure.VagueConvergence
public import StochLean.Probability.MeasureConvergence.Empirical
public import StochLean.Probability.MeasureConvergence.Mapping
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Uniform

/-!
# Semantic regressions for convergence of measures

These are executable mathematical boundary tests for the fourth design handoff.  They protect the
distinction between weak and vague convergence, weak convergence and convergence of masses of
arbitrary Borel sets, continuous and merely measurable mappings, and convergence in probability
and in distribution.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace ProbabilityTheory

noncomputable section

/-- Probability mass escaping to infinity. -/
def escapingDirac (n : ℕ) : ProbabilityMeasure ℝ :=
  MeasureTheory.diracProba (n : ℝ)

/-- Escaping probability mass has the zero measure as a vague limit. -/
theorem escapingDirac_tendstoVaguely_zero :
    TendstoVaguely (fun n ↦ (escapingDirac n : Measure ℝ)) atTop 0 := by
  apply tendstoVaguely_dirac_zero_of_tendsto_cocompact
  simpa [Metric.cobounded_eq_cocompact] using
    (tendsto_natCast_atTop_cobounded (α := ℝ))

/-- The escaping Dirac family is not tight. -/
theorem escapingDirac_not_isTightMeasureSet :
    ¬ IsTightMeasureSet (range fun n ↦ (escapingDirac n : Measure ℝ)) := by
  intro htight
  obtain ⟨K, hK, hmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight (1 / 2) (by norm_num)
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hnK : (n : ℝ) ∉ K := by
    intro hnK
    have hnr := hr hnK
    change dist (n : ℝ) 0 ≤ r at hnr
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnr' : (n : ℝ) ≤ r := by
      simpa [Real.dist_eq, abs_of_nonneg hnnonneg] using hnr
    exact (not_le_of_gt hn) hnr'
  have hle := hmass (escapingDirac n : Measure ℝ) ⟨n, rfl⟩
  have hone : (escapingDirac n : Measure ℝ) (Kᶜ) = 1 :=
    MeasureTheory.diracProba_toMeasure_apply_of_mem (by simpa using hnK)
  rw [hone] at hle
  norm_num at hle

/-- Hence escaping Dirac masses cannot converge weakly to any probability measure. -/
theorem escapingDirac_not_tendsto_probabilityMeasure (ν : ProbabilityMeasure ℝ) :
    ¬ Tendsto escapingDirac atTop (nhds ν) := by
  intro h
  have hcompactInsert : IsCompact (insert ν (range escapingDirac)) :=
    h.isCompact_insert_range
  have hcompactClosure : IsCompact (closure (range escapingDirac)) :=
    hcompactInsert.of_isClosed_subset isClosed_closure <|
      closure_minimal (by simp) hcompactInsert.isClosed
  have htight := isTightMeasureSet_of_isCompact_closure hcompactClosure
  apply escapingDirac_not_isTightMeasureSet
  have hsets :
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ range escapingDirac} =
        range (fun n ↦ (escapingDirac n : Measure ℝ)) := by
    ext m
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨escapingDirac n, ⟨n, rfl⟩, rfl⟩
  rw [hsets] at htight
  exact htight

/-- Dirac masses approaching zero give the basic weak-convergence example. -/
def shrinkingDirac (n : ℕ) : ProbabilityMeasure ℝ :=
  MeasureTheory.diracProba (1 / (n + 1 : ℝ))

theorem shrinkingDirac_tendsto_dirac_zero :
    Tendsto shrinkingDirac atTop (nhds (MeasureTheory.diracProba (0 : ℝ))) := by
  change Tendsto (fun n : ℕ ↦ MeasureTheory.diracProba (1 / (n + 1 : ℝ))) atTop
    (nhds (MeasureTheory.diracProba (0 : ℝ)))
  exact MeasureTheory.continuous_diracProba.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Weak convergence does not imply convergence on a Borel set whose frontier has positive limit
mass: every approximating measure gives `{0}` mass zero, while the limit gives it mass one. -/
theorem shrinkingDirac_singleton_mass_boundary :
    (∀ n, (shrinkingDirac n : Measure ℝ) ({0} : Set ℝ) = 0) ∧
      (MeasureTheory.diracProba (0 : ℝ) : Measure ℝ) ({0} : Set ℝ) = 1 := by
  constructor
  · intro n
    change Measure.dirac (1 / (n + 1 : ℝ)) ({0} : Set ℝ) = 0
    rw [dirac_eq_zero_iff_not_mem (measurableSet_singleton 0)]
    simp only [mem_singleton_iff, div_eq_zero_iff, one_ne_zero, false_or]
    positivity
  · simp

theorem shrinkingDirac_singleton_mass_not_tendsto :
    ¬ Tendsto (fun n ↦ (shrinkingDirac n : Measure ℝ) ({0} : Set ℝ)) atTop
      (nhds ((MeasureTheory.diracProba (0 : ℝ) : Measure ℝ) ({0} : Set ℝ))) := by
  intro h
  rw [shrinkingDirac_singleton_mass_boundary.2] at h
  have hzero : Tendsto
      (fun n ↦ (shrinkingDirac n : Measure ℝ) ({0} : Set ℝ)) atTop (nhds 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (nhds 0)) using 1
    funext n
    exact shrinkingDirac_singleton_mass_boundary.1 n
  exact one_ne_zero (tendsto_nhds_unique h hzero)

/-- A measurable map discontinuous at the limiting atom. -/
def zeroDetector (x : ℝ) : Bool := decide (x = 0)

theorem zeroDetector_measurable : Measurable zeroDetector :=
  measurable_to_bool <| by
    convert measurableSet_singleton (0 : ℝ) using 1
    ext x
    simp [zeroDetector]

theorem zeroDetector_not_continuousAt_zero : ¬ ContinuousAt zeroDetector 0 := by
  intro h
  have ht : Tendsto (fun n : ℕ ↦ zeroDetector (1 / (n + 1 : ℝ))) atTop
      (nhds (zeroDetector 0)) := h.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hseq : (fun n : ℕ ↦ zeroDetector (1 / (n + 1 : ℝ))) =
      (fun _ : ℕ ↦ false) := by
    funext n
    simp only [zeroDetector, decide_eq_false_iff_not, div_eq_zero_iff, one_ne_zero, false_or]
    positivity
  rw [hseq] at ht
  have hf : Tendsto (fun _ : ℕ ↦ false) atTop (nhds false) := tendsto_const_nhds
  have heq : false = true := tendsto_nhds_unique hf (by simpa [zeroDetector] using ht)
  simp at heq

/-- The continuous-mapping conclusion fails for `zeroDetector`: all image laws are `δ_false`,
whereas the image of the weak limit is `δ_true`. -/
theorem zeroDetector_mapped_shrinkingDirac_not_tendsto :
    ¬ Tendsto
      (fun n ↦ (shrinkingDirac n).map zeroDetector_measurable.aemeasurable)
      atTop
      (nhds ((MeasureTheory.diracProba (0 : ℝ)).map
        zeroDetector_measurable.aemeasurable)) := by
  intro h
  have hsource (n : ℕ) :
      (shrinkingDirac n).map zeroDetector_measurable.aemeasurable =
        MeasureTheory.diracProba false := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.dirac (1 / (n + 1 : ℝ))).map zeroDetector = Measure.dirac false
    rw [Measure.map_dirac' zeroDetector_measurable]
    congr
    simp only [zeroDetector, decide_eq_false_iff_not, div_eq_zero_iff, one_ne_zero, false_or]
    positivity
  have htarget :
      (MeasureTheory.diracProba (0 : ℝ)).map zeroDetector_measurable.aemeasurable =
        MeasureTheory.diracProba true := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.dirac (0 : ℝ)).map zeroDetector = Measure.dirac true
    rw [Measure.map_dirac' zeroDetector_measurable]
    congr
    simp [zeroDetector]
  rw [show (fun n ↦ (shrinkingDirac n).map zeroDetector_measurable.aemeasurable) =
      (fun _ : ℕ ↦ MeasureTheory.diracProba false) by funext n; exact hsource n,
    htarget] at h
  have hfalse : Tendsto
      (fun _ : ℕ ↦ MeasureTheory.diracProba false) atTop
      (nhds (MeasureTheory.diracProba false)) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hfalse h
  exact Bool.false_ne_true (MeasureTheory.injective_diracProba heq)

/-- The fair Boolean law, used to separate convergence in law from convergence in probability. -/
def uniformBoolLawMeasure : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure uniformBoolLawMeasure := by
  dsimp only [uniformBoolLawMeasure]
  infer_instance

private theorem identDistrib_bool_not :
    IdentDistrib (fun x : Bool ↦ !x) id uniformBoolLawMeasure uniformBoolLawMeasure := by
  refine ⟨(measurable_of_finite _).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [uniformBoolLawMeasure,
    PMF.toMeasure_map (f := fun x : Bool ↦ !x) (PMF.uniformOfFintype Bool)
      (measurable_of_finite _),
    PMF.toMeasure_map (f := id) (PMF.uniformOfFintype Bool) measurable_id]
  congr 1
  ext b
  cases b <;> simp [PMF.map_apply]

def boolRademacher (x : Bool) : ℝ := if x then 1 else -1

theorem boolFlip_tendstoInDistribution :
    TendstoInDistribution (fun _ : ℕ ↦ fun x : Bool ↦ boolRademacher (!x)) atTop
      boolRademacher
      (fun _ ↦ uniformBoolLawMeasure) uniformBoolLawMeasure := by
  apply tendstoInDistribution_of_identDistrib 0
  · intro j
    exact IdentDistrib.refl <| (measurable_of_finite _).aemeasurable
  · exact identDistrib_bool_not.comp (u := boolRademacher) (measurable_of_finite _)

theorem boolFlip_not_tendstoInMeasure :
    ¬ TendstoInMeasure uniformBoolLawMeasure
      (fun _ : ℕ ↦ fun x : Bool ↦ boolRademacher (!x)) atTop boolRademacher := by
  intro h
  have ht := h (ENNReal.ofReal (1 / 2 : ℝ)) (ENNReal.ofReal_pos.mpr (by norm_num))
  have hset (n : ℕ) :
      {x | ENNReal.ofReal (1 / 2 : ℝ) ≤
        edist (boolRademacher (!x)) (boolRademacher x)} = univ := by
    ext x
    cases x <;> norm_num [boolRademacher, edist_dist, Real.dist_eq]
  have ht' : Tendsto (fun _ : ℕ ↦ uniformBoolLawMeasure univ) atTop (nhds 0) := by
    convert ht using 1
    funext n
    rw [hset n]
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ≥0∞)) atTop (nhds 0) := by
    simpa only [measure_univ] using ht'
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hone)

/- The canonical implication and Slutsky/continuous-mapping chain remain directly reusable. -/
example {Ω E : Type*} {_mΩ : MeasurableSpace Ω} {_mE : MeasurableSpace E}
    [PseudoEMetricSpace E] [BorelSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E} {Z : Ω → E}
    (h : TendstoInMeasure P X atTop Z) (hX : ∀ n, AEMeasurable (X n) P) :
    TendstoInDistribution X atTop Z (fun _ ↦ P) P :=
  h.tendstoInDistribution hX

/- The canonical continuous-mapping theorem for random variables remains the ordinary Mathlib
theorem, distinct from the a.e.-continuous measure-level gap filled below. -/
example {ι Ω E F : Type*} {_mΩ : MeasurableSpace Ω}
    {_mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]
    {_mF : MeasurableSpace F} [TopologicalSpace F] [BorelSpace F]
    {P : Measure Ω} [IsProbabilityMeasure P] {l : Filter ι}
    {X : ι → Ω → E} {Z : Ω → E} {g : E → F}
    (h : TendstoInDistribution X l Z (fun _ ↦ P) P) (hg : Continuous g) :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) (fun _ ↦ P) P :=
  h.continuous_comp hg

/- Slutsky's addition theorem is reused with its genuine convergence-in-probability hypothesis. -/
example {ι Ω E : Type*} {_mΩ : MeasurableSpace Ω} {_mE : MeasurableSpace E}
    [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {l : Filter ι} [l.IsCountablyGenerated]
    {X Y : ι → Ω → E} {Z : Ω → E} {c : E}
    (hX : TendstoInDistribution X l Z (fun _ ↦ P) P)
    (hY : TendstoInMeasure P Y l (fun _ ↦ c))
    (hYm : ∀ i, AEMeasurable (Y i) P) :
    TendstoInDistribution (fun n ↦ X n + Y n) l (fun ω ↦ Z ω + c)
      (fun _ ↦ P) P :=
  hX.add_of_tendstoInMeasure_const hY hYm

/- Portmanteau's null-frontier result is the precise positive boundary for set masses. -/
example {ι X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X]
    {l : Filter ι} {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (h : Tendsto μ l (nhds ν)) {s : Set X} (hs : ν (frontier s) = 0) :
    Tendsto (fun i ↦ μ i s) l (nhds (ν s)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h hs

/- The a.e.-continuous mapping bridge is genuinely weaker than global continuity. -/
example {ι X Y : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [HasOuterApproxClosed X]
    [OpensMeasurableSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
    [BorelSpace Y] {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} {f : X → Y}
    (hμ : Tendsto μ l (nhds ν)) (hf : Measurable f)
    (hcont : (ν : Measure X) {x | ¬ ContinuousAt f x} = 0) :
    Tendsto (fun i ↦ (μ i).map hf.aemeasurable) l
      (nhds (ν.map hf.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous hμ hf hcont

/- The empirical weak limit consumes the empirical measure and CDF APIs from milestone three. -/
example {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (hindep : Pairwise (fun i j ↦ IndepFun (X i) (X j) P))
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empiricalProbabilityMeasurePM X n ω) atTop
      (nhds (lawProbabilityMeasure P (X 0) (hX 0))) :=
  tendsto_empiricalProbabilityMeasurePM_ae P X hX hindep hident

end

end ProbabilityTheory
