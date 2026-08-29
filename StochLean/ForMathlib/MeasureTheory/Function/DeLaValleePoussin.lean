/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.UnifTight
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# A de la Vallée-Poussin envelope criterion

This file supplies the generic sufficient direction of the de la Vallée-Poussin criterion. If a
family has uniformly bounded integrals through a nonnegative superlinear envelope, its `L¹` tails
are uniformly small. The result is exposed both for Mathlib's measure-theoretic
`UnifIntegrable` and, on finite measure spaces, its probability-style `UniformIntegrable`.

Convexity and monotonicity of the envelope are useful when constructing an envelope from uniform
integrability, but are not needed for this sufficient direction.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

noncomputable section

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
variable [NormedAddCommGroup E]

/-- Klenke's sigma-finite uniform-integrability notion, expressed through Mathlib's canonical
decomposition into uniform absolute continuity and uniform tightness. On finite measure spaces the
tightness conjunct is automatic, while on infinite spaces it records the spatial envelope control
that ordinary `UniformIntegrable` does not provide. -/
def UniformIntegrableByEnvelope (f : ι → α → E) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  UniformIntegrable f p μ ∧ UnifTight f p μ

namespace UniformIntegrableByEnvelope

variable {f g : ι → α → E} {p : ℝ≥0∞}

theorem uniformIntegrable (hf : UniformIntegrableByEnvelope f p μ) :
    UniformIntegrable f p μ := hf.1

theorem unifIntegrable (hf : UniformIntegrableByEnvelope f p μ) :
    UnifIntegrable f p μ := hf.1.unifIntegrable

theorem unifTight (hf : UniformIntegrableByEnvelope f p μ) :
    UnifTight f p μ := hf.2

theorem aestronglyMeasurable (hf : UniformIntegrableByEnvelope f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ := hf.1.aestronglyMeasurable i

theorem memLp (hf : UniformIntegrableByEnvelope f p μ) (i : ι) :
    MemLp (f i) p μ := hf.1.memLp i

theorem ae_eq (hf : UniformIntegrableByEnvelope f p μ)
    (hfg : ∀ i, f i =ᵐ[μ] g i) : UniformIntegrableByEnvelope g p μ :=
  ⟨hf.1.ae_eq hfg, hf.2.aeeq hfg⟩

/-- Reindexing preserves envelope uniform integrability. -/
theorem comp {J : Type*} (hf : UniformIntegrableByEnvelope f p μ) (k : J → ι) :
    UniformIntegrableByEnvelope (fun j ↦ f (k j)) p μ := by
  obtain ⟨C, hC⟩ := hf.1.2.2
  refine ⟨⟨fun j ↦ hf.aestronglyMeasurable (k j), ?_, ⟨C, fun j ↦ hC (k j)⟩⟩, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hf.1.2.1 hε
    exact ⟨δ, hδ, fun j s hs hμs ↦ hsmall (k j) s hs hμs⟩
  · intro ε hε
    obtain ⟨s, hμs, hout⟩ := hf.2 hε
    exact ⟨s, hμs, fun j ↦ hout (k j)⟩

/-- Envelope uniform integrability is closed under negation. -/
theorem neg (hf : UniformIntegrableByEnvelope f p μ) :
    UniformIntegrableByEnvelope (-f) p μ := by
  refine ⟨⟨fun i ↦ (hf.aestronglyMeasurable i).neg, hf.1.2.1.neg, ?_⟩, hf.2.neg⟩
  obtain ⟨C, hC⟩ := hf.1.2.2
  exact ⟨C, fun i ↦ by simpa using hC i⟩

/-- Envelope uniform integrability is closed under addition. -/
theorem add (hf : UniformIntegrableByEnvelope f p μ)
    (hg : UniformIntegrableByEnvelope g p μ) (hp : 1 ≤ p) :
    UniformIntegrableByEnvelope (f + g) p μ := by
  obtain ⟨Cf, hCf⟩ := hf.1.2.2
  obtain ⟨Cg, hCg⟩ := hg.1.2.2
  refine ⟨⟨fun i ↦ (hf.aestronglyMeasurable i).add (hg.aestronglyMeasurable i),
      hf.1.2.1.add hg.1.2.1 hp (fun i ↦ hf.aestronglyMeasurable i)
        (fun i ↦ hg.aestronglyMeasurable i), ⟨Cf + Cg, fun i ↦ ?_⟩⟩,
    hf.2.add hg.2 (fun i ↦ hf.aestronglyMeasurable i)
      (fun i ↦ hg.aestronglyMeasurable i)⟩
  simpa only [Pi.add_apply, ENNReal.coe_add] using
    (eLpNorm_add_le (hf.aestronglyMeasurable i) (hg.aestronglyMeasurable i) hp).trans
      (add_le_add (hCf i) (hCg i))

/-- Envelope uniform integrability is closed under subtraction. -/
theorem sub (hf : UniformIntegrableByEnvelope f p μ)
    (hg : UniformIntegrableByEnvelope g p μ) (hp : 1 ≤ p) :
    UniformIntegrableByEnvelope (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp

/-- A dominated measurable family inherits envelope uniform integrability. -/
theorem mono_enorm {F : Type*} [NormedAddCommGroup F] {g : ι → α → F}
    (hf : UniformIntegrableByEnvelope f p μ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    (hgf : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ₑ ≤ ‖f i x‖ₑ) :
    UniformIntegrableByEnvelope g p μ := by
  obtain ⟨C, hC⟩ := hf.1.2.2
  refine ⟨⟨hg, ?_, ⟨C, fun i ↦ (eLpNorm_mono_enorm_ae (hgf i)).trans (hC i)⟩⟩, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hfδ⟩ := hf.1.2.1 hε
    refine ⟨δ, hδ, fun i s hs hμs ↦ ?_⟩
    apply (eLpNorm_mono_enorm_ae ?_).trans (hfδ i s hs hμs)
    filter_upwards [hgf i] with x hx
    by_cases hxs : x ∈ s <;> simp [hxs, hx]
  · intro ε hε
    obtain ⟨s, hμs, hfε⟩ := hf.2 hε
    refine ⟨s, hμs, fun i ↦ ?_⟩
    apply (eLpNorm_mono_enorm_ae ?_).trans (hfε i)
    filter_upwards [hgf i] with x hx
    by_cases hxs : x ∈ sᶜ <;> simp [hxs, hx]

/-- Taking pointwise norms preserves envelope uniform integrability. -/
theorem norm (hf : UniformIntegrableByEnvelope f p μ) :
    UniformIntegrableByEnvelope (fun i x ↦ ‖f i x‖) p μ :=
  hf.mono_enorm (fun i ↦ (hf.aestronglyMeasurable i).norm) (fun _ ↦ by simp)

/-- Klenke's domination closure with a possibly different dominating family member for each
target function. -/
theorem dominated {J F : Type*} [NormedAddCommGroup F] {g : J → α → F}
    (hf : UniformIntegrableByEnvelope f p μ) (k : J → ι)
    (hg : ∀ j, AEStronglyMeasurable (g j) μ)
    (hgf : ∀ j, ∀ᵐ x ∂μ, ‖g j x‖ₑ ≤ ‖f (k j) x‖ₑ) :
    UniformIntegrableByEnvelope g p μ :=
  (hf.comp k).mono_enorm hg hgf

/-- A finite family of `Lᵖ` functions is envelope uniformly integrable. -/
theorem finite [Finite ι] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ i, MemLp (f i) p μ) : UniformIntegrableByEnvelope f p μ :=
  ⟨uniformIntegrable_finite hp hp' hf, unifTight_finite hp' hf⟩

end UniformIntegrableByEnvelope

/-- On a finite measure space, Mathlib's probability-style uniform integrability already includes
all of Klenke's envelope uniform integrability. -/
theorem uniformIntegrableByEnvelope_iff_uniformIntegrable [IsFiniteMeasure μ]
    {f : ι → α → E} {p : ℝ≥0∞} :
    UniformIntegrableByEnvelope f p μ ↔ UniformIntegrable f p μ := by
  constructor
  · exact UniformIntegrableByEnvelope.uniformIntegrable
  · intro hf
    refine ⟨hf, ?_⟩
    intro ε hε
    refine ⟨Set.univ, measure_ne_top _ _, fun i ↦ ?_⟩
    simp

/-- A nonnegative envelope is superlinear if `Φ(t) / t` tends to infinity. -/
def SuperlinearEnvelope (Φ : ℝ≥0 → ℝ≥0) : Prop :=
  Tendsto (fun t ↦ Φ t / t) atTop atTop

namespace SuperlinearEnvelope

/-- A step envelope generated by thresholds: each threshold already crossed contributes one copy
of the current argument. -/
def step (a : ℕ → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  ∑' n, if a n ≤ t then t else 0

/-- Linear escape of the thresholds makes the defining step-envelope sum pointwise finite. -/
theorem summable_step (a : ℕ → ℝ≥0) (ha : ∀ n : ℕ, (n : ℝ≥0) ≤ a n) (t : ℝ≥0) :
    Summable (fun n ↦ if a n ≤ t then t else 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (t : ℝ) + 1))
  intro n hn
  have hnceil : Nat.ceil (t : ℝ) < n := by simpa using hn
  have htn : t < (n : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe]
    exact (Nat.le_ceil (t : ℝ)).trans_lt (by exact_mod_cast hnceil)
  have hnot : ¬a n ≤ t := not_le.mpr (htn.trans_le (ha n))
  simp [hnot]

/-- A step envelope with escaping thresholds is measurable. -/
theorem measurable_step (a : ℕ → ℝ≥0) : Measurable (step a) := by
  apply Measurable.tsum
  intro n
  exact measurable_id.ite measurableSet_Ici measurable_const

/-- Escaping thresholds make the associated step envelope superlinear. -/
theorem superlinear_step (a : ℕ → ℝ≥0) (ha : ∀ n : ℕ, (n : ℝ≥0) ≤ a n) :
    SuperlinearEnvelope (step a) := by
  rw [SuperlinearEnvelope, tendsto_atTop]
  intro R
  let N : ℕ := Nat.ceil (R : ℝ) + 1
  let A : ℝ≥0 := max 1 ((Finset.range N).sup a)
  refine Filter.eventually_atTop.2 ⟨A, fun t ht ↦ ?_⟩
  have htpos : 0 < t := zero_lt_one.trans_le ((le_max_left _ _).trans ht)
  have hRN : R ≤ (N : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    dsimp [N]
    exact (Nat.le_ceil (R : ℝ)).trans (by exact_mod_cast Nat.le_add_right _ _)
  have hsum : ∑ n ∈ Finset.range N, (if a n ≤ t then t else 0) = N • t := by
    calc
      ∑ n ∈ Finset.range N, (if a n ≤ t then t else 0) =
          ∑ _n ∈ Finset.range N, t := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos]
        exact (Finset.le_sup (f := a) hn).trans ((le_max_right _ _).trans ht)
      _ = N • t := by simp
  have hpartial : N • t ≤ step a t := by
    rw [← hsum]
    exact (summable_step a ha t).sum_le_tsum (Finset.range N) (fun _ _ ↦ zero_le)
  exact hRN.trans ((le_div_iff₀ htpos).2 (by simpa [nsmul_eq_mul] using hpartial))

/-- A uniform bound on superlinear-envelope integrals gives a uniform `L¹` tail estimate. -/
theorem exists_eLpNorm_indicator_le {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (C : ℝ≥0)
    (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ≥0, ∀ i,
      eLpNorm ({x | M ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε := by
  let e : ℝ≥0 := ⟨ε, hε.le⟩
  let R : ℝ≥0 := (C + 1) / e
  have hepos : 0 < e := hε
  have hRpos : 0 < R := div_pos (by positivity) hepos
  have hratio : ∀ᶠ t in atTop, R ≤ Φ t / t := (tendsto_atTop.1 hΦ) R
  obtain ⟨M, hM⟩ := eventually_atTop.1 hratio
  refine ⟨M, fun i ↦ ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ x, ‖{x | M ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ∂μ ≤
        ∫⁻ x, ((R : ℝ≥0∞)⁻¹ * (Φ ‖f i x‖₊ : ℝ≥0∞)) ∂μ := by
      apply lintegral_mono
      intro x
      change ‖{x | M ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ≤
        (R : ℝ≥0∞)⁻¹ * (Φ ‖f i x‖₊ : ℝ≥0∞)
      by_cases hx : M ≤ ‖f i x‖₊
      · have hxmem : x ∈ {y : α | M ≤ ‖f i y‖₊} := hx
        rw [Set.indicator_of_mem hxmem]
        have hquot := hM ‖f i x‖₊ hx
        have hnormpos : 0 < ‖f i x‖₊ := by
          by_contra hn
          have hnzero : ‖f i x‖₊ = 0 := le_antisymm (not_lt.mp hn) zero_le
          rw [hnzero, div_zero] at hquot
          exact (not_le_of_gt hRpos) hquot
        have hmul : R * ‖f i x‖₊ ≤ Φ ‖f i x‖₊ := (le_div_iff₀ hnormpos).mp hquot
        have hnn : ‖f i x‖₊ ≤ R⁻¹ * Φ ‖f i x‖₊ := by
          calc
            ‖f i x‖₊ = R⁻¹ * (R * ‖f i x‖₊) := by field_simp
            _ ≤ R⁻¹ * Φ ‖f i x‖₊ := mul_le_mul_of_nonneg_left hmul zero_le
        rw [enorm_eq_nnnorm, ← ENNReal.coe_inv hRpos.ne', ← ENNReal.coe_mul]
        exact ENNReal.coe_le_coe.mpr hnn
      · have hxmem : x ∉ {y : α | M ≤ ‖f i y‖₊} := hx
        rw [Set.indicator_of_notMem hxmem, enorm_zero]
        exact zero_le
    _ ≤ (R : ℝ≥0∞)⁻¹ * ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ := by
      have hmeas : AEMeasurable (fun x ↦ (Φ ‖f i x‖₊ : ℝ≥0∞)) μ :=
        (hΦmeas.comp_aemeasurable (hf i).nnnorm.aemeasurable).coe_nnreal_ennreal
      exact (lintegral_const_mul'' (R : ℝ≥0∞)⁻¹ hmeas).le
    _ ≤ (R : ℝ≥0∞)⁻¹ * (C : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_left (hC i) zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [show ENNReal.ofReal ε = (e : ℝ≥0∞) by
        have he : NNReal.mk ε hε.le = e := by
          apply NNReal.eq
          rfl
        exact (ENNReal.ofReal_eq_coe_nnreal hε.le).trans (congrArg ((↑) : ℝ≥0 → ℝ≥0∞) he)]
      have hfinal : R⁻¹ * C ≤ e := by
        dsimp [R]
        rw [inv_div]
        calc
          e / (C + 1) * C ≤ e / (C + 1) * (C + 1) := by
            exact mul_le_mul_of_nonneg_left (le_add_right (le_refl C)) zero_le
          _ = e := by field_simp
      rw [← ENNReal.coe_inv hRpos.ne', ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr hfinal

end SuperlinearEnvelope

/-- Superlinear-envelope control implies measure-theoretic uniform integrability in `L¹`. -/
theorem unifIntegrable_of_superlinearEnvelope {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ≥0) (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞)) :
    UnifIntegrable f 1 μ :=
  unifIntegrable_of le_rfl ENNReal.one_ne_top hf fun _ hε ↦
    hΦ.exists_eLpNorm_indicator_le hΦmeas hf C hC hε

/-- On a finite measure space, superlinear-envelope control also implies Mathlib's
probability-style uniform integrability in `L¹`. -/
theorem uniformIntegrable_of_superlinearEnvelope [IsFiniteMeasure μ]
    {f : ι → α → E} {Φ : ℝ≥0 → ℝ≥0}
    (hΦ : SuperlinearEnvelope Φ) (hΦmeas : Measurable Φ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ≥0) (hC : ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞)) :
    UniformIntegrable f 1 μ :=
  uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun _ hε ↦
    hΦ.exists_eLpNorm_indicator_le hΦmeas hf C hC hε

/-- Converse de la Vallée-Poussin construction on a finite measure space.  The step envelope is
measurable and superlinear; convexity is not needed for the criterion and is therefore not baked
into the public witness. -/
theorem UniformIntegrable.exists_superlinearEnvelope [IsFiniteMeasure μ]
    {f : ι → α → E} (hf : UniformIntegrable f 1 μ) :
    ∃ Φ : ℝ≥0 → ℝ≥0, SuperlinearEnvelope Φ ∧ Measurable Φ ∧
      ∃ C : ℝ≥0, ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞) := by
  let e : ℕ → ℝ≥0 := fun n ↦ (2⁻¹ : ℝ≥0) ^ (n + 1)
  have hepos (n : ℕ) : 0 < (e n : ℝ) := by simp [e]
  choose b hb using fun n ↦ hf.spec one_ne_zero ENNReal.one_ne_top (hepos n)
  let a : ℕ → ℝ≥0 := fun n ↦ max (b n) n
  have ha (n : ℕ) : (n : ℝ≥0) ≤ a n := le_max_right _ _
  have htail (n : ℕ) (i : ι) :
      eLpNorm ({x | a n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤ (e n : ℝ≥0∞) := by
    calc
      eLpNorm ({x | a n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ ≤
          eLpNorm ({x | b n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ := by
        apply eLpNorm_mono
        exact fun x ↦ norm_indicator_le_of_subset
          (show {x | a n ≤ ‖f i x‖₊} ⊆ {x | b n ≤ ‖f i x‖₊} from
            fun x hx ↦ by
              change a n ≤ ‖f i x‖₊ at hx
              change b n ≤ ‖f i x‖₊
              exact (le_max_left _ _).trans hx) (f i) x
      _ ≤ ENNReal.ofReal (e n : ℝ) := hb n i
      _ = (e n : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  refine ⟨SuperlinearEnvelope.step a, SuperlinearEnvelope.superlinear_step a ha,
    SuperlinearEnvelope.measurable_step a, 1, fun i ↦ ?_⟩
  have hterm (n : ℕ) :
      (fun x ↦ ((if a n ≤ ‖f i x‖₊ then ‖f i x‖₊ else 0 : ℝ≥0) : ℝ≥0∞)) =ᵐ[μ]
        fun x ↦ ‖{x | a n ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ := by
    exact Eventually.of_forall fun x ↦ by
      by_cases hx : a n ≤ ‖f i x‖₊ <;> simp [hx, enorm_eq_nnnorm]
  have hmeasTerm (n : ℕ) : AEMeasurable
      (fun x ↦ ((if a n ≤ ‖f i x‖₊ then ‖f i x‖₊ else 0 : ℝ≥0) : ℝ≥0∞)) μ :=
    by
      have hs : NullMeasurableSet {x | a n ≤ ‖f i x‖₊} μ :=
        nullMeasurableSet_le aemeasurable_const
          (hf.aestronglyMeasurable i).nnnorm.aemeasurable
      apply AEMeasurable.congr
        ((hf.aestronglyMeasurable i).nnnorm.aemeasurable.coe_nnreal_ennreal.indicator₀ hs)
      exact Eventually.of_forall fun x ↦ by
        by_cases hx : a n ≤ ‖f i x‖₊ <;> simp [Set.indicator, hx]
  calc
    ∫⁻ x, (SuperlinearEnvelope.step a ‖f i x‖₊ : ℝ≥0∞) ∂μ =
        ∫⁻ x, ∑' n, ((if a n ≤ ‖f i x‖₊ then ‖f i x‖₊ else 0 : ℝ≥0) : ℝ≥0∞) ∂μ := by
      apply lintegral_congr
      intro x
      exact ENNReal.coe_tsum (SuperlinearEnvelope.summable_step a ha ‖f i x‖₊)
    _ = ∑' n, ∫⁻ x,
        ((if a n ≤ ‖f i x‖₊ then ‖f i x‖₊ else 0 : ℝ≥0) : ℝ≥0∞) ∂μ :=
      lintegral_tsum (β := ℕ) hmeasTerm
    _ = ∑' n, eLpNorm ({x | a n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ := by
      apply tsum_congr
      intro n
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact lintegral_congr_ae (hterm n)
    _ ≤ ∑' n, (e n : ℝ≥0∞) := ENNReal.tsum_le_tsum fun n ↦ htail n i
    _ = 1 := by
      simp only [e, ENNReal.coe_pow]
      rw [show ((↑((2 : ℝ≥0)⁻¹) : ℝ≥0∞)) = (2 : ℝ≥0∞)⁻¹ by
        exact ENNReal.coe_inv (by norm_num)]
      rw [ENNReal.tsum_geometric_add_one]
      rw [ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) ENNReal.ofNat_ne_top
    _ = (1 : ℝ≥0∞) := rfl

/-- Finite-measure de la Vallée-Poussin criterion, in a form that exposes the measurable
superlinear envelope and a common envelope-integral bound. -/
theorem uniformIntegrable_iff_exists_superlinearEnvelope [IsFiniteMeasure μ]
    {f : ι → α → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    UniformIntegrable f 1 μ ↔
      ∃ Φ : ℝ≥0 → ℝ≥0, SuperlinearEnvelope Φ ∧ Measurable Φ ∧
        ∃ C : ℝ≥0, ∀ i, ∫⁻ x, (Φ ‖f i x‖₊ : ℝ≥0∞) ∂μ ≤ (C : ℝ≥0∞) := by
  constructor
  · exact UniformIntegrable.exists_superlinearEnvelope
  · rintro ⟨Φ, hΦ, hΦmeas, C, hC⟩
    exact uniformIntegrable_of_superlinearEnvelope hΦ hΦmeas hf C hC

end

end MeasureTheory
