/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Local convergence in measure

This file defines convergence in measure on every measurable set of finite measure. Unlike
`MeasureTheory.TendstoInMeasure`, this is the local notion used on sigma-finite spaces in Klenke,
Definition 6.2.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι κ E : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section EDist

variable [EDist E]

/-- `f` converges locally in `μ`-measure to `g` along `l` if it converges in measure after
restricting `μ` to every measurable set of finite measure. -/
def TendstoLocallyInMeasure (μ : Measure α) (f : ι → α → E) (l : Filter ι)
    (g : α → E) : Prop :=
  ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → TendstoInMeasure (μ.restrict s) f l g

namespace TendstoInMeasure

/-- Global convergence in measure implies local convergence in measure. -/
theorem locally {f : ι → α → E} {l : Filter ι} {g : α → E}
    (h : TendstoInMeasure μ f l g) : TendstoLocallyInMeasure μ f l g := by
  intro s _hs _hμs ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ bot_le) (fun _ ↦ Measure.restrict_le_self _)

end TendstoInMeasure

namespace TendstoLocallyInMeasure

variable {f f' : ι → α → E} {l : Filter ι} {g g' : α → E}

/-- On a finite measure, local convergence in measure is the same as Mathlib's global notion. -/
theorem iff_tendstoInMeasure [IsFiniteMeasure μ] :
    TendstoLocallyInMeasure μ f l g ↔ TendstoInMeasure μ f l g := by
  constructor
  · intro h
    simpa only [Measure.restrict_univ] using h Set.univ MeasurableSet.univ (measure_ne_top μ _)
  · exact TendstoInMeasure.locally

/-- Local convergence is preserved when the indexing filter is strengthened. -/
theorem mono {v : Filter ι} (hvl : v ≤ l) (h : TendstoLocallyInMeasure μ f l g) :
    TendstoLocallyInMeasure μ f v g := by
  intro s hs hμs
  exact (h s hs hμs).mono hvl

/-- Local convergence is preserved by reindexing. -/
theorem comp {v : Filter κ} {ns : κ → ι} (h : TendstoLocallyInMeasure μ f l g)
    (hns : Tendsto ns v l) : TendstoLocallyInMeasure μ (f ∘ ns) v g := by
  intro s hs hμs
  exact (h s hs hμs).comp hns

/-- Local convergence depends only on the almost-everywhere classes of all functions involved. -/
theorem congr (hleft : ∀ i, f i =ᵐ[μ] f' i) (hright : g =ᵐ[μ] g')
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f' l g' := by
  intro s hs hμs
  apply (h s hs hμs).congr
  · intro i
    exact Measure.AbsolutelyContinuous.ae_eq Measure.restrict_le_self.absolutelyContinuous
      (hleft i)
  · exact Measure.AbsolutelyContinuous.ae_eq Measure.restrict_le_self.absolutelyContinuous hright

theorem congr_left (hleft : ∀ i, f i =ᵐ[μ] f' i)
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f' l g :=
  h.congr hleft EventuallyEq.rfl

theorem congr_right (hright : g =ᵐ[μ] g')
    (h : TendstoLocallyInMeasure μ f l g) : TendstoLocallyInMeasure μ f l g' :=
  h.congr (fun _ ↦ EventuallyEq.rfl) hright

end TendstoLocallyInMeasure

end EDist

section AlmostEverywhere

variable {f : ℕ → α → E} {g : α → E} [PseudoEMetricSpace E]

/-- On each measurable finite-measure restriction, local convergence supplies an almost-everywhere
convergent subsequence. A single subsequence valid on an entire sigma-finite exhaustion requires a
separate diagonal argument. -/
theorem TendstoLocallyInMeasure.exists_seq_tendsto_ae_restrict
    (h : TendstoLocallyInMeasure μ f atTop g) (s : Set α) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(μ.restrict s), Tendsto (fun i ↦ f (ns i) x) atTop (nhds (g x)) :=
  (h s hs hμs).exists_seq_tendsto_ae

/-- On a sigma-finite measure space, a sequence converging locally in measure has a single
subsequence converging almost everywhere on the whole space.

The construction chooses the `n`-th term so that its bad set is small on Mathlib's `n`-th
sigma-finite spanning set. The first Borel–Cantelli lemma and the fact that the spanning sets
eventually contain every point then give global almost-everywhere convergence.
-/
theorem TendstoLocallyInMeasure.exists_seq_tendsto_ae [SigmaFinite μ]
    (hfg : TendstoLocallyInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i ↦ f (ns i) x) atTop (nhds (g x)) := by
  have h_lt_ε_real (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ k : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
    · positivity
    · simp
  let hres (n : ℕ) : TendstoInMeasure (μ.restrict (spanningSets μ n)) f atTop g :=
    hfg (spanningSets μ n) (measurableSet_spanningSets μ n)
      (measure_spanningSets_lt_top μ n).ne
  let N (n : ℕ) : ℕ := Classical.choose
    (ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (hres n) n)
  have hN (n m : ℕ) (hnm : N n ≤ m) :
      (μ.restrict (spanningSets μ n))
          {x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f m x) (g x)} ≤ (2 : ℝ≥0∞)⁻¹ ^ n :=
    Classical.choose_spec
      (ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (hres n) n) m hnm
  let ns : ℕ → ℕ := fun n ↦
    Nat.rec (N 0) (fun n previous ↦ max (N (n + 1)) (previous + 1)) n
  have hns_succ (n : ℕ) : ns (n + 1) = max (N (n + 1)) (ns n + 1) := by
    simp [ns]
  have hns_mono : StrictMono ns := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    rw [hns_succ]
    exact lt_of_lt_of_le (lt_add_one (ns n)) (le_max_right _ _)
  have hNns (n : ℕ) : N n ≤ ns n := by
    cases n with
    | zero => simp [ns]
    | succ n => rw [hns_succ]; exact le_max_left _ _
  refine ⟨ns, hns_mono, ?_⟩
  let S := fun k ↦
    {x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ edist (f (ns k) x) (g x)} ∩ spanningSets μ k
  have hμS_le : ∀ k, μ (S k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    change μ ({x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ edist (f (ns k) x) (g x)} ∩
      spanningSets μ k) ≤ _
    rw [← Measure.restrict_apply' (measurableSet_spanningSets μ k)]
    exact hN k (ns k) (hNns k)
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      ENNReal.ofNat_ne_top
  have h_tendsto : ∀ x ∈ sᶜ, Tendsto (fun i ↦ f (ns i) x) atTop (nhds (g x)) := by
    intro x hx
    refine EMetric.tendsto_atTop.mpr fun ε hε ↦ ?_
    rw [hs, limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter,
      Set.compl_iUnion, Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or] at hx
    obtain ⟨N₀, hN₀x⟩ := hx
    obtain ⟨N₁, hN₁x⟩ := (eventually_atTop.1 (eventually_mem_spanningSets μ x))
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max (max N₀ N₁) (k - 1), fun n hn_ge ↦ ?_⟩
    have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans (le_max_left _ _ |>.trans hn_ge)
    have hnN₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans (le_max_left _ _ |>.trans hn_ge)
    have hnot := hN₀x n hnN₀
    have hmem := hN₁x n hnN₁
    have hdist : edist (f (ns n) x) (g x) < (2 : ℝ≥0∞)⁻¹ ^ n := by
      rcases hnot with hnot | hnot
      · exact lt_of_not_ge hnot
      · exact False.elim (hnot hmem)
    have h_inv_n_le_k : (2 : ℝ≥0∞)⁻¹ ^ n ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : ℝ≥0∞)]
      rw [mul_comm, ← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_iff_le_mul,
        ← mul_assoc, mul_comm (_ ^ n), mul_assoc, ← ENNReal.inv_le_iff_le_mul,
        inv_inv, ← pow_add]
      · gcongr
        · simp
        · omega
      all_goals simp
    exact (lt_of_lt_of_le hdist h_inv_n_le_k).trans hk_lt_ε
  rw [ae_iff]
  exact measure_mono_null (fun x ↦ by
    rw [Set.mem_ofPred_eq, ← @Classical.not_not (x ∈ s), not_imp_not]
    exact h_tendsto x) hμs

/-- On a sigma-finite space, local convergence in measure is equivalent to the subsequence
principle: every subsequence has a further subsequence converging almost everywhere. -/
theorem exists_seq_tendstoLocallyInMeasure_atTop_iff [SigmaFinite μ]
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) :
    TendstoLocallyInMeasure μ f atTop g ↔
      ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ x ∂μ, Tendsto (fun i ↦ f (ns (ns' i)) x) atTop (nhds (g x)) := by
  constructor
  · intro h ns hns
    exact (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  · intro h s hs hμs
    let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
    rw [exists_seq_tendstoInMeasure_atTop_iff (fun n ↦ (hf n).restrict)]
    intro ns hns
    obtain ⟨ns', hns', hlim⟩ := h ns hns
    exact ⟨ns', hns', ae_restrict_of_ae hlim⟩

/-- Almost-everywhere convergence implies local convergence in measure, without assuming that the
ambient measure is finite. -/
theorem tendstoLocallyInMeasure_of_tendsto_ae
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    TendstoLocallyInMeasure μ f atTop g := by
  intro s _hs hμs
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hμs
  exact tendstoInMeasure_of_tendsto_ae (fun n ↦ (hf n).restrict) (ae_restrict_of_ae hfg)

end AlmostEverywhere

end MeasureTheory
