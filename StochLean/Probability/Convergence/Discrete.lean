/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.GeneratingFunction.Basic
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Convergence of natural-number-valued laws

This file proves both directions of the discrete convergence principle. Coefficientwise
convergence implies PGF convergence by Tannery's theorem. Conversely, nonnegative coefficients
can be recovered from PGF convergence using normalized tails at arbitrarily small positive
arguments; no interchange of limits and derivatives is required.
-/

@[expose] public section

open Filter Topology

namespace PMF

noncomputable section

variable {ι : Type*} {l : Filter ι} {p : ι → PMF ℕ} {q : PMF ℕ}

/-- The real mass assigned by a natural-valued PMF to an arbitrary set. -/
def setMassReal (p : PMF ℕ) (s : Set ℕ) : ℝ :=
  ∑' n, s.indicator p.massReal n

/-- The real mass in the tail starting at `k`. -/
def tailMassReal (p : PMF ℕ) (k : ℕ) : ℝ :=
  ∑' n, p.massReal (n + k)

lemma summable_setMassReal (p : PMF ℕ) (s : Set ℕ) :
    Summable (s.indicator p.massReal) :=
  p.summable_massReal.indicator s

lemma tailMassReal_eq_one_sub_sum_range (p : PMF ℕ) (k : ℕ) :
    p.tailMassReal k = 1 - ∑ n ∈ Finset.range k, p.massReal n := by
  have h := p.summable_massReal.sum_add_tsum_nat_add k
  rw [p.tsum_massReal] at h
  rw [eq_sub_iff_add_eq]
  simpa only [tailMassReal, add_comm] using h

lemma tailMassReal_nonneg (p : PMF ℕ) (k : ℕ) : 0 ≤ p.tailMassReal k :=
  tsum_nonneg fun n ↦ p.massReal_nonneg (n + k)

lemma tendsto_tailMassReal_atTop (p : PMF ℕ) :
    Tendsto p.tailMassReal atTop (𝓝 0) := by
  have h :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      p.summable_massReal.tendsto_sum_tsum_nat
  rw [p.tsum_massReal] at h
  simpa only [sub_self] using
    h.congr' (Eventually.of_forall fun k ↦ (p.tailMassReal_eq_one_sub_sum_range k).symm)

lemma tendsto_tailMassReal_of_tendsto_mass
    (h : ∀ n, Tendsto (fun i ↦ (p i).massReal n) l (𝓝 (q.massReal n))) (k : ℕ) :
    Tendsto (fun i ↦ (p i).tailMassReal k) l (𝓝 (q.tailMassReal k)) := by
  have hsum : Tendsto
      (fun i ↦ ∑ n ∈ Finset.range k, (p i).massReal n) l
      (𝓝 (∑ n ∈ Finset.range k, q.massReal n)) := by
    exact tendsto_finsetSum _ fun n _ ↦ h n
  simpa only [tailMassReal_eq_one_sub_sum_range] using tendsto_const_nhds.sub hsum

lemma setMassReal_eq_sum_add_tail (p : PMF ℕ) (s : Set ℕ) (k : ℕ) :
    p.setMassReal s =
      ∑ n ∈ Finset.range k, s.indicator p.massReal n +
        ∑' n, s.indicator p.massReal (n + k) := by
  exact (p.summable_setMassReal s).sum_add_tsum_nat_add k |>.symm

lemma setMassReal_tail_le (p : PMF ℕ) (s : Set ℕ) (k : ℕ) :
    (∑' n, s.indicator p.massReal (n + k)) ≤ p.tailMassReal k := by
  apply ((summable_nat_add_iff k).2 (p.summable_setMassReal s)).tsum_le_tsum
  · intro n
    by_cases hn : n + k ∈ s
    · simp [Set.indicator_of_mem hn]
    · simp [Set.indicator_of_notMem hn, p.massReal_nonneg]
  · exact (summable_nat_add_iff k).2 p.summable_massReal

lemma setMassReal_tail_nonneg (p : PMF ℕ) (s : Set ℕ) (k : ℕ) :
    0 ≤ ∑' n, s.indicator p.massReal (n + k) :=
  tsum_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ p.massReal_nonneg _) _

/-- Coefficientwise convergence of natural-number-valued probability laws implies setwise
convergence. This is the discrete Scheffé principle: total probability prevents mass from escaping
to infinity. -/
theorem tendsto_setMassReal_of_tendsto_mass
    (h : ∀ n, Tendsto (fun i ↦ (p i).massReal n) l (𝓝 (q.massReal n)))
    (s : Set ℕ) : Tendsto (fun i ↦ (p i).setMassReal s) l (𝓝 (q.setMassReal s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hqtail : ∀ᶠ k in atTop, q.tailMassReal k < ε / 8 :=
    q.tendsto_tailMassReal_atTop.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨k, hk⟩ := hqtail.exists
  have hfinite : Tendsto
      (fun i ↦ ∑ n ∈ Finset.range k, s.indicator (p i).massReal n) l
      (𝓝 (∑ n ∈ Finset.range k, s.indicator q.massReal n)) := by
    apply tendsto_finsetSum
    intro n _
    by_cases hn : n ∈ s
    · simpa [Set.indicator_of_mem hn] using h n
    · simpa [Set.indicator_of_notMem hn] using
        (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  have hptail := tendsto_tailMassReal_of_tendsto_mass h k
  filter_upwards
      [(Metric.tendsto_nhds.1 hfinite) (ε / 2) (by positivity),
        (Metric.tendsto_nhds.1 hptail) (ε / 8) (by positivity)] with i hfin htail
  rw [(p i).setMassReal_eq_sum_add_tail s k, q.setMassReal_eq_sum_add_tail s k]
  apply lt_of_le_of_lt (dist_add_add_le _ _ _ _)
  have hpnonneg := (p i).setMassReal_tail_nonneg s k
  have hqnonneg := q.setMassReal_tail_nonneg s k
  have hple : (p i).tailMassReal k < ε / 4 := by
    have hdiff : (p i).tailMassReal k - q.tailMassReal k ≤
        dist ((p i).tailMassReal k) (q.tailMassReal k) := by
      rw [Real.dist_eq]
      exact le_abs_self _
    linarith
  have hsetp := (p i).setMassReal_tail_le s k
  have hsetq := q.setMassReal_tail_le s k
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  calc
    dist (∑ n ∈ Finset.range k, s.indicator (p i).massReal n)
          (∑ n ∈ Finset.range k, s.indicator q.massReal n) +
        ‖(∑' n, s.indicator (p i).massReal (n + k)) -
          (∑' n, s.indicator q.massReal (n + k))‖
        ≤ dist (∑ n ∈ Finset.range k, s.indicator (p i).massReal n)
            (∑ n ∈ Finset.range k, s.indicator q.massReal n) +
          ((∑' n, s.indicator (p i).massReal (n + k)) +
            (∑' n, s.indicator q.massReal (n + k))) := by
              gcongr
              simpa [Real.norm_eq_abs, abs_of_nonneg hpnonneg, abs_of_nonneg hqnonneg] using
                norm_sub_le (∑' n, s.indicator (p i).massReal (n + k))
                  (∑' n, s.indicator q.massReal (n + k))
    _ < ε := by linarith

/-- Coefficientwise convergence of natural-number-valued laws implies convergence of their PGFs
at every point of `[0, 1]`. -/
theorem tendsto_pgf_of_tendsto_mass
    (h : ∀ n, Tendsto (fun i ↦ (p i).massReal n) l (𝓝 (q.massReal n)))
    (z : unitInterval) : Tendsto (fun i ↦ (p i).pgf z) l (𝓝 (q.pgf z)) := by
  by_cases hz : (z : ℝ) = 1
  · have hz' : z = 1 := Subtype.ext hz
    simp only [hz', pgf_one]
    exact tendsto_const_nhds
  · have hzlt : (z : ℝ) < 1 := lt_of_le_of_ne z.property.2 hz
    have hgeom : Summable fun n : ℕ ↦ (z : ℝ) ^ n := by
      apply summable_geometric_of_norm_lt_one
      simpa [Real.norm_eq_abs, abs_of_nonneg z.property.1]
    have ht := tendsto_tsum_of_dominated_convergence
      (𝓕 := l) (f := fun i n ↦ (p i).massReal n * (z : ℝ) ^ n)
      (g := fun n ↦ q.massReal n * (z : ℝ) ^ n)
      (bound := fun n ↦ (z : ℝ) ^ n) hgeom
      (fun n ↦ (h n).mul_const ((z : ℝ) ^ n))
      (Filter.Eventually.of_forall fun i n ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((p i).massReal_nonneg n),
          abs_of_nonneg (pow_nonneg z.property.1 n)]
        exact mul_le_of_le_one_left (pow_nonneg z.property.1 n) ((p i).massReal_le_one n))
    simpa only [pgf] using ht

/-- The PGF tail starting at coefficient `k`, normalized by the `k`-th power of the argument. -/
def normalizedPGFTail (p : PMF ℕ) (k : ℕ) (z : unitInterval) : ℝ :=
  ∑' n, p.massReal (n + k) * (z : ℝ) ^ n

lemma summable_normalizedPGFTail (p : PMF ℕ) (k : ℕ) (z : unitInterval) :
    Summable fun n ↦ p.massReal (n + k) * (z : ℝ) ^ n := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (p.massReal_nonneg _) (pow_nonneg z.property.1 _))
    (fun n ↦ mul_le_of_le_one_right (p.massReal_nonneg _)
      (pow_le_one₀ z.property.1 z.property.2))
  exact (summable_nat_add_iff k).2 p.summable_massReal

lemma tsum_massReal_nat_add_le_one (p : PMF ℕ) (k : ℕ) :
    (∑' n, p.massReal (n + k)) ≤ 1 := by
  have h := p.summable_massReal.sum_add_tsum_nat_add k
  rw [p.tsum_massReal] at h
  linarith [Finset.sum_nonneg (s := Finset.range k) (fun n _ ↦ p.massReal_nonneg n)]

lemma massReal_le_normalizedPGFTail (p : PMF ℕ) (k : ℕ) (z : unitInterval) :
    p.massReal k ≤ p.normalizedPGFTail k z := by
  rw [normalizedPGFTail, ← (p.summable_normalizedPGFTail k z).sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, zero_add, pow_zero, mul_one]
  exact le_add_of_nonneg_right (tsum_nonneg fun n ↦
    mul_nonneg (p.massReal_nonneg _) (pow_nonneg z.property.1 _))

lemma normalizedPGFTail_le_massReal_add (p : PMF ℕ) (k : ℕ) (z : unitInterval) :
    p.normalizedPGFTail k z ≤ p.massReal k + (z : ℝ) := by
  rw [normalizedPGFTail, ← (p.summable_normalizedPGFTail k z).sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, zero_add, pow_zero, mul_one]
  gcongr
  calc
    ∑' n, p.massReal (n + 1 + k) * (z : ℝ) ^ (n + 1) ≤
        ∑' n, (z : ℝ) * p.massReal (n + (k + 1)) := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [add_assoc, add_comm 1 k, ← add_assoc]
        calc
          p.massReal (n + (k + 1)) * (z : ℝ) ^ (n + 1) =
              (z : ℝ) * (p.massReal (n + (k + 1)) * (z : ℝ) ^ n) := by
                rw [pow_succ']
                ring
          _ ≤ (z : ℝ) * p.massReal (n + (k + 1)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_of_le_one_right (p.massReal_nonneg _)
                (pow_le_one₀ z.property.1 z.property.2)) z.property.1
      · exact ((summable_nat_add_iff 1).2 (p.summable_normalizedPGFTail k z))
      · exact ((summable_nat_add_iff (k + 1)).2 p.summable_massReal).mul_left (z : ℝ)
    _ = (z : ℝ) * ∑' n, p.massReal (n + (k + 1)) := by
      rw [((summable_nat_add_iff (k + 1)).2 p.summable_massReal).tsum_mul_left]
    _ ≤ (z : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (p.tsum_massReal_nat_add_le_one (k + 1)) z.property.1

lemma dist_massReal_normalizedPGFTail_le (p : PMF ℕ) (k : ℕ) (z : unitInterval) :
    dist (p.massReal k) (p.normalizedPGFTail k z) ≤ (z : ℝ) := by
  rw [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (p.massReal_le_normalizedPGFTail k z))]
  linarith [p.normalizedPGFTail_le_massReal_add k z]

lemma normalizedPGFTail_eq_pgf_sub_sum_div (p : PMF ℕ) (k : ℕ)
    (z : unitInterval) (hz : 0 < (z : ℝ)) :
    p.normalizedPGFTail k z =
      (p.pgf z - ∑ n ∈ Finset.range k, p.massReal n * (z : ℝ) ^ n) / (z : ℝ) ^ k := by
  unfold normalizedPGFTail
  rw [show p.pgf z = ∑ n ∈ Finset.range k, p.massReal n * (z : ℝ) ^ n +
      ∑' n, p.massReal (n + k) * (z : ℝ) ^ (n + k) by
    rw [pgf]
    exact ((p.summable_pgf z).sum_add_tsum_nat_add k).symm]
  rw [add_sub_cancel_left, ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [pow_add]
  field_simp

/-- Pointwise convergence of PGFs on `[0, 1]` recovers coefficientwise convergence of the
underlying natural-number-valued probability laws. -/
theorem tendsto_mass_of_tendsto_pgf
    (hpgf : ∀ z : unitInterval, Tendsto (fun i ↦ (p i).pgf z) l (nhds (q.pgf z))) :
    ∀ k, Tendsto (fun i ↦ (p i).massReal k) l (nhds (q.massReal k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [Metric.tendsto_nhds]
      intro ε hε
      let r : ℝ := min (ε / 4) (1 / 2)
      have hrpos : 0 < r := lt_min (div_pos hε (by norm_num)) (by norm_num)
      have hrle : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
      let z : unitInterval := ⟨r, hrpos.le, hrle⟩
      have hzpos : 0 < (z : ℝ) := hrpos
      have hsum : Tendsto
          (fun i ↦ ∑ n ∈ Finset.range k, (p i).massReal n * (z : ℝ) ^ n) l
          (nhds (∑ n ∈ Finset.range k, q.massReal n * (z : ℝ) ^ n)) := by
        apply tendsto_finsetSum
        intro n hn
        exact (ih n (Finset.mem_range.mp hn)).mul_const ((z : ℝ) ^ n)
      have htail : Tendsto (fun i ↦ (p i).normalizedPGFTail k z) l
          (nhds (q.normalizedPGFTail k z)) := by
        simp_rw [normalizedPGFTail_eq_pgf_sub_sum_div _ k z hzpos]
        exact ((hpgf z).sub hsum).div_const ((z : ℝ) ^ k)
      filter_upwards [(Metric.tendsto_nhds.1 htail) (ε / 2) (half_pos hε)] with i hi
      apply lt_of_le_of_lt
        (dist_triangle4 ((p i).massReal k) ((p i).normalizedPGFTail k z)
          (q.normalizedPGFTail k z) (q.massReal k))
      have hleft := (p i).dist_massReal_normalizedPGFTail_le k z
      have hright := q.dist_massReal_normalizedPGFTail_le k z
      rw [dist_comm (q.normalizedPGFTail k z) (q.massReal k)]
      rw [show (z : ℝ) = r by rfl] at hleft hright
      have hrε : r ≤ ε / 4 := min_le_left _ _
      linarith

/-- For natural-number-valued probability laws, coefficientwise convergence is equivalent to
pointwise convergence of PGFs on their full basic domain. -/
theorem tendsto_pgf_iff_tendsto_mass :
    (∀ z : unitInterval, Tendsto (fun i ↦ (p i).pgf z) l (nhds (q.pgf z))) ↔
      ∀ k, Tendsto (fun i ↦ (p i).massReal k) l (nhds (q.massReal k)) :=
  ⟨tendsto_mass_of_tendsto_pgf, fun h z ↦ tendsto_pgf_of_tendsto_mass h z⟩

end

end PMF
