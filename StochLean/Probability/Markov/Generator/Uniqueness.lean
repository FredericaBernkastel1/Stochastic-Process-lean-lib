/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Generator.Uniformization
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Uniqueness of bounded-Q uniformization

The Poisson-mixture construction does not depend on the selected dominating rate. The proof
identifies a higher-rate uniformization step as a lazy version of the lower-rate step and uses
the Cauchy convolution of Poisson weights. The zero-rate case is handled explicitly.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory

noncomputable section

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

local instance kernelNatCast : NatCast (Kernel E E) :=
  ⟨fun n => n • Kernel.id⟩

local instance kernelSemiring : Semiring (Kernel E E) :=
  Semiring.mk (fun a => Kernel.zero_comp a) (fun a => Kernel.comp_zero a)
    (fun a b c => Kernel.comp_add_right b c a)
    (fun a b c => Kernel.comp_add_left c a b)
    (natCast_zero := by change 0 • (Kernel.id : Kernel E E) = 0; simp)
    (natCast_succ := by
      intro n
      change (n + 1) • (Kernel.id : Kernel E E) = n • Kernel.id + Kernel.id
      rw [add_nsmul, one_nsmul])

theorem scaleKernel_add (c d : ℝ≥0∞) (κ : Kernel E E) :
    scaleKernel (c + d) κ = scaleKernel c κ + scaleKernel d κ := by
  ext x A hA
  simp only [scaleKernel_apply, Kernel.add_apply, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul]
  ring

theorem scaleKernel_one (κ : Kernel E E) : scaleKernel 1 κ = κ := by
  ext x A hA
  simp [scaleKernel_apply, Measure.smul_apply]

theorem scaleKernel_pow (c : ℝ≥0∞) (κ : Kernel E E) (n : ℕ) :
    (scaleKernel c κ) ^ n = scaleKernel (c ^ n) (κ ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, scaleKernel_one]
  | succ n ih =>
      rw [pow_succ, ih]
      change scaleKernel (c ^ n) (κ ^ n) ∘ₖ scaleKernel c κ = _
      rw [scaleKernel_comp_scaleKernel]
      apply congrArg₂ scaleKernel
      · exact (pow_succ c n).symm
      · exact (pow_succ κ n).symm

private theorem natCast_kernel_eq_scaleKernel_id (n : ℕ) :
    (n : Kernel E E) = scaleKernel n Kernel.id := by
  change n • Kernel.id = _
  induction n with
  | zero => ext x A hA; simp [scaleKernel_apply]
  | succ n ih =>
      rw [succ_nsmul, ih]
      ext x A hA
      simp [scaleKernel_apply, Measure.smul_apply]
      ring

private theorem scaleKernel_commute_scaleKernel_id (a b : ℝ≥0∞) (P : Kernel E E) :
    Commute (scaleKernel a P) (scaleKernel b Kernel.id) := by
  change scaleKernel a P ∘ₖ scaleKernel b Kernel.id =
    scaleKernel b Kernel.id ∘ₖ scaleKernel a P
  rw [scaleKernel_comp_scaleKernel, scaleKernel_comp_scaleKernel,
    Kernel.comp_id, Kernel.id_comp, mul_comm]

theorem lazyKernel_pow (a b : ℝ≥0∞) (P : Kernel E E) (n : ℕ) :
    (scaleKernel a P + scaleKernel b Kernel.id) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        scaleKernel (n.choose k * a ^ k * b ^ (n - k)) (P ^ k) := by
  rw [(scaleKernel_commute_scaleKernel_id a b P).add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scaleKernel_pow, scaleKernel_pow, natCast_kernel_eq_scaleKernel_id]
  have hidpow : (Kernel.id : Kernel E E) ^ (n - k) = Kernel.id := one_pow _
  change (scaleKernel (a ^ k) (P ^ k) ∘ₖ
      scaleKernel (b ^ (n - k)) (Kernel.id ^ (n - k))) ∘ₖ
        scaleKernel (n.choose k) Kernel.id = _
  rw [scaleKernel_comp_scaleKernel, scaleKernel_comp_scaleKernel]
  rw [hidpow, Kernel.comp_id]
  apply congrArg₂ scaleKernel
  · ring
  · exact Kernel.comp_id _

theorem uniformizationKernel_eq_lazy_of_le
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ M : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hM : IsUniformizationRate q M)
    (hΛpos : 0 < Λ) (hΛM : Λ ≤ M) :
    uniformizationKernel q M =
      scaleKernel (ENNReal.ofReal (Λ / M)) (uniformizationKernel q Λ) +
        scaleKernel (ENNReal.ofReal (1 - Λ / M)) Kernel.id := by
  have hMpos : 0 < M := hΛpos.trans_le hΛM
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  simp only [add_apply, scaleKernel_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    rw [uniformizationKernel, if_neg hMpos.ne', uniformizationKernel, if_neg hΛpos.ne']
    change positiveUniformizationMeasure q M x {x} =
      ENNReal.ofReal (Λ / M) * positiveUniformizationMeasure q Λ x {x} +
        ENNReal.ofReal (1 - Λ / M) * Kernel.id x {x}
    rw [positiveUniformizationMeasure_apply_self, positiveUniformizationMeasure_apply_self,
      Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
    rw [Set.indicator_of_mem (Set.mem_singleton x)]
    simp only [Pi.one_apply, mul_one]
    have ha : 0 ≤ Λ / M := div_nonneg hΛpos.le hMpos.le
    have hb : 0 ≤ 1 - Λ / M := sub_nonneg.mpr ((div_le_one hMpos).2 hΛM)
    have hc : 0 ≤ 1 - exitRate q x / Λ :=
      sub_nonneg.mpr ((div_le_one hΛpos).2 (hΛ.dominates x))
    rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (mul_nonneg ha hc) hb]
    congr 1
    field_simp
    ring
  · rw [uniformizationKernel, if_neg hMpos.ne', uniformizationKernel, if_neg hΛpos.ne']
    change positiveUniformizationMeasure q M x {y} =
      ENNReal.ofReal (Λ / M) * positiveUniformizationMeasure q Λ x {y} +
        ENNReal.ofReal (1 - Λ / M) * Kernel.id x {y}
    rw [positiveUniformizationMeasure_apply_of_ne q M hxy,
      positiveUniformizationMeasure_apply_of_ne q Λ hxy,
      Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton y)]
    rw [Set.indicator_of_notMem (by simpa using hxy), mul_zero, add_zero]
    have ha : 0 ≤ Λ / M := div_nonneg hΛpos.le hMpos.le
    have hc : 0 ≤ q x y / Λ :=
      div_nonneg (hq.offDiag_nonneg x y hxy) hΛpos.le
    rw [← ENNReal.ofReal_mul ha]
    congr 1
    field_simp

private theorem uniformizationRealCoefficient (Λ M : ℝ) (t : ℝ≥0) (hM : M ≠ 0)
    {n k : ℕ} (hk : k ≤ n) :
    (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
        (n.choose k * (Λ / M) ^ k * (1 - Λ / M) ^ (n - k)) =
      (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) *
        (Real.exp (-(M - Λ) * t) * ((M - Λ) * t) ^ (n - k) /
          (n - k).factorial) := by
  have hn : n = k + (n - k) := (Nat.add_sub_of_le hk).symm
  have hfac := Nat.choose_mul_factorial_mul_factorial hk
  have hfacR : (n.factorial : ℝ) =
      (n.choose k : ℝ) * k.factorial * (n - k).factorial := by
    exact_mod_cast hfac.symm
  have hchoose : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hpow : (M * (t : ℝ)) ^ n * (Λ / M) ^ k *
      (1 - Λ / M) ^ (n - k) =
      (Λ * t) ^ k * ((M - Λ) * t) ^ (n - k) := by
    rw [show 1 - Λ / M = (M - Λ) / M by field_simp]
    rw [hn, pow_add]
    simp only [Nat.add_sub_cancel_left]
    simp only [mul_pow, div_pow]
    field_simp [hM]
  have hprod : (M * (t : ℝ)) ^ n *
      ((n.choose k : ℝ) * (Λ / M) ^ k * (1 - Λ / M) ^ (n - k)) =
      (n.choose k : ℝ) * ((Λ * t) ^ k * ((M - Λ) * t) ^ (n - k)) := by
    calc
      _ = (n.choose k : ℝ) *
          ((M * t) ^ n * (Λ / M) ^ k * (1 - Λ / M) ^ (n - k)) := by ring
      _ = _ := by rw [hpow]
  rw [show Real.exp (-M * (t : ℝ)) =
      Real.exp (-Λ * t) * Real.exp (-(M - Λ) * t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [hfacR]
  field_simp [hchoose]
  ring_nf at hpow ⊢
  simpa [mul_inv_cancel₀ hM] using hpow

private theorem uniformizationCoefficient (Λ M : ℝ) (t : ℝ≥0)
    (hΛ : 0 ≤ Λ) (hΛM : Λ ≤ M) (hMpos : 0 < M)
    {n k : ℕ} (hk : k ≤ n) :
    ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
        ((n.choose k : ℝ≥0∞) * ENNReal.ofReal (Λ / M) ^ k *
          ENNReal.ofReal (1 - Λ / M) ^ (n - k)) =
      ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) *
        ENNReal.ofReal (Real.exp (-(M - Λ) * t) *
          ((M - Λ) * t) ^ (n - k) / (n - k).factorial) := by
  have ha : 0 ≤ Λ / M := div_nonneg hΛ hMpos.le
  have hb : 0 ≤ 1 - Λ / M := sub_nonneg.mpr ((div_le_one hMpos).2 hΛM)
  have hwM : 0 ≤ Real.exp (-M * t) * (M * t) ^ n / n.factorial := by positivity
  have hwΛ : 0 ≤ Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial := by positivity
  have hMu : 0 ≤ M - Λ := sub_nonneg.mpr hΛM
  have hwu : 0 ≤ Real.exp (-(M - Λ) * t) *
      ((M - Λ) * t) ^ (n - k) / (n - k).factorial := by positivity
  rw [← ENNReal.ofReal_natCast (n.choose k), ← ENNReal.ofReal_pow ha,
    ← ENNReal.ofReal_pow hb]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg' (n.choose k))]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg' (n.choose k))
    (pow_nonneg ha k))]
  rw [← ENNReal.ofReal_mul hwM, ← ENNReal.ofReal_mul hwΛ]
  congr 1
  exact uniformizationRealCoefficient Λ M t hMpos.ne' hk

theorem ENNReal.tsum_sum_range_mul (f g : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
      (∑' k, f k) * ∑' j, g j := by
  simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k j => f k * g j]
  conv_lhs =>
    congr
    ext n
    rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  calc
    (∑' n : ℕ, ∑' b : ↥(Finset.antidiagonal n),
        f (b : ℕ × ℕ).1 * g (b : ℕ × ℕ).2) =
        ∑' p : Σ n : ℕ, ↥(Finset.antidiagonal n),
          f (p.2 : ℕ × ℕ).1 * g (p.2 : ℕ × ℕ).2 :=
      (ENNReal.tsum_sigma _).symm
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 := by
      simpa [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd] using
        (Equiv.tsum_eq
          (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
          (fun p : ℕ × ℕ => f p.1 * g p.2))
    _ = ∑' k : ℕ, ∑' j : ℕ, f k * g j := ENNReal.tsum_prod'
    _ = (∑' k, f k) * ∑' j, g j := by
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]

theorem poissonMixture_lazy
    (P : Kernel E E) (Λ M : ℝ) (t : ℝ≥0)
    (hΛ : 0 ≤ Λ) (hΛM : Λ ≤ M) (hMpos : 0 < M) :
    Kernel.sum (fun n : ℕ =>
      scaleKernel
        (ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial))
        ((scaleKernel (ENNReal.ofReal (Λ / M)) P +
          scaleKernel (ENNReal.ofReal (1 - Λ / M)) Kernel.id) ^ n)) =
    Kernel.sum (fun k : ℕ =>
      scaleKernel
        (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial))
        (P ^ k)) := by
  ext x A hA
  rw [Kernel.sum_apply' _ x hA, Kernel.sum_apply' _ x hA]
  simp_rw [lazyKernel_pow]
  simp only [scaleKernel_apply, Measure.smul_apply, smul_eq_mul]
  have hsum (n : ℕ) :
      ((∑ k ∈ Finset.range (n + 1),
          scaleKernel (n.choose k * ENNReal.ofReal (Λ / M) ^ k *
            ENNReal.ofReal (1 - Λ / M) ^ (n - k)) (P ^ k)) x) A =
        ∑ k ∈ Finset.range (n + 1),
          (n.choose k * ENNReal.ofReal (Λ / M) ^ k *
            ENNReal.ofReal (1 - Λ / M) ^ (n - k)) * (P ^ k) x A := by
    classical
    let F : ℕ → Kernel E E := fun k =>
      scaleKernel (n.choose k * ENNReal.ofReal (Λ / M) ^ k *
        ENNReal.ofReal (1 - Λ / M) ^ (n - k)) (P ^ k)
    let G : ℕ → ℝ≥0∞ := fun k =>
      (n.choose k * ENNReal.ofReal (Λ / M) ^ k *
        ENNReal.ofReal (1 - Λ / M) ^ (n - k)) * (P ^ k) x A
    change ((∑ k ∈ Finset.range (n + 1), F k) x) A =
      ∑ k ∈ Finset.range (n + 1), G k
    generalize Finset.range (n + 1) = s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [add_apply, Measure.add_apply, ih]
        simp only [F, G, scaleKernel_apply, Measure.smul_apply, smul_eq_mul]
  have hrewrite :
      (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
          ((∑ k ∈ Finset.range (n + 1),
            scaleKernel (n.choose k * ENNReal.ofReal (Λ / M) ^ k *
              ENNReal.ofReal (1 - Λ / M) ^ (n - k)) (P ^ k)) x) A) =
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
            ((n.choose k * ENNReal.ofReal (Λ / M) ^ k *
              ENNReal.ofReal (1 - Λ / M) ^ (n - k)) * (P ^ k) x A)) := by
    funext n
    rw [hsum n, Finset.mul_sum]
  rw [hrewrite]
  have hcoeff (n k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
          (↑(n.choose k) * ENNReal.ofReal (Λ / M) ^ k *
            ENNReal.ofReal (1 - Λ / M) ^ (n - k)) =
        ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) *
          ENNReal.ofReal (Real.exp (-(M - Λ) * t) *
            ((M - Λ) * t) ^ (n - k) / (n - k).factorial) :=
    uniformizationCoefficient Λ M t hΛ hΛM hMpos
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hinner (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (Real.exp (-M * t) * (M * t) ^ n / n.factorial) *
          ((n.choose k * ENNReal.ofReal (Λ / M) ^ k *
            ENNReal.ofReal (1 - Λ / M) ^ (n - k)) * (P ^ k) x A)) =
      ∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) *
          ENNReal.ofReal (Real.exp (-(M - Λ) * t) *
            ((M - Λ) * t) ^ (n - k) / (n - k).factorial)) * (P ^ k) x A := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← mul_assoc, hcoeff n k hk]
  simp_rw [hinner]
  let f : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) * (P ^ k) x A
  let g : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.exp (-(M - Λ) * t) * ((M - Λ) * t) ^ j / j.factorial)
  have hreorder (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ k / k.factorial) *
          ENNReal.ofReal (Real.exp (-(M - Λ) * t) *
            ((M - Λ) * t) ^ (n - k) / (n - k).factorial)) * (P ^ k) x A) =
      ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [f, g]
    ring
  simp_rw [hreorder]
  change (∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) =
    ∑' k : ℕ, f k
  rw [ENNReal.tsum_sum_range_mul]
  rw [uniformizationWeights_tsum_eq_one (M - Λ) t (sub_nonneg.mpr hΛM)]
  simp

theorem uniformizationKernel_zero_q (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    uniformizationKernel (fun _ _ : E => 0) Λ = Kernel.id := by
  by_cases hz : Λ = 0
  · subst Λ
    exact uniformizationKernel_zero _
  have hΛpos : 0 < Λ := lt_of_le_of_ne hΛ (Ne.symm hz)
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [uniformizationKernel, if_neg hz, Kernel.id_apply,
    Measure.dirac_apply' _ (measurableSet_singleton y)]
  change positiveUniformizationMeasure (fun _ _ : E => 0) Λ x {y} = _
  by_cases hxy : x = y
  · subst y
    rw [positiveUniformizationMeasure_apply_self]
    simp [exitRate]
  · rw [positiveUniformizationMeasure_apply_of_ne _ _ hxy]
    simp [hxy]

theorem uniformizedSemigroup_zero_q (Λ : ℝ) (hΛ : 0 ≤ Λ) (t : ℝ≥0) :
    uniformizedSemigroup (fun _ _ : E => 0) Λ t = Kernel.id := by
  ext x A hA
  rw [uniformizedSemigroup, Kernel.sum_apply' _ x hA,
    uniformizationKernel_zero_q Λ hΛ, Kernel.id_apply]
  have hterm (n : ℕ) :
      ((scaleKernel
        (ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial))
        ((Kernel.id : Kernel E E) ^ n)) x) A =
      ENNReal.ofReal (Real.exp (-Λ * t) * (Λ * t) ^ n / n.factorial) *
        (Measure.dirac x) A := by
    have hid : (Kernel.id : Kernel E E) ^ n = Kernel.id := by
      change (1 : Kernel E E) ^ n = 1
      exact one_pow n
    rw [hid, scaleKernel_apply, Measure.smul_apply, Kernel.id_apply]
    rfl
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_right, uniformizationWeights_tsum_eq_one Λ t hΛ, one_mul]

theorem uniformizedSemigroup_eq_of_rate_le
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ M : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hM : IsUniformizationRate q M)
    (hΛM : Λ ≤ M) (t : ℝ≥0) :
    uniformizedSemigroup q M t = uniformizedSemigroup q Λ t := by
  by_cases hΛzero : Λ = 0
  · subst Λ
    have hqzero := hΛ.eq_zero_of_zero hq
    subst q
    rw [uniformizedSemigroup_zero_q M hM.nonneg,
      uniformizedSemigroup_zero_q 0 hΛ.nonneg]
  · have hΛpos : 0 < Λ := lt_of_le_of_ne hΛ.nonneg (Ne.symm hΛzero)
    have hMpos : 0 < M := hΛpos.trans_le hΛM
    rw [uniformizedSemigroup, uniformizedSemigroup,
      uniformizationKernel_eq_lazy_of_le hq hΛ hM hΛpos hΛM]
    exact poissonMixture_lazy (uniformizationKernel q Λ) Λ M t
      hΛ.nonneg hΛM hMpos

theorem uniformizedSemigroup_rate_independent
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ M : ℝ}
    (hΛ : IsUniformizationRate q Λ) (hM : IsUniformizationRate q M) :
    uniformizedSemigroup q Λ = uniformizedSemigroup q M := by
  funext t
  rcases le_total Λ M with hΛM | hMΛ
  · exact (uniformizedSemigroup_eq_of_rate_le hq hΛ hM hΛM t).symm
  · exact uniformizedSemigroup_eq_of_rate_le hq hM hΛ hMΛ t

/-! ### Canonical bounded-Q semigroup -/

/-- A transition family is the canonical bounded-Q semigroup when it is obtained by
uniformization at some explicit dominating rate.  The rate is deliberately kept existential:
`uniformizedSemigroup_rate_independent` proves that it is construction data, not semantics. -/
def IsCanonicalBoundedQSemigroup (q : E → E → ℝ) (κ : ℝ≥0 → Kernel E E) : Prop :=
  ∃ Λ : ℝ, IsUniformizationRate q Λ ∧ κ = uniformizedSemigroup q Λ

/-- Every valid uniformization construction represents the canonical bounded-Q semigroup. -/
theorem isCanonicalBoundedQSemigroup_uniformizedSemigroup
    {q : E → E → ℝ} (Λ : ℝ) (hΛ : IsUniformizationRate q Λ) :
    IsCanonicalBoundedQSemigroup q (uniformizedSemigroup q Λ) :=
  ⟨Λ, hΛ, rfl⟩

/-- Two canonical bounded-Q semigroups for the same Q-matrix are equal. -/
theorem IsCanonicalBoundedQSemigroup.eq
    {q : E → E → ℝ} (hq : IsQMatrix q)
    {κ η : ℝ≥0 → Kernel E E}
    (hκ : IsCanonicalBoundedQSemigroup q κ)
    (hη : IsCanonicalBoundedQSemigroup q η) : κ = η := by
  rcases hκ with ⟨Λ, hΛ, rfl⟩
  rcases hη with ⟨M, hM, rfl⟩
  exact uniformizedSemigroup_rate_independent hq hΛ hM

/-- The canonical bounded-Q semigroup exists and is unique once any explicit exit-rate bound is
provided.  This is uniqueness of the canonical transition family, not equality of process
functions carried by unrelated sample spaces. -/
theorem existsUnique_isCanonicalBoundedQSemigroup
    {q : E → E → ℝ} (hq : IsQMatrix q) {Λ : ℝ}
    (hΛ : IsUniformizationRate q Λ) :
    ∃! κ : ℝ≥0 → Kernel E E, IsCanonicalBoundedQSemigroup q κ := by
  refine ⟨uniformizedSemigroup q Λ,
    isCanonicalBoundedQSemigroup_uniformizedSemigroup Λ hΛ, ?_⟩
  intro κ hκ
  exact hκ.eq hq (isCanonicalBoundedQSemigroup_uniformizedSemigroup Λ hΛ)

/-- The canonical bounded-Q transition family is a Markov semigroup. -/
theorem IsCanonicalBoundedQSemigroup.isMarkovSemigroup
    {q : E → E → ℝ} (hq : IsQMatrix q)
    {κ : ℝ≥0 → Kernel E E} (hκ : IsCanonicalBoundedQSemigroup q κ) :
    IsMarkovSemigroup κ := by
  rcases hκ with ⟨Λ, hΛ, rfl⟩
  exact isMarkovSemigroup_uniformizedSemigroup hq hΛ

/-- The canonical bounded-Q transition family has the prescribed singleton right derivative. -/
theorem IsCanonicalBoundedQSemigroup.hasQMatrix
    {q : E → E → ℝ} (hq : IsQMatrix q)
    {κ : ℝ≥0 → Kernel E E} (hκ : IsCanonicalBoundedQSemigroup q κ) :
    HasQMatrix κ q := by
  rcases hκ with ⟨Λ, hΛ, rfl⟩
  exact hasQMatrix_uniformizedSemigroup hq hΛ

end

end ProbabilityTheory
