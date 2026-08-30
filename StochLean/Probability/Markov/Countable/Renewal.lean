/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Countable.Excursion

/-!
# Renewal series for countable-state Markov chains

This file isolates the extended-nonnegative Cauchy-product calculation used by the return-time
renewal equation.  No finiteness assumption is imposed on either series.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The Cauchy convolution associated with a renewal pair. -/
noncomputable def renewalConvolution (f u : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' N, ∑ k ∈ Finset.range (N + 1), f k * u (N - k)

/-- Extended mass of a nonnegative series. -/
noncomputable def ennrealSeriesMass (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, a n

/-- Product of the two total masses in a renewal pair. -/
noncomputable def renewalProduct (f u : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ennrealSeriesMass f * ennrealSeriesMass u

/-- Total mass after deleting the zeroth term. -/
noncomputable def ennrealTailMass (u : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, u (n + 1)

set_option maxHeartbeats 500000 in
-- The explicit sigma/antidiagonal reindexing requires a larger local elaboration budget.
/-- Cauchy's product identity for arbitrary extended-nonnegative series.  The larger local
heartbeat budget covers the explicit sigma/antidiagonal reindexing. -/
theorem ennrealCauchyProduct (f u : ℕ → ℝ≥0∞) :
    renewalProduct f u = renewalConvolution f u := by
  rw [renewalProduct, ennrealSeriesMass, renewalConvolution]
  calc
    (∑' n, f n) * ∑' n, u n =
        ∑' k, f k * ∑' n, u n := ENNReal.tsum_mul_right.symm
    _ = ∑' k, ∑' n, f k * u n := by
      apply tsum_congr
      intro k
      exact ENNReal.tsum_mul_left.symm
    _ = ∑' p : ℕ × ℕ, f p.1 * u p.2 := ENNReal.tsum_prod.symm
    _ = ∑' c : Σ N, ↥(Finset.antidiagonal N),
        f (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c).1 *
          u (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c).2 :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
        (fun p : ℕ × ℕ => f p.1 * u p.2)).symm
    _ = ∑' c : Σ N, ↥(Finset.antidiagonal N),
        f c.2.1.1 * u c.2.1.2 := by
      apply tsum_congr
      rintro ⟨N, p⟩
      rfl
    _ = ∑' N, ∑' p : ↥(Finset.antidiagonal N), f p.1.1 * u p.1.2 :=
      ENNReal.tsum_sigma'
        (fun c : Σ N, ↥(Finset.antidiagonal N) => f c.2.1.1 * u c.2.1.2)
    _ = ∑' N, ∑ p ∈ Finset.antidiagonal N, f p.1 * u p.2 := by
      apply tsum_congr
      intro N
      rw [← Finset.sum_finset_coe, tsum_fintype]
      rfl
    _ = ∑' N, ∑ k ∈ Finset.range (N + 1), f k * u (N - k) := by
      apply tsum_congr
      intro N
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l => f k * u l) N

private theorem one_add_congr_ennreal {a b : ℝ≥0∞} (h : a = b) : 1 + a = 1 + b :=
  congrArg (fun z : ℝ≥0∞ => 1 + z) h

theorem one_add_renewalConvolution_eq (f u : ℕ → ℝ≥0∞) :
    1 + renewalConvolution f u = 1 + renewalProduct f u :=
  @one_add_congr_ennreal (renewalConvolution f u) (renewalProduct f u)
    (ennrealCauchyProduct f u).symm

/-- A pair of sequences satisfying the renewal recurrence after the zeroth term. -/
def IsRenewalPair (u f : ℕ → ℝ≥0∞) : Prop :=
  (fun N => u (N + 1)) = fun N =>
    ∑ k ∈ Finset.range (N + 1), f k * u (N - k)

theorem ennrealTailMass_eq_renewalConvolution (u f : ℕ → ℝ≥0∞)
    (hrec : IsRenewalPair u f) :
    ennrealTailMass u = renewalConvolution f u := by
  change (fun N => u (N + 1)) = (fun N =>
    ∑ k ∈ Finset.range (N + 1), f k * u (N - k)) at hrec
  have htail0 :
      (∑' N, u (N + 1)) =
        ∑' N, ∑ k ∈ Finset.range (N + 1), f k * u (N - k) :=
    congrArg (fun v : ℕ → ℝ≥0∞ => ∑' N, v N) hrec
  rw [ennrealTailMass]
  exact htail0

theorem ennrealSeriesMass_split (u : ℕ → ℝ≥0∞) :
    ennrealSeriesMass u = u 0 + ennrealTailMass u := by
  change (∑' n, u n) = u 0 + ∑' n, u (n + 1)
  exact tsum_eq_zero_add' (f := u) ENNReal.summable

private theorem renewalAlgebra {U u₀ T C : ℝ≥0∞}
    (hsplit : U = u₀ + T) (hzero : u₀ = 1) (htail : T = C) :
    U = 1 + C := by
  cases hzero
  cases htail
  exact hsplit

/-- Summing a renewal pair gives the extended identity `U = 1 + F * U`. -/
theorem renewalTsumIdentityOfTail (u f : ℕ → ℝ≥0∞)
    (hzero : u 0 = 1)
    (htail : ennrealTailMass u = renewalConvolution f u) :
    ennrealSeriesMass u = 1 + renewalProduct f u :=
  Eq.trans
    (@renewalAlgebra (ennrealSeriesMass u) (u 0) (ennrealTailMass u)
      (renewalConvolution f u) (ennrealSeriesMass_split u) hzero htail)
    (one_add_renewalConvolution_eq f u)

/-- Truncation of a nonnegative sequence to its first `N` terms. -/
def truncateSequence (u : ℕ → ℝ≥0∞) (N n : ℕ) : ℝ≥0∞ :=
  if n < N then u n else 0

/-- The finite convolution step appearing in a renewal recurrence. -/
noncomputable def renewalStep (f u : ℕ → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (N + 1), f k * u (N - k)

theorem ennrealSeriesMass_truncateSequence (u : ℕ → ℝ≥0∞) (N : ℕ) :
    ennrealSeriesMass (truncateSequence u N) =
      ∑ n ∈ Finset.range N, u n := by
  rw [ennrealSeriesMass, tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [truncateSequence, Finset.mem_range.1 hn]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [truncateSequence, hn]

theorem renewalStep_truncateSequence (f u : ℕ → ℝ≥0∞) {n N : ℕ}
    (hnN : n < N) :
    renewalStep f (truncateSequence u N) n = renewalStep f u n := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [truncateSequence, if_pos]
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  omega

/-- The first `N` tail terms of a renewal sequence are bounded by the total renewal mass times
the first `N` terms of the sequence. -/
theorem sum_tail_le_seriesMass_mul_partial
    (u f : ℕ → ℝ≥0∞) (hrec : IsRenewalPair u f) (N : ℕ) :
    (∑ n ∈ Finset.range N, u (n + 1)) ≤
      ennrealSeriesMass f * ∑ n ∈ Finset.range N, u n := by
  rw [IsRenewalPair] at hrec
  have hpoint (n : ℕ) : u (n + 1) = renewalStep f u n :=
    congrFun hrec n
  calc
    (∑ n ∈ Finset.range N, u (n + 1)) =
        ∑ n ∈ Finset.range N, renewalStep f u n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = ∑ n ∈ Finset.range N,
        renewalStep f (truncateSequence u N) n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (renewalStep_truncateSequence f u (Finset.mem_range.1 hn)).symm
    _ ≤ ∑' n, renewalStep f (truncateSequence u N) n :=
      ENNReal.sum_le_tsum (Finset.range N)
    _ = renewalConvolution f (truncateSequence u N) := by rfl
    _ = renewalProduct f (truncateSequence u N) :=
      (ennrealCauchyProduct f (truncateSequence u N)).symm
    _ = ennrealSeriesMass f * ∑ n ∈ Finset.range N, u n := by
      rw [renewalProduct, ennrealSeriesMass_truncateSequence]

/-- Finite partial masses of a renewal sequence are bounded by geometric partial sums. -/
theorem partialMass_le_geometric
    (u f : ℕ → ℝ≥0∞) (hzero : u 0 = 1) (hrec : IsRenewalPair u f) :
    ∀ N, (∑ n ∈ Finset.range N, u n) ≤
      ∑ j ∈ Finset.range N, (ennrealSeriesMass f) ^ j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ']
      rw [hzero]
      calc
        (∑ n ∈ Finset.range N, u (n + 1)) + 1 ≤
            ennrealSeriesMass f * (∑ n ∈ Finset.range N, u n) + 1 :=
          add_le_add (sum_tail_le_seriesMass_mul_partial u f hrec N) le_rfl
        _ ≤ ennrealSeriesMass f *
              (∑ j ∈ Finset.range N, (ennrealSeriesMass f) ^ j) + 1 :=
          add_le_add (by gcongr) le_rfl
        _ = ∑ j ∈ Finset.range (N + 1), (ennrealSeriesMass f) ^ j := by
          rw [Finset.sum_range_succ']
          simp only [pow_zero]
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_succ']

/-- A renewal sequence has finite total mass whenever its renewal mass is strictly below one. -/
theorem ennrealSeriesMass_lt_top_of_mass_lt_one
    (u f : ℕ → ℝ≥0∞) (hzero : u 0 = 1) (hrec : IsRenewalPair u f)
    (hf : ennrealSeriesMass f < 1) :
    ennrealSeriesMass u < ∞ := by
  have hpartial := partialMass_le_geometric u f hzero hrec
  have hle : ennrealSeriesMass u ≤ ∑' j, (ennrealSeriesMass f) ^ j := by
    rw [ennrealSeriesMass, ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro N
    exact (hpartial N).trans (ENNReal.sum_le_tsum (Finset.range N))
  refine hle.trans_lt ?_
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hf)

section Markov

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Diagonal transition masses of the successive powers of a Markov kernel. -/
noncomputable def returnMassSequence (κ : Kernel E E) (x : E) (n : ℕ) : ℝ≥0∞ :=
  (κ ^ n) x {x}

/-- Exact first-return masses under the canonical Markov-chain law. -/
noncomputable def firstReturnMassSequence
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ) : ℝ≥0∞ :=
  markovChainLaw κ x (firstReturnSlice x n)

theorem returnMassSequence_zero
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    returnMassSequence κ x 0 = 1 := by
  rw [returnMassSequence, pow_zero]
  change Kernel.id x {x} = 1
  rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
  simp

/-- The return and first-return sequences satisfy the renewal recurrence. -/
theorem isRenewalPair_markov
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    IsRenewalPair (returnMassSequence κ x) (firstReturnMassSequence κ x) := by
  rw [IsRenewalPair]
  funext N
  exact markovRenewalEquation κ x N

theorem returnSeriesMass_eq_green (κ : Kernel E E) (x : E) :
    ennrealSeriesMass (returnMassSequence κ x) = κ.green x x := by
  rfl

theorem firstReturnSeriesMass_eq_returnProbability
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    ennrealSeriesMass (firstReturnMassSequence κ x) = returnProbability κ x x := by
  exact tsum_firstReturnSlice_eq_returnProbability κ x

/-- The total return mass satisfies `G = 1 + F * G`, with all terms in `ℝ≥0∞`. -/
theorem markovReturnSeries_identity
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    κ.green x x = 1 + returnProbability κ x x * κ.green x x := by
  have htail := ennrealTailMass_eq_renewalConvolution
    (returnMassSequence κ x) (firstReturnMassSequence κ x)
    (isRenewalPair_markov κ x)
  have h := renewalTsumIdentityOfTail
    (returnMassSequence κ x) (firstReturnMassSequence κ x)
    (returnMassSequence_zero κ x) htail
  rw [returnSeriesMass_eq_green,
    renewalProduct, firstReturnSeriesMass_eq_returnProbability,
    returnSeriesMass_eq_green] at h
  exact h

/-- Recurrence forces infinite diagonal Green mass. -/
theorem RecurrentAt.green_eq_top
    (κ : Kernel E E) [IsMarkovKernel κ] {x : E}
    (hx : RecurrentAt κ x) :
    κ.green x x = ⊤ := by
  have h := markovReturnSeries_identity κ x
  rw [hx, one_mul] at h
  by_contra htop
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add ENNReal.one_ne_top htop] at hr
  norm_num at hr

/-- Transience forces finite diagonal Green mass. -/
theorem TransientAt.green_lt_top
    (κ : Kernel E E) [IsMarkovKernel κ] {x : E}
    (hx : TransientAt κ x) :
    κ.green x x < ∞ := by
  rw [← returnSeriesMass_eq_green]
  apply ennrealSeriesMass_lt_top_of_mass_lt_one
  · exact returnMassSequence_zero κ x
  · exact isRenewalPair_markov κ x
  · rw [firstReturnSeriesMass_eq_returnProbability]
    exact hx

/-- A state is recurrent exactly when its diagonal Green mass is infinite. -/
theorem green_eq_top_iff_recurrentAt
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    κ.green x x = ∞ ↔ RecurrentAt κ x := by
  constructor
  · intro htop
    rcases recurrentAt_or_transientAt κ x with hrec | htrans
    · exact hrec
    · exact False.elim ((ne_of_lt (htrans.green_lt_top κ)) htop)
  · exact RecurrentAt.green_eq_top κ

/-- Recurrence propagates across a communicating class. -/
theorem RecurrentAt.of_communicates
    (κ : Kernel E E) [IsMarkovKernel κ] {x y : E}
    (hxy : κ.CanReach x y) (hyx : κ.CanReach y x)
    (hx : RecurrentAt κ x) : RecurrentAt κ y := by
  rw [← green_eq_top_iff_recurrentAt]
  exact Kernel.green_self_eq_top_of_communicates κ hxy hyx
    ((green_eq_top_iff_recurrentAt κ x).2 hx)

end Markov

end ProbabilityTheory
