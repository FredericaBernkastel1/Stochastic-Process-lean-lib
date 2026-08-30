/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Exchangeability.ConditionalExpectation
public import StochLean.Probability.Martingale.Reverse

/-!
# Exchangeable means and reverse martingales

The symmetric mean is first defined by the canonical finite group average.  This makes the
conditional-expectation and reverse-martingale structure transparent; its arithmetic-average
formula is a separate algebraic statement.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- The first-coordinate statistic on a positive finite sample. -/
def firstCoordinateStatistic (n : ℕ) : (Fin (n + 1) → ℝ) → ℝ := fun x => x 0

theorem measurable_firstCoordinateStatistic (n : ℕ) :
    Measurable (firstCoordinateStatistic n) := measurable_pi_apply 0

/-- Finite group symmetrization of one coordinate is the ordinary arithmetic average. -/
theorem finiteSymmetrization_firstCoordinate_eq_average (n : ℕ) (x : Fin (n + 1) → ℝ) :
    finiteSymmetrization (firstCoordinateStatistic n) x =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, x j := by
  let a : Fin (n + 1) := 0
  let S : Fin (n + 1) → ℝ := fun j => ∑ σ : Equiv.Perm (Fin (n + 1)), x (σ j)
  have hS : ∀ j, S j = S a := by
    intro j
    let e : Equiv.Perm (Equiv.Perm (Fin (n + 1))) :=
      Equiv.mulRight (Equiv.swap a j)
    simp only [S]
    rw [← e.sum_comp]
    · apply Fintype.sum_congr
      intro σ
      simp [e, a]
    · simp
  have hleft : ∑ j, S j = (Fintype.card (Fin (n + 1)) : ℝ) * S a := by
    simp_rw [hS]
    simp
  have hright : ∑ j, S j =
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) * ∑ j, x j := by
    simp only [S]
    rw [Finset.sum_comm]
    have hinner : ∀ σ : Equiv.Perm (Fin (n + 1)), ∑ j, x (σ j) = ∑ j, x j :=
      fun σ => Equiv.sum_comp σ x
    simp_rw [hinner]
    simp
  have heq : (Fintype.card (Fin (n + 1)) : ℝ) * S a =
      (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) * ∑ j, x j :=
    hleft.symm.trans hright
  have hc : (Fintype.card (Fin (n + 1)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [finiteSymmetrization]
  change (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ)⁻¹ * S a =
    ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, x j
  rw [inv_mul_eq_div, inv_mul_eq_div]
  have hdiv : S a / (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) =
      (∑ j, x j) / (Fintype.card (Fin (n + 1)) : ℝ) :=
    (div_eq_div_iff hp hc).2 (by simpa [mul_comm] using heq)
  simpa using hdiv

/-- Exchangeable sample mean represented as the finite symmetrization of one coordinate. -/
noncomputable def exchangeableSymmetricMean (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  finiteSymmetrization (firstCoordinateStatistic n)
    (prefixCoordinates (E := ℝ) (n + 1) x)

theorem exchangeableSymmetricMean_eq_average (n : ℕ) (x : ℕ → ℝ) :
    exchangeableSymmetricMean n x =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1), x j :=
  finiteSymmetrization_firstCoordinate_eq_average n
    (prefixCoordinates (E := ℝ) (n + 1) x)

/-- Under an exchangeable canonical law, the symmetric mean is the conditional expectation of
the first coordinate with respect to the decreasing invariant sigma-field. -/
theorem IsExchangeable.exchangeableSymmetricMean_ae_eq_condExp
    {μ : Measure (ℕ → ℝ)} [IsFiniteMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) (n : ℕ) :
    exchangeableSymmetricMean n =ᵐ[μ]
      μ[(fun x : ℕ → ℝ => x 0) |
        prefixInvariantMeasurableSpace (E := ℝ) (n + 1)] := by
  change finiteSymmetrization (firstCoordinateStatistic n) ∘
      prefixCoordinates (E := ℝ) (n + 1) =ᵐ[μ]
    μ[firstCoordinateStatistic n ∘ prefixCoordinates (E := ℝ) (n + 1) |
      prefixInvariantMeasurableSpace (E := ℝ) (n + 1)]
  exact hX.finiteSymmetrization_ae_eq_condExp (firstCoordinateStatistic n)
    (measurable_firstCoordinateStatistic n) h0

/-- The exchangeable symmetric means form a reverse martingale.  The proof is only a congruence
bridge to Mathlib's ordinary conditional-expectation martingale on `OrderDual ℕ`. -/
theorem IsExchangeable.reverseMartingale_exchangeableSymmetricMean
    {μ : Measure (ℕ → ℝ)} [IsFiniteMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) :
    ReverseMartingale
      (fun n : OrderDual ℕ => exchangeableSymmetricMean n)
      (fun n => prefixInvariantMeasurableSpace (E := ℝ) (n + 1))
      (fun _ _ hnm => prefixInvariantMeasurableSpace_antitone (Nat.add_le_add_right hnm 1))
      (fun _ _ hs => hs.1) μ := by
  let G : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun n => prefixInvariantMeasurableSpace (E := ℝ) (n + 1)
  have hG : Antitone G := fun _ _ hnm =>
    prefixInvariantMeasurableSpace_antitone (Nat.add_le_add_right hnm 1)
  have hG_le : ∀ n, G n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    fun _ _ hs => hs.1
  have hcond := reverseMartingale_condExp (fun x : ℕ → ℝ => x 0) G hG hG_le μ
  change Martingale (fun n : OrderDual ℕ => exchangeableSymmetricMean n)
    (antitoneFiltration G hG hG_le) μ
  apply hcond.congr
  · intro n
    exact stronglyMeasurable_finiteSymmetrization_prefix
      (firstCoordinateStatistic n) (measurable_firstCoordinateStatistic n)
  · intro n
    exact (hX.exchangeableSymmetricMean_ae_eq_condExp h0 n).symm

/-- Automatic uniform integrability of exchangeable means, inherited from the canonical
conditional-expectation family. -/
theorem IsExchangeable.uniformIntegrable_exchangeableSymmetricMean
    {μ : Measure (ℕ → ℝ)} [IsFiniteMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) :
    UniformIntegrable exchangeableSymmetricMean 1 μ := by
  have hUI := h0.uniformIntegrable_condExp
    (ℱ := fun n => prefixInvariantMeasurableSpace (E := ℝ) (n + 1))
    (fun _ _ hs => hs.1)
  exact hUI.ae_eq fun n =>
    (hX.exchangeableSymmetricMean_ae_eq_condExp h0 n).symm

end ProbabilityTheory
