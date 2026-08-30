/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
import StochLean.Probability.Exchangeability.ConditionalExpectation
import StochLean.Probability.Martingale.Reverse

/-!
# Exchangeable means and reverse martingales

The symmetric mean is first defined by the canonical finite group average.  This makes the
conditional-expectation and reverse-martingale structure transparent; its arithmetic-average
formula is a separate algebraic statement.
-/

open MeasureTheory
open Filter
open scoped Topology ENNReal BigOperators

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

/-- Exchangeable strong law on canonical real sequence space: the sample averages converge almost
surely to the conditional expectation of the first coordinate given the exchangeable sigma-field.
-/
theorem IsExchangeable.tendsto_ae_exchangeableSymmetricMean
    {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => exchangeableSymmetricMean n x) atTop
      (𝓝 (μ[(fun y : ℕ → ℝ => y 0) |
        exchangeableMeasurableSpace (E := ℝ)] x)) := by
  let G : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun n => prefixInvariantMeasurableSpace (E := ℝ) (n + 1)
  have hG : Antitone G := fun _ _ hnm =>
    prefixInvariantMeasurableSpace_antitone (Nat.add_le_add_right hnm 1)
  have hG_le : ∀ n, G n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    fun _ _ hs => hs.1
  have hce := tendsto_ae_condExp_iInf (μ := μ) hG hG_le
    (fun x : ℕ → ℝ => x 0) h0
  have hmean : ∀ᵐ x ∂μ, ∀ n, exchangeableSymmetricMean n x =
      μ[(fun y : ℕ → ℝ => y 0) | G n] x := by
    rw [ae_all_iff]
    exact fun n => hX.exchangeableSymmetricMean_ae_eq_condExp h0 n
  filter_upwards [hce, hmean] with x hx hxm
  rw [iInf_prefixInvariantMeasurableSpace_succ] at hx
  exact hx.congr' (Filter.Eventually.of_forall fun n => (hxm n).symm)

/-- `L¹` form of the exchangeable strong law. -/
theorem IsExchangeable.tendsto_eLpNorm_exchangeableSymmetricMean
    {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) :
    Tendsto (fun n => eLpNorm
      (exchangeableSymmetricMean n -
        μ[(fun y : ℕ → ℝ => y 0) | exchangeableMeasurableSpace (E := ℝ)]) 1 μ)
      atTop (𝓝 0) := by
  let G : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun n => prefixInvariantMeasurableSpace (E := ℝ) (n + 1)
  have hG : Antitone G := fun _ _ hnm =>
    prefixInvariantMeasurableSpace_antitone (Nat.add_le_add_right hnm 1)
  have hG_le : ∀ n, G n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    fun _ _ hs => hs.1
  have hL1 := h0.tendsto_eLpNorm_condExp_iInf hG hG_le
  rw [iInf_prefixInvariantMeasurableSpace_succ] at hL1
  convert hL1 using 1
  funext n
  apply eLpNorm_congr_ae
  exact (hX.exchangeableSymmetricMean_ae_eq_condExp h0 n).sub EventuallyEq.rfl

/-- Arithmetic-average spelling of the almost-sure exchangeable law of large numbers. -/
theorem IsExchangeable.tendsto_ae_sampleAverage
    {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hX : IsExchangeable (fun k (x : ℕ → ℝ) => x k) μ)
    (h0 : Integrable (fun x : ℕ → ℝ => x 0) μ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n => ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (n + 1), x j) atTop
      (𝓝 (μ[(fun y : ℕ → ℝ => y 0) |
        exchangeableMeasurableSpace (E := ℝ)] x)) := by
  simpa only [← exchangeableSymmetricMean_eq_average] using
    hX.tendsto_ae_exchangeableSymmetricMean h0

section FiniteCoordinateStatistic

variable {E : Type*} [MeasurableSpace E]

/-- Extend a statistic of the first `k` coordinates to a longer finite vector.  The proof
argument is part of the definition so that no value outside the natural domain is ever selected. -/
def extendPrefixStatistic {k n : ℕ} (hkn : k ≤ n) (φ : (Fin k → E) → ℝ) :
    (Fin n → E) → ℝ := fun x => φ (fun j => x (Fin.castLEEmb hkn j))

theorem measurable_extendPrefixStatistic {k n : ℕ} (hkn : k ≤ n)
    {φ : (Fin k → E) → ℝ} (hφ : Measurable φ) :
    Measurable (extendPrefixStatistic hkn φ) := by
  apply hφ.comp
  rw [measurable_pi_iff]
  exact fun j => measurable_pi_apply (Fin.castLEEmb hkn j)

/-- Klenke's finite-coordinate symmetrization `Aₙ φ`.  Before the statistic's support fits in
the prefix the value is set to zero; every convergence theorem below uses only the cofinal
natural domain `k ≤ n`. -/
noncomputable def prefixSymmetrization {k : ℕ} (φ : (Fin k → E) → ℝ)
    (n : ℕ) (x : ℕ → E) : ℝ :=
  if hkn : k ≤ n then
    finiteSymmetrization (extendPrefixStatistic hkn φ)
      (prefixCoordinates (E := E) n x)
  else 0

theorem IsExchangeable.prefixSymmetrization_ae_eq_condExp
    {k n : ℕ} {μ : Measure (ℕ → E)} [IsFiniteMeasure μ]
    (hX : IsExchangeable (fun j (x : ℕ → E) => x j) μ)
    (φ : (Fin k → E) → ℝ) (hφm : Measurable φ)
    (hφ : Integrable (φ ∘ prefixCoordinates (E := E) k) μ)
    (hkn : k ≤ n) :
    prefixSymmetrization φ n =ᵐ[μ]
      μ[φ ∘ prefixCoordinates (E := E) k |
        prefixInvariantMeasurableSpace (E := E) n] := by
  have hcomp : extendPrefixStatistic hkn φ ∘ prefixCoordinates (E := E) n =
      φ ∘ prefixCoordinates (E := E) k := by
    rfl
  have h := hX.finiteSymmetrization_ae_eq_condExp
    (extendPrefixStatistic hkn φ) (measurable_extendPrefixStatistic hkn hφm)
    (hcomp ▸ hφ)
  have hpref : prefixSymmetrization φ n =
      finiteSymmetrization (extendPrefixStatistic hkn φ) ∘
        prefixCoordinates (E := E) n := by
    funext x
    simp [prefixSymmetrization, hkn]
  rw [hpref]
  simpa only [hcomp] using h

/-- Symmetrized law of large numbers for an integrable measurable statistic depending on a
finite coordinate prefix.  It is a direct corollary of the same Levy-downward engine used by
exchangeable means; no reverse upcrossing or convergence stack is duplicated. -/
theorem IsExchangeable.tendsto_ae_prefixSymmetrization
    {k : ℕ} {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]
    (hX : IsExchangeable (fun j (x : ℕ → E) => x j) μ)
    (φ : (Fin k → E) → ℝ) (hφm : Measurable φ)
    (hφ : Integrable (φ ∘ prefixCoordinates (E := E) k) μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => prefixSymmetrization φ n x) atTop
      (𝓝 (μ[φ ∘ prefixCoordinates (E := E) k |
        exchangeableMeasurableSpace (E := E)] x)) := by
  have hce := tendsto_ae_condExp_iInf
    (prefixInvariantMeasurableSpace_antitone (E := E))
    (fun _ _ hs => hs.1) (φ ∘ prefixCoordinates (E := E) k) hφ
  have hsymm : ∀ᵐ x ∂μ, ∀ n, k ≤ n →
      prefixSymmetrization φ n x =
        μ[φ ∘ prefixCoordinates (E := E) k |
          prefixInvariantMeasurableSpace (E := E) n] x := by
    rw [ae_all_iff]
    intro n
    by_cases hkn : k ≤ n
    · exact (hX.prefixSymmetrization_ae_eq_condExp φ hφm hφ hkn).mono
        (fun x hx _ => hx)
    · exact ae_of_all μ fun _ h => (hkn h).elim
  filter_upwards [hce, hsymm] with x hx hxs
  exact hx.congr' (eventually_atTop.2 ⟨k, fun n hn => (hxs n hn).symm⟩)

end FiniteCoordinateStatistic

end ProbabilityTheory
