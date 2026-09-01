/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import StochLean.Probability.InfinitelyDivisible.LevyKhintchine

/-!
# Stable probability laws

Stable laws are predicates on canonical probability measures.  Nondegeneracy is primitive, broad
and strict stability are distinct, and positive scaling is explicit before reciprocal powers are
used.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory.ProbabilityMeasure

/-- Pushforward of a real law by a positive-affine map. -/
noncomputable def affineMap (a d : ℝ) (μ : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  μ.map (by fun_prop : AEMeasurable (fun x : ℝ ↦ a * x + d) μ)

@[simp, norm_cast]
theorem coe_affineMap (a d : ℝ) (μ : ProbabilityMeasure ℝ) :
    ((affineMap a d μ : ProbabilityMeasure ℝ) : Measure ℝ) =
      (μ : Measure ℝ).map (fun x ↦ a * x + d) :=
  rfl

@[simp]
theorem affineMap_pointMass (a d x : ℝ) :
    affineMap a d (pointMass x) = pointMass (a * x + d) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_affineMap, coe_pointMass]
  rw [Measure.map_dirac]

@[simp]
theorem affineMap_one_zero (μ : ProbabilityMeasure ℝ) : affineMap 1 0 μ = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [coe_affineMap]

/-- Composition law for affine pushforwards. -/
theorem affineMap_comp (a d b e : ℝ) (μ : ProbabilityMeasure ℝ) :
    affineMap a d (affineMap b e μ) = affineMap (a * b) (a * e + d) μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_affineMap]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

/-- A common affine scale distributes over convolution, while the translations add. -/
theorem conv_affineMap (a d e : ℝ) (μ ν : ProbabilityMeasure ℝ) :
    conv (affineMap a d μ) (affineMap a e ν) = affineMap a (d + e) (conv μ ν) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coe_conv, coe_affineMap]
  unfold Measure.conv
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  rcases x with ⟨x, y⟩
  simp only [Function.comp_apply, Prod.map]
  ring

/-- Convolution powers commute with a common affine transformation; the translation accumulates
linearly with the number of summands. -/
theorem convPow_affineMap (a d : ℝ) (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    convPow (affineMap a d μ) n = affineMap a (n * d) (convPow μ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [convPow_succ, convPow_succ, ih, conv_affineMap]
      congr 2
      push_cast
      ring

/-- Characteristic function of the affine image, with the source frequency scaled by `a`. -/
theorem charFun_affineMap (a d : ℝ) (μ : ProbabilityMeasure ℝ) (t : ℝ) :
    charFun (affineMap a d μ : Measure ℝ) t =
      charFun (μ : Measure ℝ) (a * t) *
        Complex.exp (((d * t : ℝ) : ℂ) * Complex.I) := by
  rw [coe_affineMap]
  have hmap : (μ : Measure ℝ).map (fun x => a * x + d) =
      ((μ : Measure ℝ).map (fun x => a * x)).map (fun x => x + d) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  rw [hmap, charFun_map_add_const, charFun_map_mul]
  congr 1
  rw [Real.inner_apply]

/-- A law is nondegenerate when it is not any Dirac law. -/
def IsNonDirac (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, μ ≠ pointMass x

/-- Stability in the broad sense, with strictly positive affine scaling. -/
def IsStableInBroadSense (μ : ProbabilityMeasure ℝ) : Prop :=
  IsNonDirac μ ∧
    ∀ n : ℕ, 0 < n → ∃ a : ℝ, 0 < a ∧ ∃ d : ℝ, convPow μ n = affineMap a d μ

/-- Strict stability: no centering term is allowed. -/
def IsStable (μ : ProbabilityMeasure ℝ) : Prop :=
  IsNonDirac μ ∧
    ∀ n : ℕ, 0 < n → ∃ a : ℝ, 0 < a ∧ convPow μ n = affineMap a 0 μ

/-- Broad stability with the prescribed index scaling `n^(1/α)`. -/
def IsStableInBroadSenseWithIndex (α : ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ IsNonDirac μ ∧
    ∀ n : ℕ, 0 < n → ∃ d : ℝ,
      convPow μ n = affineMap ((n : ℝ) ^ (1 / α)) d μ

/-- Strict indexed stability. -/
def IsStableWithIndex (α : ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ IsNonDirac μ ∧
    ∀ n : ℕ, 0 < n →
      convPow μ n = affineMap ((n : ℝ) ^ (1 / α)) 0 μ

theorem IsStable.isStableInBroadSense {μ : ProbabilityMeasure ℝ} (hμ : IsStable μ) :
    IsStableInBroadSense μ := by
  refine ⟨hμ.1, ?_⟩
  intro n hn
  obtain ⟨a, ha, hpow⟩ := hμ.2 n hn
  exact ⟨a, ha, 0, hpow⟩

theorem IsStableWithIndex.isStableInBroadSenseWithIndex {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : IsStableWithIndex α μ) : IsStableInBroadSenseWithIndex α μ := by
  refine ⟨hμ.1, hμ.2.1, hμ.2.2.1, ?_⟩
  intro n hn
  exact ⟨0, hμ.2.2.2 n hn⟩

theorem IsStableInBroadSenseWithIndex.isStableInBroadSense
    {α : ℝ} {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSenseWithIndex α μ) :
    IsStableInBroadSense μ := by
  refine ⟨hμ.2.2.1, ?_⟩
  intro n hn
  obtain ⟨d, hd⟩ := hμ.2.2.2 n hn
  refine ⟨(n : ℝ) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, d, hd⟩

theorem IsStableWithIndex.isStable {α : ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : IsStableWithIndex α μ) : IsStable μ := by
  refine ⟨hμ.2.2.1, ?_⟩
  intro n hn
  exact ⟨(n : ℝ) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, hμ.2.2.2 n hn⟩

/-- Every nondegenerate stable law in the broad sense is infinitely divisible. The root is the
inverse affine image of the stability witness, with the translation divided among the `n`
summands. -/
theorem IsStableInBroadSense.isInfinitelyDivisible {μ : ProbabilityMeasure ℝ}
    (hμ : IsStableInBroadSense μ) : IsInfinitelyDivisible μ := by
  intro n hn
  obtain ⟨a, ha, d, hpow⟩ := hμ.2 n hn
  have ha0 : a ≠ 0 := ha.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  let c : ℝ := -(d / ((n : ℝ) * a))
  refine ⟨affineMap a⁻¹ c μ, ?_⟩
  rw [convPow_affineMap, hpow, affineMap_comp]
  have hscale : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have hshift : a⁻¹ * d + (n : ℝ) * c = 0 := by
    dsimp [c]
    field_simp
    ring
  rw [hscale, hshift, affineMap_one_zero]

theorem IsStable.isInfinitelyDivisible {μ : ProbabilityMeasure ℝ} (hμ : IsStable μ) :
    IsInfinitelyDivisible μ :=
  hμ.isStableInBroadSense.isInfinitelyDivisible

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

namespace LevyTriplet

/-- Representation is preserved by the canonical positive affine triplet transformation. -/
theorem Represents.affine {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (h : η.Represents μ) (a d : ℝ) (ha : 0 < a) :
    (η.affine a d ha).Represents (ProbabilityMeasure.affineMap a d μ) := by
  intro t
  rw [ProbabilityMeasure.charFun_affineMap, h (a * t), exponent_affine,
    Complex.exp_add]

/-- Uniqueness turns equality of a convolution power with an affine image into equality of the
two canonically transformed triplets. -/
theorem nsmul_eq_affine_of_convPow_eq_affine
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (n : ℕ) (a d : ℝ) (ha : 0 < a)
    (hunique : HasUniqueLevyTriplet (ProbabilityMeasure.affineMap a d μ))
    (hη : η.Represents μ)
    (hpow : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap a d μ) :
    η.nsmul n = η.affine a d ha := by
  have hn := hη.nsmul n
  have haff := hη.affine a d ha
  rw [hpow] at hn
  exact hunique.unique hn haff

theorem gaussian_scaling_of_convPow_eq_affine
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (n : ℕ) (a d : ℝ) (ha : 0 < a)
    (hunique : HasUniqueLevyTriplet (ProbabilityMeasure.affineMap a d μ))
    (hη : η.Represents μ)
    (hpow : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap a d μ) :
    (a ^ 2 - n) * (η.gaussianVariance : ℝ) = 0 := by
  have htriplet := nsmul_eq_affine_of_convPow_eq_affine n a d ha hunique hη hpow
  have hvariance := congrArg (fun ξ : LevyTriplet => (ξ.gaussianVariance : ℝ)) htriplet
  simp only [nsmul_gaussianVariance, affine_gaussianVariance, NNReal.coe_mul,
    NNReal.coe_pow, Real.coe_toNNReal _ ha.le, nsmul_eq_mul] at hvariance
  push_cast at hvariance
  calc
    (a ^ 2 - n) * (η.gaussianVariance : ℝ) =
        a ^ 2 * (η.gaussianVariance : ℝ) - n * (η.gaussianVariance : ℝ) := by ring
    _ = 0 := sub_eq_zero.mpr hvariance.symm

theorem jumpMeasure_scaling_of_convPow_eq_affine
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (n : ℕ) (a d : ℝ) (ha : 0 < a)
    (hunique : HasUniqueLevyTriplet (ProbabilityMeasure.affineMap a d μ))
    (hη : η.Represents μ)
    (hpow : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap a d μ) :
    (n : ℝ≥0) • η.jumpMeasure = η.jumpMeasure.map (fun x => a * x) := by
  have htriplet := nsmul_eq_affine_of_convPow_eq_affine n a d ha hunique hη hpow
  exact congrArg LevyTriplet.jumpMeasure htriplet

theorem drift_scaling_of_convPow_eq_affine
    {η : LevyTriplet} {μ : ProbabilityMeasure ℝ}
    (n : ℕ) (a d : ℝ) (ha : 0 < a)
    (hunique : HasUniqueLevyTriplet (ProbabilityMeasure.affineMap a d μ))
    (hη : η.Represents μ)
    (hpow : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap a d μ) :
    n * η.drift = a * η.drift + d +
      ∫ x, affineDriftIntegrand a x ∂η.jumpMeasure := by
  have htriplet := nsmul_eq_affine_of_convPow_eq_affine n a d ha hunique hη hpow
  simpa only [nsmul_drift, affine_drift, nsmul_eq_mul] using
    congrArg LevyTriplet.drift htriplet

end LevyTriplet

/-- The `sign(t) log |t|` combination with its mathematically explicit value at zero. -/
noncomputable def signedLogAbs (t : ℝ) : ℝ :=
  if t = 0 then 0 else SignType.sign t * Real.log |t|

@[simp]
theorem signedLogAbs_zero : signedLogAbs 0 = 0 := by
  simp [signedLogAbs]

theorem signedLogAbs_of_ne {t : ℝ} (ht : t ≠ 0) :
    signedLogAbs t = SignType.sign t * Real.log |t| := by
  simp [signedLogAbs, ht]

end ProbabilityTheory
