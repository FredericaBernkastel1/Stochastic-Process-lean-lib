/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the source file header.
Adapted for StochLean from statopia/statlean4 revision
dd2c4bbc72b7c643e62985d77c84755b31aec9f5.
Authors: StatLean contributors; StochLean adaptation
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Internal characteristic-function bounds

These are implementation lemmas for the triangular-array central limit theorem. They are kept
below the public StochLean API because their constants and proof decomposition are not part of the
library's mathematical interface.
-/

@[expose] public section

namespace StochLean.Internal.LimitTheorems

private lemma norm_ofReal_mul_I (θ : ℝ) : ‖(↑θ * Complex.I : ℂ)‖ = |θ| := by
  rw [Complex.norm_mul, Complex.norm_I, mul_one]
  exact Complex.norm_real θ

/-- A global quadratic-Taylor remainder bound for the complex exponential on the imaginary axis. -/
lemma norm_cexp_sub_quadratic_le (θ : ℝ) :
    ‖Complex.exp (↑θ * Complex.I) -
      ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖ ≤ 4 * |θ| ^ 3 := by
  by_cases hθ : |θ| ≤ 1
  · have hx : ‖(↑θ * Complex.I : ℂ)‖ ≤ 1 := by
      rw [norm_ofReal_mul_I]
      exact hθ
    have key := Complex.exp_bound hx (n := 3) (by norm_num)
    have sum_eq : ∑ m ∈ Finset.range 3, (↑θ * Complex.I) ^ m / ↑(Nat.factorial m) =
        (1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination (θ : ℂ) ^ 2 * (1 / 2) * hI
    rw [sum_eq] at key
    calc
      ‖Complex.exp (↑θ * Complex.I) -
          ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖
          ≤ ‖(↑θ * Complex.I : ℂ)‖ ^ 3 *
            (↑(Nat.succ 3) * (↑(Nat.factorial 3) * ↑(3 : ℕ))⁻¹) := key
      _ = |θ| ^ 3 * (4 * (6 * 3)⁻¹) := by
        rw [norm_ofReal_mul_I]
        norm_num
      _ ≤ 4 * |θ| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg θ) 3]
  · push_neg at hθ
    calc
      ‖Complex.exp (↑θ * Complex.I) -
          ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖
          ≤ ‖Complex.exp (↑θ * Complex.I)‖ +
            ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |θ| + θ ^ 2 / 2) := by
        gcongr
        · rw [Complex.norm_exp_ofReal_mul_I]
        · calc
            ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖
                ≤ ‖(1 : ℂ) + ↑θ * Complex.I‖ + ‖(↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
            _ ≤ (‖(1 : ℂ)‖ + ‖↑θ * Complex.I‖) + ‖(↑θ : ℂ) ^ 2 / 2‖ := by
              gcongr
              exact norm_add_le _ _
            _ = 1 + |θ| + θ ^ 2 / 2 := by
              rw [norm_ofReal_mul_I]
              simp
      _ ≤ 4 * |θ| ^ 3 := by
        nlinarith [sq_abs θ, sq_nonneg θ, sq_nonneg (|θ| - 1), abs_nonneg θ]

/-- A finite-product telescoping bound with a common norm bound. -/
lemma norm_prod_sub_prod_le_sum_mul_pow :
    ∀ {n : ℕ} (z w : Fin n → ℂ) (M : ℝ),
      0 ≤ M →
      (∀ i, ‖z i‖ ≤ M) →
      (∀ i, ‖w i‖ ≤ M) →
      ‖∏ i, z i - ∏ i, w i‖ ≤ M ^ (n - 1) * ∑ i, ‖z i - w i‖ := by
  intro n
  induction n with
  | zero =>
      intro z w M _ _ _
      simp
  | succ n ih =>
      intro z w M hM hz hw
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      set a := ∏ i : Fin n, z (Fin.castSucc i)
      set b := z (Fin.last n)
      set c := ∏ i : Fin n, w (Fin.castSucc i)
      set d := w (Fin.last n)
      have key : a * b - c * d = (a - c) * b + c * (b - d) := by ring
      rw [key]
      have hc_le : ‖c‖ ≤ M ^ n := by
        calc
          ‖c‖ = ‖∏ i : Fin n, w (Fin.castSucc i)‖ := rfl
          _ ≤ ∏ i : Fin n, ‖w (Fin.castSucc i)‖ := Finset.norm_prod_le Finset.univ _
          _ ≤ ∏ _i : Fin n, M :=
            Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hw (Fin.castSucc i))
          _ = M ^ n := by rw [Finset.prod_const, Finset.card_fin]
      have hih := ih (fun i ↦ z (Fin.castSucc i)) (fun i ↦ w (Fin.castSucc i)) M hM
        (fun i ↦ hz (Fin.castSucc i)) (fun i ↦ hw (Fin.castSucc i))
      simp only [Nat.succ_sub_one]
      calc
        ‖(a - c) * b + c * (b - d)‖
            ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
              calc
                _ ≤ ‖(a - c) * b‖ + ‖c * (b - d)‖ := norm_add_le _ _
                _ ≤ _ := by gcongr <;> exact norm_mul_le _ _
        _ ≤ (M ^ (n - 1) *
              ∑ i : Fin n, ‖z (Fin.castSucc i) - w (Fin.castSucc i)‖) * M +
              M ^ n * ‖b - d‖ := by
          apply add_le_add
          · apply mul_le_mul hih (hz (Fin.last n)) (norm_nonneg _)
            exact mul_nonneg (pow_nonneg hM _) (Finset.sum_nonneg (fun i _ ↦ norm_nonneg _))
          · exact mul_le_mul_of_nonneg_right hc_le (norm_nonneg _)
        _ = M ^ n *
              ((∑ i : Fin n, ‖z (Fin.castSucc i) - w (Fin.castSucc i)‖) +
                ‖z (Fin.last n) - w (Fin.last n)‖) := by
          cases n with
          | zero => simp [Fin.last, b, d]
          | succ m =>
              simp only [Nat.succ_sub_one]
              ring

/-- Characteristic function of the standard real Gaussian law. -/
lemma charFun_standardGaussian (t : ℝ) :
    MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 1) t =
      Complex.exp (-(↑(t ^ 2) / 2)) := by
  rw [ProbabilityTheory.charFun_gaussianReal]
  congr 1
  push_cast
  ring

end StochLean.Internal.LimitTheorems
