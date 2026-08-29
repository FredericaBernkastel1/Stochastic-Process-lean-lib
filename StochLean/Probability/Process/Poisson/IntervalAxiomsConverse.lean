/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import StochLean.Probability.Process.Poisson.IntervalAxioms

/-!
# Foundations for the converse Poisson interval characterization

This file develops the analytic part of the converse direction of Klenke, Theorem 5.34.  The
stationary additive interval mean is shown to be linear, Markov's inequality supplies the missing
boundedness for P5, and the exact `limsup` axiom is upgraded to a genuine right-hand limit.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {X : NNReal → Ω → ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

namespace SatisfiesPoissonIntervalAxioms

/-- The expected count in an interval of length `t`. -/
noncomputable def intervalMean (_hX : SatisfiesPoissonIntervalAxioms X P)
    (t : NNReal) : ℝ :=
  ∫ ω, (poissonIntervalCount X 0 t ω : ℝ) ∂P

theorem intervalMean_nonneg (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    0 ≤ hX.intervalMean t := by
  exact integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)

theorem intervalMean_add (hX : SatisfiesPoissonIntervalAxioms X P) (s t : NNReal) :
    hX.intervalMean (s + t) = hX.intervalMean s + hX.intervalMean t := by
  have hadd := hX.intervalAdditive 0 s (s + t) bot_le (by exact le_add_right le_rfl)
  have hcast : (fun ω ↦ (poissonIntervalCount X 0 (s + t) ω : ℝ)) =ᵐ[P]
      fun ω ↦ (poissonIntervalCount X 0 s ω : ℝ) +
        (poissonIntervalCount X s (s + t) ω : ℝ) :=
    hadd.mono fun ω hω ↦ by
      change (poissonIntervalCount X 0 (s + t) ω : ℝ) =
        (poissonIntervalCount X 0 s ω : ℝ) +
          (poissonIntervalCount X s (s + t) ω : ℝ)
      exact_mod_cast hω
  have hstat := hX.stationaryIntervalLaw 0 t s (s + t) bot_le
    (by exact le_add_right le_rfl) (by simp)
  have hstatReal := hstat.comp (measurable_of_countable fun n : ℕ ↦ (n : ℝ))
  have hstatIntegral := hstatReal.integral_eq
  change (∫ ω, (poissonIntervalCount X 0 t ω : ℝ) ∂P) =
    ∫ ω, (poissonIntervalCount X s (s + t) ω : ℝ) ∂P at hstatIntegral
  rw [intervalMean]
  calc
    (∫ ω, (poissonIntervalCount X 0 (s + t) ω : ℝ) ∂P) =
        ∫ ω, ((poissonIntervalCount X 0 s ω : ℝ) +
          (poissonIntervalCount X s (s + t) ω : ℝ)) ∂P := integral_congr_ae hcast
    _ = (∫ ω, (poissonIntervalCount X 0 s ω : ℝ) ∂P) +
        ∫ ω, (poissonIntervalCount X s (s + t) ω : ℝ) ∂P :=
      integral_add (hX.finiteMean 0 s bot_le) (hX.finiteMean s (s + t)
        (by exact le_add_right le_rfl))
    _ = (∫ ω, (poissonIntervalCount X 0 s ω : ℝ) ∂P) +
        ∫ ω, (poissonIntervalCount X 0 t ω : ℝ) ∂P := by
      rw [← hstatIntegral]

theorem intervalMean_nsmul (hX : SatisfiesPoissonIntervalAxioms X P)
    (t : NNReal) (n : ℕ) : hX.intervalMean (n • t) = n • hX.intervalMean t := by
  induction n with
  | zero => simp [intervalMean, poissonIntervalCount]
  | succ n ih => rw [succ_nsmul, hX.intervalMean_add, ih, succ_nsmul]

theorem intervalMean_mono (hX : SatisfiesPoissonIntervalAxioms X P) :
    Monotone hX.intervalMean := by
  intro s t hst
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  rw [hX.intervalMean_add]
  exact le_add_of_nonneg_right (hX.intervalMean_nonneg u)

theorem intervalMean_div_nat (hX : SatisfiesPoissonIntervalAxioms X P)
    (t : NNReal) {n : ℕ} (hn : 0 < n) :
    hX.intervalMean (t / n) = hX.intervalMean t / n := by
  have hscale := hX.intervalMean_nsmul (t / n) n
  have ht : n • (t / n) = t := by
    ext
    simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_div]
    field_simp
  rw [ht] at hscale
  rw [nsmul_eq_mul] at hscale
  rw [eq_div_iff (by exact_mod_cast hn.ne')]
  simpa only [Nat.cast_ofNat, mul_comm] using hscale.symm

theorem intervalMean_nat_div_nat (hX : SatisfiesPoissonIntervalAxioms X P)
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    hX.intervalMean ((m : NNReal) / n) =
      ((m : ℝ) / n) * hX.intervalMean 1 := by
  have harg : (m : NNReal) / n = m • ((1 : NNReal) / n) := by
    ext
    simp [nsmul_eq_mul, div_eq_mul_inv]
  rw [harg, hX.intervalMean_nsmul, hX.intervalMean_div_nat 1 hn]
  simp only [nsmul_eq_mul]
  ring

/-- Stationarity and additivity force the expected count to be linear in the
interval length.  This is the Cauchy-equation step in the converse direction
of Klenke, Theorem 5.34. -/
theorem intervalMean_linear (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    hX.intervalMean t = (t : ℝ) * hX.intervalMean 1 := by
  let lower : ℕ → NNReal := fun n ↦
    (⌊(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : NNReal) / ((n + 1 : ℕ) : NNReal)
  let upper : ℕ → NNReal := fun n ↦
    (⌈(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌉₊ : NNReal) / ((n + 1 : ℕ) : NNReal)
  have hindex : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlower_tendsto : Tendsto (fun n ↦ (lower n : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hraw := (tendsto_nat_floor_mul_div_atTop (R := ℝ) t.2).comp hindex
    change Tendsto (fun n : ℕ ↦
      (⌊(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (t : ℝ)) at hraw
    simpa only [lower, NNReal.coe_div, NNReal.coe_natCast] using hraw
  have hupper_tendsto : Tendsto (fun n ↦ (upper n : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hraw := (tendsto_nat_ceil_mul_div_atTop (R := ℝ) t.2).comp hindex
    change Tendsto (fun n : ℕ ↦
      (⌈(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (t : ℝ)) at hraw
    simpa only [upper, NNReal.coe_div, NNReal.coe_natCast] using hraw
  have hlower_le (n : ℕ) : lower n ≤ t := by
    apply NNReal.coe_le_coe.mp
    simp only [lower, NNReal.coe_div, Nat.cast_add, Nat.cast_one, NNReal.coe_natCast]
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (mul_nonneg t.2 (by positivity))
  have hle_upper (n : ℕ) : t ≤ upper n := by
    apply NNReal.coe_le_coe.mp
    simp only [upper, NNReal.coe_div, Nat.cast_add, Nat.cast_one, NNReal.coe_natCast]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  apply le_antisymm
  · apply ge_of_tendsto (hupper_tendsto.mul_const (hX.intervalMean 1))
    exact Eventually.of_forall fun n ↦ by
      have hmean : hX.intervalMean (upper n) =
          (upper n : ℝ) * hX.intervalMean 1 := by
        change hX.intervalMean
          ((⌈(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌉₊ : NNReal) / ((n + 1 : ℕ) : NNReal)) =
            ((⌈(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℝ) / ((n + 1 : ℕ) : ℝ)) *
              hX.intervalMean 1
        exact hX.intervalMean_nat_div_nat
          ⌈(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌉₊ (Nat.succ_pos n)
      rw [← hmean]
      exact hX.intervalMean_mono (hle_upper n)
  · apply le_of_tendsto (hlower_tendsto.mul_const (hX.intervalMean 1))
    exact Eventually.of_forall fun n ↦ by
      have hmean : hX.intervalMean (lower n) =
          (lower n : ℝ) * hX.intervalMean 1 := by
        change hX.intervalMean
          ((⌊(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : NNReal) / ((n + 1 : ℕ) : NNReal)) =
            ((⌊(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ)) *
              hX.intervalMean 1
        exact hX.intervalMean_nat_div_nat
          ⌊(t : ℝ) * ((n + 1 : ℕ) : ℝ)⌋₊ (Nat.succ_pos n)
      rw [← hmean]
      exact hX.intervalMean_mono (hlower_le n)

/-- The candidate rate in Klenke's converse characterization. -/
noncomputable def intervalIntensity (hX : SatisfiesPoissonIntervalAxioms X P) : NNReal :=
  ⟨hX.intervalMean 1, hX.intervalMean_nonneg 1⟩

@[simp]
theorem coe_intervalIntensity (hX : SatisfiesPoissonIntervalAxioms X P) :
    (hX.intervalIntensity : ℝ) = hX.intervalMean 1 := rfl

/-- Markov's inequality bounds the probability of two or more jumps by half
the expected count. -/
theorem measure_two_le_half_intervalMean
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    P.real {ω | 2 ≤ poissonIntervalCount X 0 t ω} ≤ hX.intervalMean t / 2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω ↦ (poissonIntervalCount X 0 t ω : ℝ))
    (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
    (hX.finiteMean 0 t bot_le) 2
  have hset : {ω | (2 : ℝ) ≤ (poissonIntervalCount X 0 t ω : ℝ)} =
      {ω | 2 ≤ poissonIntervalCount X 0 t ω} := by
    ext ω
    exact_mod_cast Iff.rfl
  rw [hset] at hm
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa only [intervalMean, mul_comm] using hm

/-- Consequently, the small-interval multiple-jump ratio is uniformly bounded
above by half the candidate intensity. -/
theorem rareMultipleJump_ratio_le_half_intensity
    (hX : SatisfiesPoissonIntervalAxioms X P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε ≤
      hX.intervalMean 1 / 2 := by
  rw [div_le_iff₀ hε]
  calc
    P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} ≤
        hX.intervalMean (Real.toNNReal ε) / 2 :=
      hX.measure_two_le_half_intervalMean (Real.toNNReal ε)
    _ = ε * hX.intervalMean 1 / 2 := by
      rw [hX.intervalMean_linear, Real.coe_toNNReal ε hε.le]
    _ = (hX.intervalMean 1 / 2) * ε := by ring

/-- Klenke's P5 `limsup` axiom is an actual right-hand limit once the
nonnegativity and Markov bounds supplied by P4 are made explicit. -/
theorem tendsto_rareMultipleJump_ratio
    (hX : SatisfiesPoissonIntervalAxioms X P) :
    Tendsto (fun ε : ℝ ↦
      P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε)
      (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℝ := fun ε ↦
    P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hnonneg : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ f ε :=
    hpos.mono fun ε hε ↦ div_nonneg (measureReal_nonneg) hε.le
  have hboundedAbove : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) f :=
    isBoundedUnder_of_eventually_le <|
      hpos.mono fun ε hε ↦ hX.rareMultipleJump_ratio_le_half_intensity hε
  have hboundedBelow : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·) f :=
    isBoundedUnder_of_eventually_ge hnonneg
  have hinf : 0 ≤ liminf f (𝓝[>] (0 : ℝ)) :=
    le_liminf_of_le hboundedAbove.isCoboundedUnder_ge hnonneg
  have hsup : limsup f (𝓝[>] (0 : ℝ)) ≤ 0 := by
    change limsup (fun ε : ℝ ↦
      P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal ε) ω} / ε)
      (𝓝[>] 0) ≤ 0
    rw [hX.rareMultipleJump]
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hboundedAbove hboundedBelow

end SatisfiesPoissonIntervalAxioms

end ProbabilityTheory
