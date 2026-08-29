/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Probability.Distributions.Bernoulli
public import StochLean.Probability.LimitTheorems.PoissonApproximation
public import StochLean.Probability.Process.Poisson.IntervalAxioms

/-!
# Foundations for the converse Poisson interval characterization

This file develops the analytic and dyadic-approximation foundations for the converse direction
of Klenke, Theorem 5.34.  The stationary additive interval mean is shown to be linear, Markov's
inequality supplies the missing boundedness for P5, the exact `limsup` axiom is upgraded to a
genuine right-hand limit, and dyadic occupation variables are identified as i.i.d. Bernoulli
variables.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped NNReal Topology BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {X : NNReal → Ω → ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Success probability of the indicator that a natural-valued random variable is nonzero. -/
noncomputable def occupationProbability (Y : Ω → ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] : unitInterval :=
  ⟨P.real {ω | 1 ≤ Y ω}, measureReal_nonneg, measureReal_le_one⟩

/-- The nonzero indicator of a natural-valued random variable has the corresponding Bernoulli
law.  The statement only needs a.e. measurability. -/
theorem hasLaw_occupationIndicator {Y : Ω → ℕ} (hY : AEMeasurable Y P) :
    HasLaw (fun ω ↦ if 1 ≤ Y ω then 1 else 0)
      (bernoulliMeasure (1 : ℕ) 0 (occupationProbability Y P)) P := by
  let Z : Ω → ℕ := fun ω ↦ if 1 ≤ Y ω then 1 else 0
  have hZ : AEMeasurable Z P := by
    exact (measurable_of_countable fun k : ℕ ↦ if 1 ≤ k then 1 else 0).comp_aemeasurable hY
  refine ⟨hZ, ?_⟩
  apply MeasureTheory.Measure.ext_of_measureReal_singleton
  intro k
  rw [map_measureReal_apply_of_aemeasurable hZ (MeasurableSet.singleton k)]
  by_cases hk1 : k = 1
  · subst k
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem]
    · apply congrArg P.real
      ext ω
      simp [Z]
      omega
    · exact MeasurableSet.singleton 1
    · simp
    · simp
  by_cases hk0 : k = 0
  · subst k
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem]
    · have hA : NullMeasurableSet {ω | 1 ≤ Y ω} P :=
        hY.nullMeasurableSet_preimage measurableSet_Ici
      rw [show Z ⁻¹' ({0} : Set ℕ) = ({ω | 1 ≤ Y ω})ᶜ by
        ext ω
        simp [Z]]
      simpa [occupationProbability] using measureReal_compl₀ hA
    · exact MeasurableSet.singleton 0
    · simp
    · simp
  · rw [bernoulliMeasure_real_apply_of_notMem_of_notMem]
    · rw [show (fun ω ↦ if 1 ≤ Y ω then 1 else 0) ⁻¹' ({k} : Set ℕ) = ∅ by
        ext ω
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        split_ifs
        · exact fun h ↦ hk1 h.symm
        · exact fun h ↦ hk0 h.symm]
      exact measureReal_empty
    · exact MeasurableSet.singleton k
    · exact fun h ↦ hk1 h.symm
    · exact fun h ↦ hk0 h.symm

namespace SatisfiesPoissonIntervalAxioms

/-- Length of one interval in the level-`n` dyadic partition of `(0, t]`. -/
noncomputable def dyadicIntervalLength (t : NNReal) (n : ℕ) : NNReal :=
  t / ((2 : NNReal) ^ n)

/-- Count in the `i`-th interval of the level-`n` dyadic partition.  The definition is useful
for all `i`; the partition of `(0, t]` uses the first `2 ^ n` values. -/
noncomputable def dyadicSubintervalCount
    (X : NNReal → Ω → ℕ) (t : NNReal) (n i : ℕ) (ω : Ω) : ℕ :=
  poissonIntervalCount X (i • dyadicIntervalLength t n) ((i + 1) • dyadicIntervalLength t n) ω

/-- Bernoulli occupation indicator of a dyadic subinterval. -/
noncomputable def dyadicSubintervalOccupied
    (X : NNReal → Ω → ℕ) (t : NNReal) (n i : ℕ) (ω : Ω) : ℕ :=
  if 1 ≤ dyadicSubintervalCount X t n i ω then 1 else 0

/-- Common Bernoulli success parameter of the level-`n` dyadic occupation indicators. -/
noncomputable def dyadicOccupancyProbability
    (X : NNReal → Ω → ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (t : NNReal) (n : ℕ) : unitInterval :=
  occupationProbability (poissonIntervalCount X 0 (dyadicIntervalLength t n)) P

/-- Number of occupied cells in the level-`n` dyadic partition of `(0, t]`. -/
noncomputable def dyadicOccupiedSum
    (X : NNReal → Ω → ℕ) (t : NNReal) (n : ℕ) (ω : Ω) : ℕ :=
  ∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω

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

/-- Counts in equal dyadic subintervals form an independent family. -/
theorem iIndepFun_dyadicSubintervalCount
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    iIndepFun (dyadicSubintervalCount X t n) P := by
  let Δ := dyadicIntervalLength t n
  have htime : Monotone (fun i : ℕ ↦ i • Δ) := by
    intro i j hij
    exact nsmul_le_nsmul_left Δ.2 hij
  change iIndepFun (fun i ω ↦
    X ((i + 1) • dyadicIntervalLength t n) ω -
      X (i • dyadicIntervalLength t n) ω) P
  exact hX.indepIncrements.nat htime

theorem aemeasurable_dyadicSubintervalCount
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    AEMeasurable (dyadicSubintervalCount X t n i) P := by
  exact (hX.aemeasurable ((i + 1) • dyadicIntervalLength t n)).sub
    (hX.aemeasurable (i • dyadicIntervalLength t n))

theorem aemeasurable_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    AEMeasurable (dyadicSubintervalOccupied X t n i) P := by
  let occupied : ℕ → ℕ := fun k ↦ if 1 ≤ k then 1 else 0
  have hm : Measurable occupied := measurable_of_countable occupied
  change AEMeasurable (fun ω ↦
    if 1 ≤ dyadicSubintervalCount X t n i ω then 1 else 0) P
  exact hm.comp_aemeasurable (hX.aemeasurable_dyadicSubintervalCount t n i)

/-- Dyadic occupation indicators inherit independence from the interval counts. -/
theorem iIndepFun_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    iIndepFun (dyadicSubintervalOccupied X t n) P := by
  let occupied : ℕ → ℕ := fun k ↦ if 1 ≤ k then 1 else 0
  have hi := (hX.iIndepFun_dyadicSubintervalCount t n).comp
    (fun _ ↦ occupied) (fun _ ↦ measurable_of_countable occupied)
  change iIndepFun (fun i ω ↦
    if 1 ≤ dyadicSubintervalCount X t n i ω then 1 else 0) P
  exact hi

/-- Every dyadic subinterval count has the law of the count on the first subinterval. -/
theorem identDistrib_dyadicSubintervalCount
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    IdentDistrib (poissonIntervalCount X 0 (dyadicIntervalLength t n))
      (dyadicSubintervalCount X t n i) P P := by
  apply hX.stationaryIntervalLaw 0 (dyadicIntervalLength t n)
    (i • dyadicIntervalLength t n) ((i + 1) • dyadicIntervalLength t n)
  · exact bot_le
  · exact nsmul_le_nsmul_left (dyadicIntervalLength t n).2 (Nat.le_succ i)
  · have hle : i • dyadicIntervalLength t n ≤
        (i + 1) • dyadicIntervalLength t n :=
      nsmul_le_nsmul_left (dyadicIntervalLength t n).2 (Nat.le_succ i)
    rw [tsub_zero]
    change dyadicIntervalLength t n =
      (i + 1) • dyadicIntervalLength t n - i • dyadicIntervalLength t n
    rw [eq_tsub_iff_add_eq_of_le hle, succ_nsmul]
    ac_rfl

/-- The occupation indicators of all dyadic subintervals are identically distributed. -/
theorem identDistrib_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    IdentDistrib
      (fun ω ↦ if 1 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω then 1 else 0)
      (dyadicSubintervalOccupied X t n i) P P := by
  let occupied : ℕ → ℕ := fun k ↦ if 1 ≤ k then 1 else 0
  have h := (hX.identDistrib_dyadicSubintervalCount t n i).comp
    (measurable_of_countable occupied)
  change IdentDistrib
    (fun ω ↦ if 1 ≤ poissonIntervalCount X 0 (dyadicIntervalLength t n) ω then 1 else 0)
    (fun ω ↦ if 1 ≤ dyadicSubintervalCount X t n i ω then 1 else 0) P P
  exact h

/-- Each dyadic occupation indicator has the common Bernoulli law. -/
theorem hasLaw_dyadicSubintervalOccupied
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n i : ℕ) :
    HasLaw (dyadicSubintervalOccupied X t n i)
      (bernoulliMeasure (1 : ℕ) 0 (dyadicOccupancyProbability X P t n)) P := by
  have hbase := hasLaw_occupationIndicator (P := P)
    ((hX.aemeasurable (dyadicIntervalLength t n)).sub (hX.aemeasurable 0))
  exact (hX.identDistrib_dyadicSubintervalOccupied t n i).hasLaw hbase

/-- The number of occupied cells in a finite dyadic partition has the corresponding
Poisson-binomial law. -/
theorem hasLaw_dyadicOccupiedSum
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) (n : ℕ) :
    HasLaw
      (fun ω ↦ ∑ i : Fin (2 ^ n), dyadicSubintervalOccupied X t n i ω)
      (PMF.poissonBinomial
        (List.replicate (2 ^ n) (dyadicOccupancyProbability X P t n))).toMeasure P := by
  have hIndep : iIndepFun
      (fun i : Fin (2 ^ n) ↦ dyadicSubintervalOccupied X t n i) P :=
    iIndepFun.precomp Fin.val_injective (hX.iIndepFun_dyadicSubintervalOccupied t n)
  have hLaw : ∀ i : Fin (2 ^ n),
      HasLaw (dyadicSubintervalOccupied X t n i)
        (bernoulliMeasure (1 : ℕ) 0 (dyadicOccupancyProbability X P t n)) P :=
    fun i ↦ hX.hasLaw_dyadicSubintervalOccupied t n i
  simpa only [Fintype.card_fin] using
    iIndepFun.hasLaw_fintype_sum_bernoulli hIndep hLaw

/-- The total error from intervals containing two or more jumps in the dyadic
partition of `(0, t]` tends to zero.  This is the P5 estimate used in Klenke's
binomial approximation argument. -/
theorem tendsto_dyadic_multipleJump_error
    (hX : SatisfiesPoissonIntervalAxioms X P) (t : NNReal) :
    Tendsto (fun n : ℕ ↦
      ((2 : ℝ) ^ n) *
        P.real {ω | 2 ≤ poissonIntervalCount X 0 (t / ((2 : NNReal) ^ n)) ω})
      atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst t
    simp [poissonIntervalCount]
  have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (lt_of_le_of_ne t.2 (Ne.symm ht))
  let ε : ℕ → ℝ := fun n ↦ (t : ℝ) / (2 : ℝ) ^ n
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    have h := hpow.const_mul (t : ℝ)
    simpa only [ε, div_eq_mul_inv, inv_pow, mul_zero] using h
  have hεpos : ∀ n, 0 < ε n := fun n ↦ div_pos htpos (pow_pos (by norm_num) n)
  have hεright : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hεzero, Eventually.of_forall fun n ↦ hεpos n⟩
  have hratio := hX.tendsto_rareMultipleJump_ratio.comp hεright
  change Tendsto (fun n : ℕ ↦
    P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal (ε n)) ω} / ε n)
    atTop (𝓝 0) at hratio
  have hscaled : Tendsto (fun n : ℕ ↦ (t : ℝ) *
      (P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal (ε n)) ω} / ε n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hratio
  apply hscaled.congr'
  exact Eventually.of_forall fun n ↦ by
    have hεnn : Real.toNNReal (ε n) = t / ((2 : NNReal) ^ n) := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ (hεpos n).le]
      simp only [ε, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
    change (t : ℝ) *
      (P.real {ω | 2 ≤ poissonIntervalCount X 0 (Real.toNNReal (ε n)) ω} / ε n) =
        ((2 : ℝ) ^ n) *
          P.real {ω | 2 ≤ poissonIntervalCount X 0 (t / ((2 : NNReal) ^ n)) ω}
    rw [hεnn]
    dsimp only [ε]
    field_simp

end SatisfiesPoissonIntervalAxioms

end ProbabilityTheory
