/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.StableClassification

/-!
# Existence of the index of a broadly stable law

This file proves the index-existence assertion in Klenke's Theorem 16.22 from the broad-stability
predicate.  The index is a theorem output, not a field smuggled into the definition.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace ProbabilityTheory

private theorem rat_cast_eq_natAbs_num_div_den {q : ℚ} (hq : 0 ≤ q) :
    (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
  rw [Rat.cast_def]
  congr 1
  have hn : q.num = (q.num.natAbs : ℤ) :=
    (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)).symm
  calc
    (q.num : ℝ) = ((q.num.natAbs : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hn
    _ = (q.num.natAbs : ℝ) := by norm_num

private theorem rat_lt_log_div_iff_pow_lt {u v : ℝ} (hu : 1 < u) (hv : 1 < v)
    {q : ℚ} (hq : 0 ≤ q) :
    (q : ℝ) < Real.log u / Real.log v ↔
      v ^ q.num.natAbs < u ^ q.den := by
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hlv : 0 < Real.log v := Real.log_pos hv
  have hden : 0 < (q.den : ℝ) := by exact_mod_cast q.den_pos
  rw [rat_cast_eq_natAbs_num_div_den hq]
  rw [div_lt_div_iff₀ hden hlv]
  have hleft : (q.num.natAbs : ℝ) * Real.log v =
      Real.log (v ^ q.num.natAbs) := (Real.log_pow _ _).symm
  have hright : Real.log u * (q.den : ℝ) = Real.log (u ^ q.den) := by
    rw [Real.log_pow]
    ring
  rw [hleft, hright]
  exact Real.log_lt_log_iff (by positivity) (by positivity)

/-- A positive, strictly increasing, completely multiplicative scale on positive natural
numbers is necessarily a real power.  This is the arithmetic core of index existence. -/
theorem exists_rpow_index_of_pos_multiplicative_strictMono
    (A : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < A n)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → A (m * n) = A m * A n)
    (hstrict : ∀ m n : ℕ, 0 < m → m < n → A m < A n) :
    ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ, 0 < n → A n = (n : ℝ) ^ (1 / α) := by
  have hAone : A 1 = 1 := by
    have h := hmul 1 1 (by norm_num) (by norm_num)
    norm_num at h
    have hp := hpos 1 (by norm_num)
    nlinarith
  have hpow (n k : ℕ) (hn : 0 < n) : A (n ^ k) = (A n) ^ k := by
    induction k with
    | zero => simp [hAone]
    | succ k ih =>
        rw [pow_succ, hmul _ n (pow_pos hn k) hn, ih, pow_succ]
  have hstrictOn : StrictMonoOn A (Set.Ioi 0) := by
    intro m hm n _hn hmn
    exact hstrict m n hm hmn
  have hA2 : 1 < A 2 := by simpa [hAone] using hstrict 1 2 (by norm_num) (by norm_num)
  have htwoR : (1 : ℝ) < 2 := by norm_num
  let c : ℝ := Real.log (A 2) / Real.log 2
  have hc : 0 < c := div_pos (Real.log_pos hA2) (Real.log_pos htwoR)
  refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := hn
  rcases hn1.eq_or_lt with rfl | hn1
  · simp [hAone]
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn1
  have hAn : 1 < A n := by simpa [hAone] using hstrict 1 n (by norm_num) hn1
  have hratio : Real.log n / Real.log 2 = Real.log (A n) / Real.log (A 2) := by
    apply eq_of_forall_rat_lt_iff_lt
    intro q
    by_cases hq : 0 ≤ q
    · rw [rat_lt_log_div_iff_pow_lt hnR (by norm_num) hq,
        rat_lt_log_div_iff_pow_lt hAn hA2 hq]
      rw [← hpow 2 q.num.natAbs (by norm_num), ← hpow n q.den hn]
      norm_cast
      exact (hstrictOn.lt_iff_lt
        (pow_pos (by norm_num : 0 < (2 : ℕ)) _) (pow_pos hn _)).symm
    · have hqneg : (q : ℝ) < 0 := by
        exact_mod_cast (lt_of_not_ge hq)
      have hleft : 0 < Real.log n / Real.log 2 :=
        div_pos (Real.log_pos hnR) (Real.log_pos htwoR)
      have hright : 0 < Real.log (A n) / Real.log (A 2) :=
        div_pos (Real.log_pos hAn) (Real.log_pos hA2)
      constructor <;> intro <;> linarith
  have hlog : Real.log (A n) = c * Real.log n := by
    dsimp [c]
    field_simp [ne_of_gt (Real.log_pos hA2), ne_of_gt (Real.log_pos htwoR)] at hratio ⊢
    nlinarith
  have hcexp : 1 / (1 / c) = c := by field_simp [hc.ne']
  rw [hcexp]
  apply Real.strictMonoOn_log.injOn
    (by exact hpos n hn) (Real.rpow_pos_of_pos (by positivity) _)
  rw [Real.log_rpow (by positivity)]
  exact hlog

/-- Positive affine scale is unique for a non-Dirac law.  If two scales differed, iteration of
the induced characteristic-function norm invariance toward zero would force unit norm at every
frequency and hence a point mass. -/
theorem affine_scale_unique_of_nonDirac
    {μ : ProbabilityMeasure ℝ} (hμ : μ.IsNonDirac)
    {n : ℕ} {a b d e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haff : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap a d μ)
    (hbff : ProbabilityMeasure.convPow μ n = ProbabilityMeasure.affineMap b e μ) :
    a = b := by
  have hlaw : ProbabilityMeasure.affineMap a d μ =
      ProbabilityMeasure.affineMap b e μ := haff.symm.trans hbff
  have hnorm (t : ℝ) :
      ‖charFun (μ : Measure ℝ) (a * t)‖ = ‖charFun (μ : Measure ℝ) (b * t)‖ := by
    have hchar := congrArg (fun ξ : ProbabilityMeasure ℝ =>
      charFun (ξ : Measure ℝ) t) hlaw
    simp only [ProbabilityMeasure.charFun_affineMap] at hchar
    have hnorm' := congrArg norm hchar
    simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using hnorm'
  have invariant_forces_pointMass (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
      (hstep : ∀ t : ℝ,
        ‖charFun (μ : Measure ℝ) (q * t)‖ = ‖charFun (μ : Measure ℝ) t‖) :
      ∃ x : ℝ, μ = ProbabilityMeasure.pointMass x := by
    apply eq_pointMass_of_charFun_norm_eq_one
    intro t
    have hiter (k : ℕ) :
        ‖charFun (μ : Measure ℝ) (q ^ k * t)‖ =
          ‖charFun (μ : Measure ℝ) t‖ := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          calc
            ‖charFun (μ : Measure ℝ) (q ^ k * q * t)‖ =
                ‖charFun (μ : Measure ℝ) (q * (q ^ k * t))‖ := by ring_nf
            _ = ‖charFun (μ : Measure ℝ) (q ^ k * t)‖ := hstep _
            _ = ‖charFun (μ : Measure ℝ) t‖ := ih
    have harg : Tendsto (fun k : ℕ => q ^ k * t) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const t
    have hlim : Tendsto
        (fun k : ℕ => ‖charFun (μ : Measure ℝ) (q ^ k * t)‖)
        atTop (nhds ‖charFun (μ : Measure ℝ) 0‖) :=
      (continuous_norm.comp
        (continuous_charFun (μ := (μ : Measure ℝ)))).continuousAt.tendsto.comp harg
    have hconst : Tendsto
        (fun k : ℕ => ‖charFun (μ : Measure ℝ) (q ^ k * t)‖)
        atTop (nhds ‖charFun (μ : Measure ℝ) t‖) := by
      rw [show (fun k : ℕ => ‖charFun (μ : Measure ℝ) (q ^ k * t)‖) =
          (fun _ : ℕ => ‖charFun (μ : Measure ℝ) t‖) by
        funext k
        exact hiter k]
      exact tendsto_const_nhds
    have heq := tendsto_nhds_unique hconst hlim
    simpa using heq
  apply le_antisymm
  · by_contra hab
    have hba : b < a := lt_of_not_ge hab
    let q : ℝ := b / a
    have hq0 : 0 ≤ q := (div_pos hb ha).le
    have hq1 : q < 1 := (div_lt_one ha).mpr hba
    have hstep (t : ℝ) :
        ‖charFun (μ : Measure ℝ) (q * t)‖ = ‖charFun (μ : Measure ℝ) t‖ := by
      have h := hnorm (t / a)
      dsimp [q]
      convert h.symm using 1 <;> field_simp [ha.ne']
    obtain ⟨x, hx⟩ := invariant_forces_pointMass q hq0 hq1 hstep
    exact hμ x hx
  · by_contra hba
    have hab : a < b := lt_of_not_ge hba
    let q : ℝ := a / b
    have hq0 : 0 ≤ q := (div_pos ha hb).le
    have hq1 : q < 1 := (div_lt_one hb).mpr hab
    have hstep (t : ℝ) :
        ‖charFun (μ : Measure ℝ) (q * t)‖ = ‖charFun (μ : Measure ℝ) t‖ := by
      have h := hnorm (t / b)
      dsimp [q]
      convert h using 1 <;> field_simp [hb.ne']
    obtain ⟨x, hx⟩ := invariant_forces_pointMass q hq0 hq1 hstep
    exact hμ x hx

theorem convPow_mul (mu : ProbabilityMeasure ℝ) (m n : ℕ) :
    ProbabilityMeasure.convPow mu (m * n) =
      ProbabilityMeasure.convPow (ProbabilityMeasure.convPow mu m) n := by
  induction n with
  | zero => simp [ProbabilityMeasure.convPow_zero]
  | succ n ih =>
      rw [Nat.mul_succ, ProbabilityMeasure.convPow_add, ProbabilityMeasure.convPow_succ, ih]

/-- Exponent-cost scaling for an arbitrary broad-stability witness. -/
theorem broadStable_exponentCost_scale
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense)
    {n : ℕ} {a d : ℝ} (haff : ProbabilityMeasure.convPow μ n =
      ProbabilityMeasure.affineMap a d μ) (t : ℝ) :
    hstable.isInfinitelyDivisible.exponentCost (a * t) =
      (n : ℝ) * hstable.isInfinitelyDivisible.exponentCost t := by
  let hID := hstable.isInfinitelyDivisible
  have hcf := congrArg
    (fun rho : ProbabilityMeasure ℝ => ‖charFun (rho : Measure ℝ) t‖) haff
  rw [ProbabilityMeasure.charFun_convPow_real,
    ProbabilityMeasure.charFun_affineMap, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one] at hcf
  rw [← hID.exp_exponent, ← hID.exp_exponent, Complex.norm_exp] at hcf
  rw [norm_pow, Complex.norm_exp, ← Real.exp_nat_mul] at hcf
  have hcost := Real.exp_injective hcf
  change -(hID.exponent (a * t)).re = (n : ℝ) * (-(hID.exponent t).re)
  linarith [hcost]

theorem IsStableInBroadSense.exists_exponentCost_pos
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense) :
    ∃ t : ℝ, 0 < hstable.isInfinitelyDivisible.exponentCost t := by
  let hID := hstable.isInfinitelyDivisible
  by_contra hnone
  push Not at hnone
  have hzero (t : ℝ) : hID.exponentCost t = 0 :=
    le_antisymm (hnone t) (hID.exponentCost_nonneg t)
  have hnorm (t : ℝ) : ‖charFun (μ : Measure ℝ) t‖ = 1 := by
    rw [← hID.exp_exponent, Complex.norm_exp]
    have hrew : (hID.exponent t).re = -hID.exponentCost t := by
      change (hID.exponent t).re = -(-(hID.exponent t).re)
      ring
    rw [hrew, hzero]
    norm_num
  obtain ⟨x, hx⟩ := eq_pointMass_of_charFun_norm_eq_one μ hnorm
  exact hstable.1 x hx

/-- The canonical chosen positive scale of a broad-stability witness. -/
noncomputable def broadStableScale
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense) (n : ℕ) : ℝ :=
  if hn : 0 < n then Classical.choose (hstable.2 n hn) else 0

theorem broadStableScale_pos
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense)
    {n : ℕ} (hn : 0 < n) : 0 < broadStableScale hstable n := by
  rw [broadStableScale, dif_pos hn]
  exact (Classical.choose_spec (hstable.2 n hn)).1

theorem broadStableScale_spec
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense)
    {n : ℕ} (hn : 0 < n) :
    ∃ d : ℝ, ProbabilityMeasure.convPow μ n =
      ProbabilityMeasure.affineMap (broadStableScale hstable n) d μ := by
  rw [broadStableScale, dif_pos hn]
  exact (Classical.choose_spec (hstable.2 n hn)).2

theorem broadStableScale_mul
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    broadStableScale hstable (m * n) =
      broadStableScale hstable m * broadStableScale hstable n := by
  obtain ⟨dm, hpm⟩ := broadStableScale_spec hstable hm
  obtain ⟨dn, hpn⟩ := broadStableScale_spec hstable hn
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  obtain ⟨dmn, hpmn⟩ := broadStableScale_spec hstable hmn
  have hcombined : ProbabilityMeasure.convPow μ (m * n) =
      ProbabilityMeasure.affineMap
        (broadStableScale hstable m * broadStableScale hstable n)
        (broadStableScale hstable m * dn + n * dm) μ := by
    calc
      ProbabilityMeasure.convPow μ (m * n) =
          ProbabilityMeasure.convPow (ProbabilityMeasure.convPow μ m) n :=
        convPow_mul μ m n
      _ = ProbabilityMeasure.convPow
          (ProbabilityMeasure.affineMap (broadStableScale hstable m) dm μ) n := by
        rw [hpm]
      _ = ProbabilityMeasure.affineMap (broadStableScale hstable m) (n * dm)
          (ProbabilityMeasure.convPow μ n) :=
        ProbabilityMeasure.convPow_affineMap _ _ _ _
      _ = ProbabilityMeasure.affineMap (broadStableScale hstable m) (n * dm)
          (ProbabilityMeasure.affineMap (broadStableScale hstable n) dn μ) := by
        rw [hpn]
      _ = ProbabilityMeasure.affineMap
          (broadStableScale hstable m * broadStableScale hstable n)
          (broadStableScale hstable m * dn + n * dm) μ := by
        rw [ProbabilityMeasure.affineMap_comp]
  exact affine_scale_unique_of_nonDirac hstable.1
    (broadStableScale_pos hstable hmn)
    (mul_pos (broadStableScale_pos hstable hm) (broadStableScale_pos hstable hn))
    hpmn hcombined

/-- The canonical scales are strictly increasing.  A reversed scale inequality would make the
nonnegative exponent cost grow along a geometric sequence tending to zero, contradicting
continuity at zero. -/
theorem broadStableScale_strictMono
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense)
    {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    broadStableScale hstable m < broadStableScale hstable n := by
  have hn : 0 < n := hm.trans hmn
  obtain ⟨dm, hpm⟩ := broadStableScale_spec hstable hm
  obtain ⟨dn, hpn⟩ := broadStableScale_spec hstable hn
  let hID := hstable.isInfinitelyDivisible
  obtain ⟨t, ht⟩ := IsStableInBroadSense.exists_exponentCost_pos hstable
  have hmScale (x : ℝ) : hID.exponentCost (broadStableScale hstable m * x) =
      (m : ℝ) * hID.exponentCost x :=
    broadStable_exponentCost_scale hstable hpm x
  have hnScale (x : ℝ) : hID.exponentCost (broadStableScale hstable n * x) =
      (n : ℝ) * hID.exponentCost x :=
    broadStable_exponentCost_scale hstable hpn x
  by_contra hnot
  have hle : broadStableScale hstable n ≤ broadStableScale hstable m := le_of_not_gt hnot
  rcases hle.eq_or_lt with heq | hlt
  · have hmnCost := hmScale t
    have hnnCost := hnScale t
    rw [heq] at hnnCost
    have hmR : (m : ℝ) < n := by exact_mod_cast hmn
    nlinarith
  · let q : ℝ := broadStableScale hstable n / broadStableScale hstable m
    have hAm : 0 < broadStableScale hstable m := broadStableScale_pos hstable hm
    have hAn : 0 < broadStableScale hstable n := broadStableScale_pos hstable hn
    have hq0 : 0 ≤ q := (div_pos hAn hAm).le
    have hq1 : q < 1 := (div_lt_one hAm).mpr hlt
    have hrel (x : ℝ) :
        (m : ℝ) * hID.exponentCost (q * x) =
          (n : ℝ) * hID.exponentCost x := by
      have hm' := hmScale (x / broadStableScale hstable m)
      have hn' := hnScale (x / broadStableScale hstable m)
      have hargm : broadStableScale hstable m *
          (x / broadStableScale hstable m) = x := by field_simp [hAm.ne']
      have hargn : broadStableScale hstable n *
          (x / broadStableScale hstable m) = q * x := by
        dsimp [q]
        field_simp [hAm.ne']
      rw [hargm] at hm'
      rw [hargn] at hn'
      nlinarith
    have hmono (x : ℝ) : hID.exponentCost x ≤ hID.exponentCost (q * x) := by
      have hr := hrel x
      have hx0 := hID.exponentCost_nonneg x
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
      nlinarith
    have hiter (k : ℕ) :
        hID.exponentCost t ≤ hID.exponentCost (q ^ k * t) := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          have hs := hmono (q ^ k * t)
          rw [show q * (q ^ k * t) = q ^ k * q * t by ring] at hs
          exact ih.trans hs
    have harg : Tendsto (fun k : ℕ => q ^ k * t) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const t
    have hlim : Tendsto (fun k : ℕ => hID.exponentCost (q ^ k * t)) atTop (nhds 0) := by
      change Tendsto (hID.exponentCost ∘ fun k : ℕ => q ^ k * t) atTop (nhds 0)
      have hraw := hID.continuous_exponentCost.continuousAt.tendsto.comp harg
      simpa only [hID.exponentCost_zero] using hraw
    have hnonpos : hID.exponentCost t ≤ 0 := ge_of_tendsto' hlim hiter
    linarith

/-- Klenke Theorem 16.22(i): every broadly stable non-Dirac real law has an index in `(0,2]`.
The proof derives the index from the canonical scales and then applies the independently proved
stable-index upper bound. -/
theorem IsStableInBroadSense.exists_index
    {μ : ProbabilityMeasure ℝ} (hstable : μ.IsStableInBroadSense) :
    ∃ α : ℝ, α ∈ Set.Ioc 0 2 ∧ μ.IsStableInBroadSenseWithIndex α := by
  obtain ⟨α, hα, hscale⟩ := exists_rpow_index_of_pos_multiplicative_strictMono
    (broadStableScale hstable)
    (fun n hn => broadStableScale_pos hstable hn)
    (fun m n hm hn => broadStableScale_mul hstable m n hm hn)
    (fun m n hm hmn => broadStableScale_strictMono hstable hm hmn)
  have hindexed : μ.IsStableInBroadSenseWithIndex α := by
    refine ⟨hα, hstable.1, ?_⟩
    intro n hn
    obtain ⟨d, hpow⟩ := broadStableScale_spec hstable hn
    refine ⟨d, ?_⟩
    rw [← hscale n hn]
    exact hpow
  exact ⟨α, ⟨hα, IsStableInBroadSenseWithIndex.index_le_two hindexed⟩, hindexed⟩

end ProbabilityTheory
