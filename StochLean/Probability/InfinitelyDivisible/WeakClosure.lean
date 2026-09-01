/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.InfinitelyDivisible.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Weak closure of infinite divisibility

This module develops Corollary 16.9 in stages.  The first load-bearing step is that a weak limit
of infinitely divisible real laws still has a nowhere-vanishing characteristic function.  The
proof is internal: normalized characteristic exponents give a dyadic lower bound, while weak
convergence supplies the local bound near frequency zero.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ProbabilityTheory

namespace ProbabilityTheory

/-- A compact/tail estimate for characteristic functions.  The compact part uses the elementary
Lipschitz bound for the circle exponential, while the complement uses its diameter-two bound. -/
theorem norm_charFun_sub_le_of_compact
    (μ : ProbabilityMeasure ℝ) {K : Set ℝ} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (s t : ℝ) :
    ‖charFun (μ : Measure ℝ) s - charFun (μ : Measure ℝ) t‖ ≤
      R * |s - t| + 2 * (μ : Measure ℝ).real Kᶜ := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  have hexp (u : ℝ) :
      Integrable (fun x : ℝ => Complex.exp (((u * x : ℝ) : ℂ) * Complex.I))
        (μ : Measure ℝ) :=
    Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with x
      rw [Complex.norm_exp]
      simp)
  have hf : Integrable f (μ : Measure ℝ) := (hexp s).sub (hexp t)
  have hphase (x : ℝ) : ‖f x‖ ≤ |s - t| * ‖x‖ := by
    have hfactor : f x =
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((((s - t) * x : ℝ) : ℂ) * Complex.I) - 1) := by
      dsimp [f]
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hcircle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (s - t) * x)
    rw [mul_comm Complex.I] at hcircle
    simpa [abs_mul, Real.norm_eq_abs] using hcircle
  let g : ℝ → ℝ := fun x =>
    R * |s - t| + Kᶜ.indicator (fun _ => (2 : ℝ)) x
  have hg : Integrable g (μ : Measure ℝ) := by
    apply Integrable.add (integrable_const _)
    exact (integrable_const (2 : ℝ)).indicator hK.measurableSet.compl
  have hfg : ∀ x, ‖f x‖ ≤ g x := by
    intro x
    by_cases hx : x ∈ K
    · have hxc : x ∉ Kᶜ := by simpa using hx
      simp only [g, Set.indicator, if_neg hxc, add_zero]
      calc
        ‖f x‖ ≤ |s - t| * ‖x‖ := hphase x
        _ ≤ |s - t| * R := by
          gcongr
          exact hKR x hx
        _ = R * |s - t| := mul_comm _ _
    · have hxc : x ∈ Kᶜ := by simpa using hx
      simp only [g, Set.indicator, if_pos hxc]
      have htwo : ‖f x‖ ≤ 2 := by
        dsimp [f]
        calc
          _ ≤
              ‖Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)‖ +
                ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [Complex.norm_exp, Complex.norm_exp]
            norm_num
      exact htwo.trans (le_add_of_nonneg_left (mul_nonneg hR (abs_nonneg (s - t))))
  have hchar :
      charFun (μ : Measure ℝ) s - charFun (μ : Measure ℝ) t =
        ∫ x, f x ∂(μ : Measure ℝ) := by
    rw [charFun_apply_real, charFun_apply_real, integral_sub (hexp s) (hexp t)]
    simp only [Complex.ofReal_mul]
  rw [hchar]
  calc
    ‖∫ x, f x ∂(μ : Measure ℝ)‖ ≤ ∫ x, g x ∂(μ : Measure ℝ) :=
      norm_integral_le_of_norm_le hg (ae_of_all _ hfg)
    _ = R * |s - t| + 2 * (μ : Measure ℝ).real Kᶜ := by
      dsimp [g]
      rw [integral_add (integrable_const _) ((integrable_const (2 : ℝ)).indicator
        hK.measurableSet.compl)]
      rw [integral_indicator hK.measurableSet.compl]
      simpa [mul_comm]

/-- Tight real probability laws have a uniformly equicontinuous family of characteristic
functions. -/
theorem uniformEquicontinuous_charFun_of_isTightMeasureSet
    {μ : ℕ → ProbabilityMeasure ℝ}
    (htight : IsTightMeasureSet (Set.range fun n => (μ n : Measure ℝ))) :
    UniformEquicontinuous (fun n t => charFun (μ n : Measure ℝ) t) := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal (ε / 8)) (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨R, hRpos, hKR⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨ε / (2 * R), by positivity, ?_⟩
  intro s t hst n
  rw [dist_eq_norm]
  have hbound := norm_charFun_sub_le_of_compact (μ n) hK hRpos.le hKR s t
  have htailReal : (μ n : Measure ℝ).real Kᶜ ≤ ε / 8 := by
    have hmeasure := htail (μ n : Measure ℝ) ⟨n, rfl⟩
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
    simpa [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 8)] using hreal
  have habs : |s - t| < ε / (2 * R) := by
    simpa [Real.dist_eq] using hst
  calc
    ‖charFun (μ n : Measure ℝ) s - charFun (μ n : Measure ℝ) t‖
        ≤ R * |s - t| + 2 * (μ n : Measure ℝ).real Kᶜ := hbound
    _ < ε := by
      have hcompactPart : R * |s - t| < ε / 2 := by
        calc
          R * |s - t| < R * (ε / (2 * R)) := by gcongr
          _ = ε / 2 := by field_simp
      nlinarith

/-- Weak convergence of real probability laws is locally uniform at the characteristic-function
level.  This strengthens the pointwise form of Lévy convergence used by Mathlib. -/
theorem tendstoUniformlyOn_charFun_of_tendsto
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hlim : Tendsto μ atTop (𝓝 μ₀)) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n t => charFun (μ n : Measure ℝ) t)
      (fun t => charFun (μ₀ : Measure ℝ) t) atTop K := by
  have hpoint (t : ℝ) :
      Tendsto (fun n => charFun (μ n : Measure ℝ) t) atTop
        (𝓝 (charFun (μ₀ : Measure ℝ) t)) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim t
  have htight : IsTightMeasureSet (Set.range fun n => (μ n : Measure ℝ)) :=
    isTightMeasureSet_of_tendsto_charFun
      (continuous_charFun (μ := (μ₀ : Measure ℝ))).continuousAt hpoint
  have heq := uniformEquicontinuous_charFun_of_isTightMeasureSet htight
  let F : ℕ → K → ℂ := fun n => K.domRestrict (fun t => charFun (μ n : Measure ℝ) t)
  let f : K → ℂ := K.domRestrict (fun t => charFun (μ₀ : Measure ℝ) t)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heqK : Equicontinuous F := by
    exact (equicontinuous_restrict_iff _).mpr
      (heq.uniformEquicontinuousOn K).equicontinuousOn
  have hpointK : Tendsto F atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro t
    exact hpoint t
  have huMap :
      Tendsto (UniformFun.ofFun ∘ F) atTop (𝓝 (UniformFun.ofFun f)) :=
    (heqK.tendsto_uniformFun_iff_pi atTop f).2 hpointK
  have hu : TendstoUniformly F f atTop := by
    simpa [Function.comp_def] using
      (UniformFun.tendsto_iff_tendstoUniformly.mp huMap)
  exact tendstoUniformlyOn_iff_restrict.mpr hu

/-- The characteristic function of a weak limit of infinitely divisible real laws cannot vanish.

For a fixed frequency `t`, choose a dyadic subdivision `s = t / 2^k` at which the limiting
characteristic function has norm greater than `3/4`.  Eventually the approximating norms at `s`
are greater than `1/2`.  The quadratic dyadic exponent bound then gives a fixed positive lower
bound at `t`, contradicting convergence to zero. -/
theorem charFun_ne_zero_of_tendsto_infinitelyDivisible
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n).IsInfinitelyDivisible)
    (hlim : Tendsto μ atTop (𝓝 μ₀)) (t : ℝ) :
    charFun (μ₀ : Measure ℝ) t ≠ 0 := by
  have hcf (u : ℝ) :
      Tendsto (fun n => charFun (μ n : Measure ℝ) u) atTop
        (𝓝 (charFun (μ₀ : Measure ℝ) u)) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim u
  intro htzero
  have harg : Tendsto (fun k : ℕ => t / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (x := (2 : ℝ)⁻¹) (by norm_num)).const_mul t
  have hnear : Tendsto
      (fun k : ℕ => ‖charFun (μ₀ : Measure ℝ) (t / (2 : ℝ) ^ k)‖)
      atTop (𝓝 1) := by
    have hchar :=
      (continuous_charFun (μ := (μ₀ : Measure ℝ))).continuousAt.tendsto.comp harg
    have hnorm := continuous_norm.continuousAt.tendsto.comp hchar
    simpa [Function.comp_def] using hnorm
  have heventuallyNear :
      ∀ᶠ k : ℕ in atTop,
        (3 / 4 : ℝ) < ‖charFun (μ₀ : Measure ℝ) (t / (2 : ℝ) ^ k)‖ :=
    hnear.eventually (eventually_gt_nhds (by norm_num))
  obtain ⟨k, hk⟩ := heventuallyNear.exists
  let s : ℝ := t / (2 : ℝ) ^ k
  have hsApprox :
      ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < ‖charFun (μ n : Measure ℝ) s‖ := by
    have hsNorm := continuous_norm.continuousAt.tendsto.comp (hcf s)
    apply hsNorm.eventually
    apply eventually_gt_nhds
    dsimp [s]
    linarith
  let c : ℝ := (1 / 2 : ℝ) ^ (4 ^ k)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have htApprox : ∀ᶠ n : ℕ in atTop, ‖charFun (μ n : Measure ℝ) t‖ < c := by
    have htNorm := continuous_norm.continuousAt.tendsto.comp (hcf t)
    rw [htzero] at htNorm
    exact htNorm.eventually (eventually_lt_nhds (by simpa using hcpos))
  obtain ⟨n, hsn, htn⟩ := (hsApprox.and htApprox).exists
  let hn := hμ n
  have hscale := hn.exponentCost_two_pow_mul_le k s
  have hargEq : (2 : ℝ) ^ k * s = t := by
    dsimp [s]
    field_simp
  rw [hargEq] at hscale
  have hnorm (u : ℝ) :
      ‖charFun (μ n : Measure ℝ) u‖ = Real.exp (-hn.exponentCost u) := by
    rw [← hn.exp_exponent, Complex.norm_exp]
    congr 1
    change (hn.exponent u).re = -(-(hn.exponent u).re)
    ring
  have hexp :
      Real.exp (-((4 : ℝ) ^ k * hn.exponentCost s)) ≤
        Real.exp (-hn.exponentCost t) :=
    Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hpow : ‖charFun (μ n : Measure ℝ) s‖ ^ (4 ^ k) ≤
      ‖charFun (μ n : Measure ℝ) t‖ := by
    rw [hnorm s, hnorm t]
    convert hexp using 1
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hcLt : c < ‖charFun (μ n : Measure ℝ) s‖ ^ (4 ^ k) := by
    dsimp [c]
    exact pow_lt_pow_left₀ hsn (by norm_num) (by positivity)
  linarith [hcLt.trans_le hpow]

/-- Normalized continuous characteristic exponents pass to weak limits of infinitely divisible
laws.  The proof uses compact-uniform convergence of characteristic functions and uniqueness of
lifts through the exponential covering map on the interval joining `0` to the target frequency. -/
theorem tendsto_continuousExponent_of_tendsto_infinitelyDivisible
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n).IsInfinitelyDivisible)
    (hlim : Tendsto μ atTop (𝓝 μ₀)) (t : ℝ) :
    Tendsto (fun n => (hμ n).exponent t) atTop
      (𝓝 (continuousExponent μ₀
        (charFun_ne_zero_of_tendsto_infinitelyDivisible hμ hlim) t)) := by
  let h₀ne : ∀ s, charFun (μ₀ : Measure ℝ) s ≠ 0 :=
    charFun_ne_zero_of_tendsto_infinitelyDivisible hμ hlim
  let K : Set ℝ := Set.uIcc 0 t
  have hK : IsCompact K := isCompact_uIcc
  have hKne : K.Nonempty := ⟨0, Set.left_mem_uIcc⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne
    ((continuous_norm.comp (continuous_charFun (μ := (μ₀ : Measure ℝ)))).continuousOn)
  let m : ℝ := ‖charFun (μ₀ : Measure ℝ) x₀‖
  have hm : 0 < m := norm_pos_iff.mpr (h₀ne x₀)
  have hmin' : ∀ y ∈ K, m ≤ ‖charFun (μ₀ : Measure ℝ) y‖ := by
    intro y hy
    exact hmin hy
  have huniform := tendstoUniformlyOn_charFun_of_tendsto hlim hK
  have hclose : ∀ᶠ n in atTop, ∀ y ∈ K,
      dist (charFun (μ₀ : Measure ℝ) y) (charFun (μ n : Measure ℝ) y) < m / 2 :=
    Metric.tendstoUniformlyOn_iff.mp huniform (m / 2) (half_pos hm)
  have hexponentEventually : ∀ᶠ n in atTop,
      (hμ n).exponent t = continuousExponent μ₀ h₀ne t +
        Complex.log
          (charFun (μ n : Measure ℝ) t / charFun (μ₀ : Measure ℝ) t) := by
    filter_upwards [hclose] with n hn
    let zratio : K → ℂ := fun y =>
      charFun (μ n : Measure ℝ) y / charFun (μ₀ : Measure ℝ) y
    have hratioClose (y : K) : ‖zratio y - 1‖ < 1 / 2 := by
      have hdist := hn y y.2
      have hdenom := hmin' y y.2
      have hdenomPos : 0 < ‖charFun (μ₀ : Measure ℝ) y‖ :=
        norm_pos_iff.mpr (h₀ne y)
      have hquot :
          ‖(charFun (μ n : Measure ℝ) y - charFun (μ₀ : Measure ℝ) y) /
            charFun (μ₀ : Measure ℝ) y‖ < 1 / 2 := by
        rw [norm_div]
        apply (div_lt_iff₀ hdenomPos).2
        have hdist' :
            ‖charFun (μ n : Measure ℝ) y - charFun (μ₀ : Measure ℝ) y‖ <
              m / 2 := by
          calc
            _ = ‖-(charFun (μ₀ : Measure ℝ) y - charFun (μ n : Measure ℝ) y)‖ := by
              congr 1
              ring
            _ = ‖charFun (μ₀ : Measure ℝ) y - charFun (μ n : Measure ℝ) y‖ :=
              norm_neg _
            _ < m / 2 := by simpa [dist_eq_norm] using hdist
        nlinarith
      rw [show zratio y - 1 =
          (charFun (μ n : Measure ℝ) y - charFun (μ₀ : Measure ℝ) y) /
            charFun (μ₀ : Measure ℝ) y by
        dsimp [zratio]
        field_simp [h₀ne y]]
      exact hquot
    have hratioSlit (y : K) : zratio y ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have hreNorm : |(zratio y - 1).re| ≤ ‖zratio y - 1‖ := Complex.abs_re_le_norm _
      have hnegAbs : -|(zratio y - 1).re| ≤ (zratio y - 1).re := neg_abs_le _
      have hsmall := hratioClose y
      change |(zratio y).re - 1| ≤ ‖zratio y - 1‖ at hreNorm
      change -|(zratio y).re - 1| ≤ (zratio y).re - 1 at hnegAbs
      norm_num at hsmall ⊢
      nlinarith
    have hratioContinuous : Continuous zratio := by
      apply Continuous.div
      · exact (continuous_charFun (μ := (μ n : Measure ℝ))).comp continuous_subtype_val
      · exact (continuous_charFun (μ := (μ₀ : Measure ℝ))).comp continuous_subtype_val
      · intro y
        exact h₀ne y
    have hlogContinuous : Continuous (fun y : K => Complex.log (zratio y)) :=
      hratioContinuous.clog hratioSlit
    let base : K := ⟨0, Set.left_mem_uIcc⟩
    let endpoint : K := ⟨t, Set.right_mem_uIcc⟩
    let target : C(K, {z : ℂ // z ≠ 0}) :=
      ⟨fun y => ⟨charFun (μ n : Measure ℝ) y, (hμ n).charFun_ne_zero y⟩,
        ((continuous_charFun (μ := (μ n : Measure ℝ))).comp
          continuous_subtype_val).subtype_mk _⟩
    let lift₁ : C(K, ℂ) :=
      ⟨fun y => (hμ n).exponent y,
        (hμ n).exponent.continuous.comp continuous_subtype_val⟩
    let lift₂ : C(K, ℂ) :=
      ⟨fun y => continuousExponent μ₀ h₀ne y + Complex.log (zratio y),
        ((continuous_continuousExponent μ₀ h₀ne).comp continuous_subtype_val).add
          hlogContinuous⟩
    have hbaseTarget :
        (⟨Complex.exp (0 : ℂ), Complex.exp_ne_zero 0⟩ : {z : ℂ // z ≠ 0}) =
          target base := by
      apply Subtype.ext
      simp [target, base]
    let hconvex : Convex ℝ K := convex_uIcc 0 t
    letI : ContractibleSpace K := hconvex.contractibleSpace hKne
    letI : LocallyPathConnectedSpace K := hconvex.locallyPathConnectedSpace
    have hlift₁ : lift₁ base = 0 ∧
        (fun z : ℂ =>
          (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ lift₁ =
          target := by
      constructor
      · simp [lift₁, base]
      · funext y
        apply Subtype.ext
        exact (hμ n).exp_exponent y
    have hlift₂ : lift₂ base = 0 ∧
        (fun z : ℂ =>
          (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ lift₂ =
          target := by
      constructor
      · simp [lift₂, base, zratio]
      · funext y
        apply Subtype.ext
        dsimp [lift₂, target]
        rw [Complex.exp_add, exp_continuousExponent,
          Complex.exp_log (div_ne_zero ((hμ n).charFun_ne_zero y) (h₀ne y))]
        field_simp [h₀ne y]
    have hliftsEqual : lift₁ = lift₂ := by
      exact (Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
        target base 0 hbaseTarget).unique hlift₁ hlift₂
    exact congrArg (fun f : C(K, ℂ) => f endpoint) hliftsEqual
  have hratioT : Tendsto
      (fun n => charFun (μ n : Measure ℝ) t / charFun (μ₀ : Measure ℝ) t)
      atTop (𝓝 1) := by
    have hpoint := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim t
    have hdiv := hpoint.div_const (charFun (μ₀ : Measure ℝ) t)
    rw [div_self (h₀ne t)] at hdiv
    exact hdiv
  have hlogT : Tendsto
      (fun n => Complex.log
        (charFun (μ n : Measure ℝ) t / charFun (μ₀ : Measure ℝ) t))
      atTop (𝓝 0) := by
    simpa using hratioT.clog (by rw [Complex.mem_slitPlane_iff]; exact Or.inl (by norm_num))
  have hsum : Tendsto
      (fun n => continuousExponent μ₀ h₀ne t + Complex.log
        (charFun (μ n : Measure ℝ) t / charFun (μ₀ : Measure ℝ) t))
      atTop (𝓝 (continuousExponent μ₀ h₀ne t)) := by
    simpa using
      (tendsto_const_nhds.add hlogT :
        Tendsto
          (fun n => continuousExponent μ₀ h₀ne t + Complex.log
            (charFun (μ n : Measure ℝ) t / charFun (μ₀ : Measure ℝ) t))
          atTop (𝓝 (continuousExponent μ₀ h₀ne t + 0)))
  apply hsum.congr'
  filter_upwards [hexponentEventually] with n hn
  exact hn.symm

/-- The class of infinitely divisible probability laws on the real line is closed under weak
convergence.  For each positive `m`, the canonical `m`-th roots of the approximating laws have
characteristic functions converging to the exponential of one `m`-th of the limiting continuous
exponent.  Levy's continuity theorem realizes this limit as a probability law, whose `m`-fold
convolution is the prescribed weak limit. -/
theorem isInfinitelyDivisible_of_tendsto
    {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n).IsInfinitelyDivisible)
    (hlim : Tendsto μ atTop (𝓝 μ₀)) :
    μ₀.IsInfinitelyDivisible := by
  let h₀ne : ∀ t, charFun (μ₀ : Measure ℝ) t ≠ 0 :=
    charFun_ne_zero_of_tendsto_infinitelyDivisible hμ hlim
  intro m hm
  let φ : ℝ → ℂ := fun t =>
    Complex.exp (continuousExponent μ₀ h₀ne t / (m : ℂ))
  have hφ : ContinuousAt φ 0 := by
    exact (Complex.continuous_exp.comp
      ((continuous_continuousExponent μ₀ h₀ne).div_const (m : ℂ))).continuousAt
  have hchar (t : ℝ) :
      Tendsto
        (fun n => charFun ((hμ n).nthRoot m hm : Measure ℝ) t)
        atTop (𝓝 (φ t)) := by
    rw [show (fun n => charFun ((hμ n).nthRoot m hm : Measure ℝ) t) =
        fun n => Complex.exp ((hμ n).exponent t / (m : ℂ)) by
      funext n
      exact (hμ n).charFun_nthRoot m hm t]
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_continuousExponent_of_tendsto_infinitelyDivisible hμ hlim t).div_const
        (m : ℂ))
  obtain ⟨ρ, hρchar, -⟩ :=
    exists_probabilityMeasure_of_tendsto_charFun hφ hchar
  refine ⟨ρ, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [ProbabilityMeasure.charFun_convPow_real, hρchar]
  dsimp [φ]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : (m : ℂ) * (continuousExponent μ₀ h₀ne t / (m : ℂ)) =
      continuousExponent μ₀ h₀ne t := by
    field_simp
  rw [← Complex.exp_nat_mul, hmul, exp_continuousExponent]

end ProbabilityTheory
