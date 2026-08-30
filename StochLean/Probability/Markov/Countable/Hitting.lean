/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Chain.PathLaw
public import Mathlib.Probability.Kernel.Irreducible
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Data.Real.ENatENNReal

/-!
# Reachability and strict-positive hitting

Reachability uses kernel powers and therefore permits time zero.  Strict return quantities use
Mathlib's `hittingAfter` with lower bound one; the distinction is intentional, especially on the
diagonal.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

namespace Kernel

variable {E : Type*} [MeasurableSpace E]

/-- Pairwise reachability by a nonnegative number of kernel steps.  In particular every state can
reach itself at time zero. -/
def CanReach (κ : Kernel E E) (x y : E) : Prop :=
  ∃ n : ℕ, (κ ^ n) x {y} > 0

theorem canReach_self (κ : Kernel E E) (x : E) [MeasurableSingletonClass E] :
    κ.CanReach x x := by
  refine ⟨0, ?_⟩
  change 0 < Kernel.id x {x}
  rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton x)]
  simpa using (zero_lt_one : (0 : ℝ≥0∞) < 1)

theorem CanReach.trans {κ : Kernel E E} [IsMarkovKernel κ]
    {x y z : E} [MeasurableSingletonClass E]
    (hxy : κ.CanReach x y) (hyz : κ.CanReach y z) : κ.CanReach x z := by
  obtain ⟨m, hm⟩ := hxy
  obtain ⟨n, hn⟩ := hyz
  refine ⟨m + n, ?_⟩
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  change 0 < ∫⁻ a, (κ ^ n) a {z} ∂(κ ^ m) x
  rw [lintegral_pos_iff_support ((κ ^ n).measurable_coe (measurableSet_singleton z))]
  exact lt_of_lt_of_le hm (measure_mono (fun a ha => by
    have hay : a = y := Set.mem_singleton_iff.mp ha
    subst a
    exact hn.ne'))

/-- On a countable discrete measurable space, Mathlib's count-measure irreducibility is exactly
pairwise reachability by kernel powers. -/
theorem isIrreducible_count_iff_forall_canReach
    [Countable E] [MeasurableSingletonClass E] (κ : Kernel E E) :
    Kernel.IsIrreducible Measure.count κ ↔ ∀ x y : E, κ.CanReach x y := by
  constructor
  · intro h x y
    obtain ⟨n, hn⟩ := h.irreducible (measurableSet_singleton y) (by simp) x
    exact ⟨n, hn⟩
  · intro h
    constructor
    intro A hA hcount x
    have hne : A.Nonempty := nonempty_of_measure_ne_zero (ne_of_lt hcount).symm
    obtain ⟨y, hy⟩ := hne
    obtain ⟨n, hn⟩ := h x y
    refine ⟨n, hn.trans_le (measure_mono ?_)⟩
    simpa only [Set.singleton_subset_iff] using hy

end Kernel

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- First entrance into `A` at a strictly positive discrete time.  Infinity is retained when the
set is never hit. -/
noncomputable def firstPositiveHittingTime (X : ℕ → Ω → E) (A : Set E) : Ω → ℕ∞ :=
  hittingAfter X A 1

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The strict-positive hitting time is the corresponding Mathlib hitting time after one. -/
theorem firstPositiveHittingTime_eq_hittingAfter (X : ℕ → Ω → E) (A : Set E) :
    firstPositiveHittingTime X A = hittingAfter X A 1 :=
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- A strict-positive hitting time is at least one. -/
theorem one_le_firstPositiveHittingTime (X : ℕ → Ω → E) (A : Set E) (ω : Ω) :
    (1 : ℕ∞) ≤ firstPositiveHittingTime X A ω :=
  le_hittingAfter ω

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- A strict-positive hitting time is infinite exactly when the set is never visited later. -/
theorem firstPositiveHittingTime_eq_top_iff (X : ℕ → Ω → E) (A : Set E) (ω : Ω) :
    firstPositiveHittingTime X A ω = (⊤ : ℕ∞) ↔ ∀ n : ℕ, 1 ≤ n → X n ω ∉ A := by
  change hittingAfter X A 1 ω = ⊤ ↔ _
  constructor
  · intro h j hj
    exact (hittingAfter_eq_top_iff (u := X) (s := A) (n := 1) (ω := ω)).mp h j hj
  · intro h
    exact (hittingAfter_eq_top_iff (u := X) (s := A) (n := 1) (ω := ω)).mpr h

variable [MeasurableSingletonClass E]

/-- Strict-positive hitting probability for the canonical chain started at `x`. -/
noncomputable def returnProbability (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) : ℝ≥0∞ :=
  markovChainLaw κ x
    {ω | firstPositiveHittingTime (fun n z => z n) {y} ω < ∞}

omit [MeasurableSingletonClass E] in
/-- A return probability is at most one. -/
theorem returnProbability_le_one (κ : Kernel E E) [IsMarkovKernel κ] (x y : E) :
    returnProbability κ x y ≤ 1 := by
  calc
    returnProbability κ x y ≤ markovChainLaw κ x Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

end ProbabilityTheory
