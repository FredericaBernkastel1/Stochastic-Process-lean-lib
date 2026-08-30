/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.Probability.Markov.Transition
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Canonical path law of a discrete Markov chain

This is a thin homogeneous specialization of Mathlib's Ionescu-Tulcea trajectory kernel.  It does
not introduce a bundled Markov-chain object or a second trajectory-measure construction.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The unique constant time-zero history determined by a starting state. -/
def markovChainInitialHistory (x : E) (_ : Finset.Iic 0) : E := x

theorem measurable_markovChainInitialHistory :
    Measurable (markovChainInitialHistory : E → (Finset.Iic 0 → E)) := by
  rw [measurable_pi_iff]
  exact fun _ => measurable_id

/-- The history-dependent kernel supplied to Ionescu-Tulcea by a homogeneous one-step kernel. -/
noncomputable def markovChainStep (κ : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E :=
  κ.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

/-- Evaluation of the homogeneous history kernel only reads the current endpoint. -/
theorem markovChainStep_apply (κ : Kernel E E) (n : ℕ)
    (z : (i : Finset.Iic n) → E) :
    markovChainStep κ n z = κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  rw [markovChainStep, Kernel.comap_apply]

instance markovChainStep.instIsMarkovKernel (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovChainStep κ n) := by
  unfold markovChainStep
  infer_instance

/-- Canonical path kernel starting from a fixed state and iterating `κ`. -/
noncomputable def markovChainPathKernel (κ : Kernel E E) [IsMarkovKernel κ] :
    Kernel E (ℕ → E) :=
  (Kernel.traj (markovChainStep κ) 0).comap
    (fun x (_ : Finset.Iic 0) => x) (by
      rw [measurable_pi_iff]
      exact fun _ => measurable_id)

instance markovChainPathKernel.instIsMarkovKernel (κ : Kernel E E) [IsMarkovKernel κ] :
    IsMarkovKernel (markovChainPathKernel κ) := by
  unfold markovChainPathKernel
  infer_instance

/-- The canonical path law when the chain starts at `x`. -/
noncomputable def markovChainLaw (κ : Kernel E E) [IsMarkovKernel κ] (x : E) : Measure (ℕ → E) :=
  markovChainPathKernel κ x

instance markovChainLaw.instIsProbabilityMeasure (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    IsProbabilityMeasure (markovChainLaw κ x) := by
  exact (markovChainPathKernel.instIsMarkovKernel κ).isProbabilityMeasure x

/-- The `n`th-coordinate marginal kernel obtained from the finite Ionescu--Tulcea trajectory. -/
noncomputable def markovChainMarginalKernel
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) : Kernel E E :=
  ((Kernel.partialTraj (X := fun _ => E) (markovChainStep κ) 0 n).map
      (fun z : (i : Finset.Iic n) → E => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).comap
    markovChainInitialHistory measurable_markovChainInitialHistory

/-- Finite-trajectory marginals satisfy the usual homogeneous recursion. -/
theorem markovChainMarginalKernel_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    markovChainMarginalKernel κ (n + 1) = κ ∘ₖ markovChainMarginalKernel κ n := by
  rw [markovChainMarginalKernel,
    Kernel.partialTraj_succ_eq_comp (X := fun _ => E) (Nat.zero_le n),
    Kernel.map_comp,
    Kernel.map_partialTraj_succ_self (X := fun _ => E)]
  change
    ((κ.comap (fun z => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)) ∘ₖ
      Kernel.partialTraj (X := fun _ => E) (markovChainStep κ) 0 n).comap _ _ = _
  rw [← Kernel.comp_map]
  rw [← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc,
    Kernel.comp_deterministic_eq_comap]
  rfl

/-- The finite-trajectory marginal kernel is exactly the corresponding kernel power. -/
theorem markovChainMarginalKernel_eq_pow
    (κ : Kernel E E) [IsMarkovKernel κ] :
    ∀ n : ℕ, markovChainMarginalKernel κ n = κ ^ n
  | 0 => by
      rw [markovChainMarginalKernel, Kernel.partialTraj_self,
        Kernel.id_map (measurable_pi_apply _)]
      change Kernel.deterministic id measurable_id = Kernel.id
      rfl
  | n + 1 => by
      rw [markovChainMarginalKernel_succ, markovChainMarginalKernel_eq_pow, pow_succ']
      rfl

/-- The endpoint marginal of a trajectory restarted from a history at time `b`. -/
noncomputable def markovChainFutureMarginalKernel
    (κ : Kernel E E) [IsMarkovKernel κ] (b n : ℕ) :
    Kernel ((i : Finset.Iic b) → E) E :=
  (Kernel.partialTraj (X := fun _ => E) (markovChainStep κ) b (b + n)).map
    (fun z : (i : Finset.Iic (b + n)) → E =>
      z ⟨b + n, Finset.mem_Iic.mpr le_rfl⟩)

/-- Restarting from a finite history and advancing `n` steps depends only on its endpoint and
applies the `n`th kernel power. -/
theorem markovChainFutureMarginalKernel_eq_pow_comap
    (κ : Kernel E E) [IsMarkovKernel κ] (b : ℕ) :
    ∀ n : ℕ, markovChainFutureMarginalKernel κ b n =
      (κ ^ n).comap
        (fun z : (i : Finset.Iic b) → E => z ⟨b, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) := by
  intro n
  induction n with
  | zero =>
      simp only [markovChainFutureMarginalKernel, Nat.add_zero]
      rw [Kernel.partialTraj_self, Kernel.id_map (measurable_pi_apply _)]
      change Kernel.deterministic _ _ = Kernel.id.comap _ _
      rw [Kernel.id]
      exact Kernel.deterministic_congr rfl
  | succ n ih =>
      simp only [markovChainFutureMarginalKernel, Nat.add_succ]
      rw [Kernel.partialTraj_succ_eq_comp (X := fun _ => E) (Nat.le_add_right b n),
        Kernel.map_comp, Kernel.map_partialTraj_succ_self (X := fun _ => E)]
      change
        (κ.comap (fun z => z ⟨b + n, Finset.mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _)) ∘ₖ
          Kernel.partialTraj (X := fun _ => E) (markovChainStep κ) b (b + n) = _
      rw [← Kernel.comp_map]
      rw [show
        (Kernel.partialTraj (X := fun _ => E) (markovChainStep κ) b (b + n)).map
          (fun z => z ⟨b + n, Finset.mem_Iic.mpr le_rfl⟩) =
            markovChainFutureMarginalKernel κ b n by rfl]
      rw [ih]
      rw [← Kernel.comp_deterministic_eq_comap,
        ← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_assoc]
      simp only [Nat.add_zero]
      rw [pow_succ']
      rfl

/-- The path kernel is definitionally the Ionescu-Tulcea trajectory kernel pulled back along the
unique time-zero history. -/
theorem markovChainPathKernel_apply (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    markovChainPathKernel κ x =
      Kernel.traj (markovChainStep κ) 0 (fun _ => x) :=
  rfl

/-- The path law is the value of the canonical path kernel. -/
theorem markovChainLaw_eq (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    markovChainLaw κ x = markovChainPathKernel κ x :=
  rfl

/-- Direct trajectory-kernel form of the canonical chain law. -/
theorem markovChainLaw_eq_traj (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    markovChainLaw κ x = Kernel.traj (markovChainStep κ) 0 (fun _ => x) :=
  rfl

section PathMap

variable {F : Type*} [MeasurableSpace F]

/-- Apply a state-space map to every entry of a finite history. -/
def historyMap (f : E → F) (n : ℕ) :
    ((i : Finset.Iic n) → E) → ((i : Finset.Iic n) → F) :=
  fun z i => f (z i)

theorem measurable_historyMap {f : E → F} (hf : Measurable f) (n : ℕ) :
    Measurable (historyMap f n) := by
  rw [measurable_pi_iff]
  intro i
  exact hf.comp (measurable_pi_apply i)

/-- Apply a state-space map coordinatewise to an infinite path. -/
def pathMap (f : E → F) : (ℕ → E) → (ℕ → F) :=
  fun z n => f (z n)

theorem measurable_pathMap {f : E → F} (hf : Measurable f) :
    Measurable (pathMap f) := by
  rw [measurable_pi_iff]
  intro n
  exact hf.comp (measurable_pi_apply n)

theorem markovChainStep_map
    (K : Kernel E E) (κ : Kernel F F) {f : E → F} (hf : Measurable f)
    (hmap : K.map f = κ.comap f hf) (n : ℕ) :
    (markovChainStep K n).map f =
      (markovChainStep κ n).comap (historyMap f n)
        (measurable_historyMap hf n) := by
  rw [markovChainStep, markovChainStep]
  rw [← Kernel.comap_map_comm]
  rw [hmap]
  rw [← Kernel.comap_comp_right]
  rfl
  exact hf

private def iocMap (f : E → F) (n : ℕ) :
    ((i : Finset.Ioc n (n + 1)) → E) → ((i : Finset.Ioc n (n + 1)) → F) :=
  fun z i => f (z i)

private theorem measurable_iocMap {f : E → F} (hf : Measurable f) (n : ℕ) :
    Measurable (iocMap f n) := by
  rw [measurable_pi_iff]
  intro i
  exact hf.comp (measurable_pi_apply i)

private theorem historyMap_IicProdIoc {f : E → F} (n : ℕ) :
    historyMap f (n + 1) ∘
        (IicProdIoc (X := fun _ : ℕ => E) n (n + 1)) =
      (IicProdIoc (X := fun _ : ℕ => F) n (n + 1)) ∘
        Prod.map (historyMap f n) (iocMap f n) := by
  funext z i
  simp only [Function.comp_apply, historyMap, iocMap, IicProdIoc_def,
    Prod.map_fst, Prod.map_snd]
  split_ifs <;> rfl

private theorem iocMap_piSingleton {f : E → F} (n : ℕ) :
    iocMap f n ∘
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => E) n) =
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => F) n) ∘ f := by
  funext z i
  simp [iocMap, MeasurableEquiv.piSingleton]

private theorem partialTraj_succ_self_map
    (K : Kernel E E) (κ : Kernel F F) [IsMarkovKernel K] [IsMarkovKernel κ]
    {f : E → F} (hf : Measurable f)
    (hmap : K.map f = κ.comap f hf) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => E) (markovChainStep K) n (n + 1)).map
        (historyMap f (n + 1)) =
      (Kernel.partialTraj (X := fun _ : ℕ => F) (markovChainStep κ) n (n + 1)).comap
        (historyMap f n) (measurable_historyMap hf n) := by
  rw [Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self]
  rw [← Kernel.map_comp_right]
  rw [historyMap_IicProdIoc]
  rw [Kernel.map_comp_right]
  rw [← Kernel.map_prod_map]
  rw [Kernel.id_map]
  rw [← Kernel.map_comp_right]
  rw [iocMap_piSingleton]
  rw [Kernel.map_comp_right]
  rw [markovChainStep_map K κ hf hmap n]
  rw [← Kernel.comap_map_comm]
  rw [← Kernel.id_comap]
  rw [← Kernel.comap_prod]
  rw [Kernel.comap_map_comm]
  all_goals
    first
    | exact measurable_historyMap hf n
    | exact measurable_historyMap hf (n + 1)
    | exact measurable_iocMap hf n
    | exact (measurable_historyMap hf n).comp measurable_fst |>.prodMk
        ((measurable_iocMap hf n).comp measurable_snd)
    | exact measurable_IicProdIoc
    | exact (MeasurableEquiv.piSingleton _).measurable
    | exact hf
    | infer_instance

theorem partialTraj_map
    (K : Kernel E E) (κ : Kernel F F) [IsMarkovKernel K] [IsMarkovKernel κ]
    {f : E → F} (hf : Measurable f)
    (hmap : K.map f = κ.comap f hf) :
    ∀ n : ℕ,
      (Kernel.partialTraj (X := fun _ : ℕ => E) (markovChainStep K) 0 n).map
          (historyMap f n) =
        (Kernel.partialTraj (X := fun _ : ℕ => F) (markovChainStep κ) 0 n).comap
          (historyMap f 0) (measurable_historyMap hf 0)
  | 0 => by
      rw [Kernel.partialTraj_self, Kernel.partialTraj_self,
        Kernel.id_map, Kernel.id_comap]
  | n + 1 => by
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
        Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.map_comp]
      rw [partialTraj_succ_self_map K κ hf hmap n]
      rw [← Kernel.comp_map]
      rw [partialTraj_map K κ hf hmap n]
      rw [← Kernel.comp_deterministic_eq_comap, ← Kernel.comp_assoc,
        Kernel.comp_deterministic_eq_comap]

theorem frestrictLe_pathMap {f : E → F} (n : ℕ) :
    Preorder.frestrictLe n ∘ pathMap f =
      historyMap f n ∘ Preorder.frestrictLe n := by
  rfl

-- Projective-limit uniqueness expands many dependent finite-coordinate maps during elaboration.
set_option maxHeartbeats 1000000 in
/-- Functoriality of the canonical Markov-chain law: a measurable state-space map which
intertwines the one-step kernels also intertwines the entire path laws. -/
theorem markovChainLaw_map
    (K : Kernel E E) (κ : Kernel F F) [IsMarkovKernel K] [IsMarkovKernel κ]
    {f : E → F} (hf : Measurable f)
    (hmap : K.map f = κ.comap f hf) (x : E) :
    Measure.map (pathMap f) (markovChainLaw K x) =
      markovChainLaw κ (f x) := by
  let μsource : Measure (ℕ → F) :=
    Measure.map (pathMap f) (markovChainLaw K x)
  let xF : (i : Finset.Iic 0) → F := historyMap f 0 (fun _ => x)
  let P : (J : Finset ℕ) → Measure (J → F) :=
    MeasureTheory.inducedFamily (X := fun _ : ℕ => F) fun n =>
      Kernel.partialTraj (X := fun _ : ℕ => F) (markovChainStep κ) 0 n xF
  have htarget : IsProjectiveLimit (α := fun _ : ℕ => F)
      (Kernel.trajFun (markovChainStep κ) 0 xF) P := by
    exact Kernel.isProjectiveLimit_trajFun
      (X := fun _ : ℕ => F) (κ := markovChainStep κ) 0 xF
  letI (n : ℕ) : IsProbabilityMeasure
      (Kernel.partialTraj (X := fun _ : ℕ => F) (markovChainStep κ) 0 n xF) := by
    infer_instance
  letI (J : Finset ℕ) : IsProbabilityMeasure (P J) := by
    dsimp only [P]
    infer_instance
  have hsource : IsProjectiveLimit (α := fun _ : ℕ => F) μsource P := by
    change IsProjectiveLimit (α := fun _ : ℕ => F) μsource
      (MeasureTheory.inducedFamily (X := fun _ : ℕ => F) fun n =>
        Kernel.partialTraj (X := fun _ : ℕ => F) (markovChainStep κ) 0 n xF)
    rw [MeasureTheory.isProjectiveLimit_nat_iff
      (Kernel.isProjectiveMeasureFamily_partialTraj
        (X := fun _ : ℕ => F) (markovChainStep κ) xF)]
    intro n
    rw [MeasureTheory.inducedFamily_Iic]
    simp only [μsource]
    rw [Measure.map_map (Preorder.measurable_frestrictLe n)
      (measurable_pathMap hf)]
    rw [frestrictLe_pathMap]
    rw [← Measure.map_map (measurable_historyMap hf n)
      (Preorder.measurable_frestrictLe n)]
    rw [markovChainLaw_eq_traj,
      Kernel.traj_map_frestrictLe_apply]
    have hpartial := congrArg
      (fun L : Kernel ((i : Finset.Iic 0) → E) ((i : Finset.Iic n) → F) =>
        L (fun _ => x))
      (partialTraj_map K κ hf hmap n)
    rw [Kernel.map_apply _ (measurable_historyMap hf n),
      Kernel.comap_apply] at hpartial
    simpa only [xF] using hpartial
  have heq := htarget.unique hsource
  rw [← Kernel.traj_apply] at heq
  have hxF : xF = fun _ => f x := by rfl
  rw [hxF] at heq
  simpa only [μsource, markovChainLaw_eq_traj] using heq.symm

end PathMap

/-- The one-time marginal of the canonical path kernel is the corresponding kernel power. -/
theorem markovChainPathKernel_map_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    (markovChainPathKernel κ).map (fun z : ℕ → E => z n) = κ ^ n := by
  rw [markovChainPathKernel]
  change
    ((Kernel.traj (markovChainStep κ) 0).comap markovChainInitialHistory
      measurable_markovChainInitialHistory).map (fun z : ℕ → E => z n) = κ ^ n
  rw [← (Kernel.comap_map_comm (Kernel.traj (markovChainStep κ) 0)
      (f := markovChainInitialHistory) (g := fun z : ℕ → E => z n)
      measurable_markovChainInitialHistory (measurable_pi_apply n))]
  have heval :
      (fun z : ℕ → E => z n) =
        (fun z : (i : Finset.Iic n) → E => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ∘
          Preorder.frestrictLe n := rfl
  rw [heval, Kernel.map_comp_right _
    (Preorder.measurable_frestrictLe (X := fun _ => E) n) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe (X := fun _ => E) (κ := markovChainStep κ) 0 n]
  change markovChainMarginalKernel κ n = κ ^ n
  exact markovChainMarginalKernel_eq_pow κ n

/-- The `n`th coordinate under the canonical chain law has distribution `κ ^ n`. -/
theorem markovChainLaw_map_apply
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ) :
    (markovChainLaw κ x).map (fun z : ℕ → E => z n) = (κ ^ n) x := by
  rw [markovChainLaw, ← Kernel.map_apply _ (measurable_pi_apply n),
    markovChainPathKernel_map_apply]

/-- Measurable-set form of the canonical one-time marginal formula. -/
theorem markovChainLaw_apply_coordinate
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    markovChainLaw κ x {z | z n ∈ A} = (κ ^ n) x A := by
  change markovChainLaw κ x ((fun z : ℕ → E => z n) ⁻¹' A) = (κ ^ n) x A
  rw [← Measure.map_apply (measurable_pi_apply n) hA, markovChainLaw_map_apply]

/-- The joint law of two adjacent coordinates is obtained by integrating one transition from
the first coordinate marginal. -/
theorem markovChainLaw_inter_coordinate_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) (n : ℕ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    markovChainLaw κ x
        ({z : ℕ → E | z n ∈ A} ∩ {z : ℕ → E | z (n + 1) ∈ B}) =
      ∫⁻ y in A, κ y B ∂(κ ^ n) x := by
  let H : Set ((i : Finset.Iic n) → E) :=
    {z | z ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ A}
  have hH : MeasurableSet H := by
    change MeasurableSet
      ((fun z : (i : Finset.Iic n) → E =>
        z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ⁻¹' A)
    exact (measurable_pi_apply
      (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)) hA
  have hcomp := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => E) (κ := markovChainStep κ)
    (a := 0) (b := n) (Nat.zero_le n)
    (x₀ := fun _ => x)
  have heval := congrArg (fun μ : Measure (((i : Finset.Iic n) → E) × E) =>
      μ (H ×ˢ B)) hcomp
  rw [Measure.compProd_apply_prod hH hB] at heval
  rw [Measure.map_apply] at heval
  · rw [← markovChainLaw_eq_traj κ x] at heval
    rw [show (fun z : ℕ → E => (Preorder.frestrictLe n z, z (n + 1))) ⁻¹'
        (H ×ˢ B) =
        {z : ℕ → E | z n ∈ A} ∩ {z : ℕ → E | z (n + 1) ∈ B} by
      ext z
      rfl] at heval
    rw [← markovChainMarginalKernel_eq_pow κ n]
    change _ = ∫⁻ y in A, κ y B ∂markovChainMarginalKernel κ n x
    rw [markovChainMarginalKernel]
    rw [Kernel.comap_apply]
    rw [Kernel.map_apply _ (measurable_pi_apply _)]
    rw [setLIntegral_map hA]
    · exact heval.symm
    · exact κ.measurable_coe hB
    · exact measurable_pi_apply _
  · exact (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  · exact hH.prod hB

/-- Integrating a one-step coordinate event against a trajectory restarted from a finite history
evaluates the one-step kernel at the endpoint of that history. -/
theorem integral_eventIndicator_traj_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ)
    (z : (i : Finset.Iic n) → E) {A : Set E} (hA : MeasurableSet A) :
    ∫ y, eventIndicator (fun w : ℕ → E => w (n + 1)) A y
        ∂Kernel.traj (markovChainStep κ) n z =
      transitionProbability κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A := by
  have hset : MeasurableSet {y : ℕ → E | y (n + 1) ∈ A} :=
    (measurable_pi_apply (n + 1)) hA
  rw [show eventIndicator (fun w : ℕ → E => w (n + 1)) A =
      {y : ℕ → E | y (n + 1) ∈ A}.indicator (fun _ => (1 : ℝ)) by rfl,
    integral_indicator_const (1 : ℝ) hset]
  simp only [smul_eq_mul, mul_one]
  change (Kernel.traj (markovChainStep κ) n z).real
      {y : ℕ → E | y (n + 1) ∈ A} = _
  rw [Measure.real]
  change ((Kernel.traj (markovChainStep κ) n z)
      ((fun y : ℕ → E => y (n + 1)) ⁻¹' A)).toReal = _
  rw [← Measure.map_apply (measurable_pi_apply (n + 1)) hA]
  rw [← Kernel.map_apply _ (measurable_pi_apply (n + 1)),
    Kernel.map_traj_succ_self, markovChainStep_apply, transitionProbability]

/-- A trajectory restarted from a finite history has the expected homogeneous multi-step
endpoint probability. -/
theorem integral_eventIndicator_traj_add
    (κ : Kernel E E) [IsMarkovKernel κ] (b n : ℕ)
    (z : (i : Finset.Iic b) → E) {A : Set E} (hA : MeasurableSet A) :
    ∫ y, eventIndicator (fun w : ℕ → E => w (b + n)) A y
        ∂Kernel.traj (markovChainStep κ) b z =
      transitionProbability (κ ^ n)
        (z ⟨b, Finset.mem_Iic.mpr le_rfl⟩) A := by
  have hset : MeasurableSet {y : ℕ → E | y (b + n) ∈ A} :=
    (measurable_pi_apply (b + n)) hA
  rw [show eventIndicator (fun w : ℕ → E => w (b + n)) A =
      {y : ℕ → E | y (b + n) ∈ A}.indicator (fun _ => (1 : ℝ)) by rfl,
    integral_indicator_const (1 : ℝ) hset]
  simp only [smul_eq_mul, mul_one]
  change (Kernel.traj (markovChainStep κ) b z).real
      {y : ℕ → E | y (b + n) ∈ A} = _
  rw [Measure.real]
  change ((Kernel.traj (markovChainStep κ) b z)
      ((fun y : ℕ → E => y (b + n)) ⁻¹' A)).toReal = _
  rw [← Measure.map_apply (measurable_pi_apply (b + n)) hA]
  rw [← Kernel.map_apply _ (measurable_pi_apply (b + n))]
  have heval :
      (fun y : ℕ → E => y (b + n)) =
        (fun y : (i : Finset.Iic (b + n)) → E =>
          y ⟨b + n, Finset.mem_Iic.mpr le_rfl⟩) ∘
          Preorder.frestrictLe (b + n) := rfl
  rw [heval, Kernel.map_comp_right _
    (Preorder.measurable_frestrictLe (X := fun _ => E) (b + n))
    (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe (X := fun _ => E) (κ := markovChainStep κ) b (b + n)]
  change (markovChainFutureMarginalKernel κ b n z A).toReal = _
  rw [markovChainFutureMarginalKernel_eq_pow_comap, Kernel.comap_apply,
    transitionProbability]

/-- The extended nonnegative one-step event integral against a restarted trajectory is the kernel
mass at the endpoint of the finite history. -/
theorem lintegral_indicator_traj_succ
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ)
    (z : (i : Finset.Iic n) → E) {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ y, {w : ℕ → E | w (n + 1) ∈ A}.indicator (fun _ => (1 : ℝ≥0∞)) y
        ∂Kernel.traj (markovChainStep κ) n z =
      κ (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) A := by
  have hset : MeasurableSet {w : ℕ → E | w (n + 1) ∈ A} :=
    (measurable_pi_apply (n + 1)) hA
  rw [lintegral_indicator hset]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
  change (Kernel.traj (markovChainStep κ) n z)
      ((fun y : ℕ → E => y (n + 1)) ⁻¹' A) = _
  rw [← Measure.map_apply (measurable_pi_apply (n + 1)) hA,
    ← Kernel.map_apply _ (measurable_pi_apply (n + 1)),
    Kernel.map_traj_succ_self, markovChainStep_apply]

end ProbabilityTheory
