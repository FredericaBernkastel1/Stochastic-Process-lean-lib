/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/
module

public import StochLean.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform

/-!
# Semantic regressions for projective constructions

These declarations pin the direction of projectivity, cylinder generation, arbitrary products,
Ionescu--Tulcea reuse, empty-index behavior, finite-dimensional recovery, and the distinction
between finite and probability projective families.  The canonical process is only the raw
coordinate map on the product sample space.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory

noncomputable section

/- Coordinate maps and measurable cylinders use Mathlib's product measurable space. -/
example {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (i : ι) :
    Measurable (fun x : ∀ i, α i ↦ x i) :=
  measurable_pi_apply i

example {ι : Type*} (α : ι → Type*) [∀ i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (measurableCylinders α) = MeasurableSpace.pi :=
  generateFrom_measurableCylinders

/- Projectivity has the deliberate direction `P J = map restrict (P I)` for `J ⊆ I`. -/
example {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {P : ∀ J : Finset ι, Measure (∀ j : J, α j)} (hP : IsProjectiveMeasureFamily P)
    (I J : Finset ι) (hJI : J ⊆ I) :
    P J = (P I).map (Finset.restrict₂ hJI) :=
  hP I J hJI

/- Mathlib's arbitrary product is already a projective limit and has exact cylinder values. -/
example {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] (J : Finset ι) :
    (Measure.infinitePi μ).map J.restrict = Measure.pi (fun j : J ↦ μ j) :=
  Measure.infinitePi_map_restrict μ

example {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (J : Finset ι) (s : Set (∀ j : J, α j)) (hs : MeasurableSet s) :
    Measure.infinitePi μ (cylinder J s) = Measure.pi (fun j : J ↦ μ j) s :=
  Measure.infinitePi_cylinder μ hs

/- The standard-Borel facade exposes no topology in this compile-time public-domain test. -/
example {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, StandardBorelSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)] (hP : IsProjectiveMeasureFamily P) (J : Finset ι) :
    (projectiveLimitOfStandardBorel P hP).map J.restrict = P J :=
  projectiveLimitOfStandardBorel_map_restrict P hP J

/- A concrete three-coordinate family recovers every prescribed marginal. -/
def fairBoolMeasure : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairBoolMeasure := by
  dsimp only [fairBoolMeasure]
  infer_instance

def threeCoinFamily (J : Finset (Fin 3)) : Measure (∀ _ : J, Bool) :=
  Measure.pi (fun _ : J ↦ fairBoolMeasure)

instance (J : Finset (Fin 3)) : IsProbabilityMeasure (threeCoinFamily J) := by
  dsimp only [threeCoinFamily]
  infer_instance

theorem threeCoinFamily_isProjective :
    IsProjectiveMeasureFamily (α := fun _ : Fin 3 ↦ Bool) threeCoinFamily :=
  isProjectiveMeasureFamily_pi (fun _ : Fin 3 ↦ fairBoolMeasure)

theorem threeCoin_projectiveLimit_recovers (J : Finset (Fin 3)) :
    (projectiveLimitOfStandardBorel (α := fun _ : Fin 3 ↦ Bool)
      threeCoinFamily threeCoinFamily_isProjective).map
        J.restrict = threeCoinFamily J :=
  projectiveLimitOfStandardBorel_map_restrict _ threeCoinFamily_isProjective J

instance : IsProbabilityMeasure
    (projectiveLimitOfStandardBorel (α := fun _ : Fin 3 ↦ Bool)
      threeCoinFamily threeCoinFamily_isProjective) :=
  inferInstance

/- Empty index types require no artificial `Nonempty ι` hypothesis. -/
def emptyCoordinateMeasure (i : Empty) : Measure Unit := nomatch i

instance (i : Empty) : IsProbabilityMeasure (emptyCoordinateMeasure i) := nomatch i

def emptyProductFamily (J : Finset Empty) : Measure (∀ _ : J, Unit) :=
  Measure.pi (fun j : J ↦ emptyCoordinateMeasure j)

instance (J : Finset Empty) : IsProbabilityMeasure (emptyProductFamily J) := by
  dsimp only [emptyProductFamily]
  infer_instance

theorem emptyProductFamily_isProjective :
    IsProjectiveMeasureFamily (α := fun _ : Empty ↦ Unit) emptyProductFamily :=
  isProjectiveMeasureFamily_pi emptyCoordinateMeasure

theorem emptyIndex_projectiveLimit_isProbability :
    IsProbabilityMeasure
      (projectiveLimitOfStandardBorel (α := fun _ : Empty ↦ Unit)
        emptyProductFamily emptyProductFamily_isProjective) :=
  inferInstance

theorem emptyIndex_existsUnique_projectiveLimit :
    ∃! μ : Measure (∀ _ : Empty, Unit), IsProjectiveLimit μ emptyProductFamily :=
  existsUnique_isProjectiveLimit_of_standardBorel
    (α := fun _ : Empty ↦ Unit) emptyProductFamily emptyProductFamily_isProjective

/- Finite mass alone is not probability mass. -/
def twoMassFiniteFamily (J : Finset Bool) : Measure (∀ _ : J, Unit) :=
  (2 : ℝ≥0∞) • Measure.dirac (fun _ ↦ ())

instance (J : Finset Bool) : IsFiniteMeasure (twoMassFiniteFamily J) := by
  constructor
  simp [twoMassFiniteFamily]

theorem twoMassFiniteFamily_isProjective :
    IsProjectiveMeasureFamily (α := fun _ : Bool ↦ Unit) twoMassFiniteFamily := by
  intro I J hJI
  simp only [twoMassFiniteFamily, Measure.map_smul]
  rw [Measure.map_dirac]

def twoMassLimit : Measure (Bool → Unit) :=
  (2 : ℝ≥0∞) • Measure.dirac (fun _ ↦ ())

theorem twoMassLimit_isProjectiveLimit :
    IsProjectiveLimit (α := fun _ : Bool ↦ Unit) twoMassLimit twoMassFiniteFamily := by
  intro I
  simp only [twoMassLimit, twoMassFiniteFamily, Measure.map_smul]
  rw [Measure.map_dirac]

theorem twoMassLimit_not_isProbabilityMeasure : ¬ IsProbabilityMeasure twoMassLimit := by
  intro h
  have hone := h.measure_univ
  simp [twoMassLimit] at hone

/- Ionescu--Tulcea remains the canonical sequential-kernel construction. -/
example {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (κ : (n : ℕ) → Kernel (∀ i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] :
    IsProbabilityMeasure (Kernel.trajMeasure μ₀ κ) :=
  inferInstance

example {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (∀ i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (a : ℕ) :
    IsMarkovKernel (Kernel.traj κ a) :=
  inferInstance

end

end MeasureTheory
