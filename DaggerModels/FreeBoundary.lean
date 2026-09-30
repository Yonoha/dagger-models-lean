import DaggerModels.FreeCofibrationClosure
import DaggerModels.FreeDaggerCofibration
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# The actual free dagger boundary generators

These are the generators in Part I, `dj.lem.free-cof`. Their saturation is
contained in the original free-cofibration class. The converse, which requires
constructing boundary attachments for every free cofibration, is not assumed.
The adjunction also gives the exact underlying boundary lifting condition.
-/

open CategoryTheory Limits Simplicial HomotopicalAlgebra

universe u

namespace DaggerModels

/-- The actual images of the standard boundary inclusions under the given free functor. -/
def freeBoundaryGenerators (F : SSet.{u} ⥤ DaggerSSet.{u}) :
    MorphismProperty DaggerSSet.{u} :=
  .ofHoms (fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι)

/-- The given genuine free functor sends every boundary inclusion to a free cofibration. -/
theorem freeBoundaryGenerators_le (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) :
    freeBoundaryGenerators F ≤ DaggerSSet.freeCofibrations := by
  intro X Y f hf
  cases hf with
  | mk n => exact freeDagger_map_freeCofibration F adj _

/-- Every map generated from the free boundaries by the stated saturation operations is free. -/
theorem freeBoundarySaturation_le (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators F)).pushouts).retracts ≤
        DaggerSSet.freeCofibrations := by
  rw [MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff,
    MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
  exact freeBoundaryGenerators_le F adj

/-- This inclusion applies in particular to the previously constructed canonical free functor. -/
theorem canonical_freeBoundarySaturation_le :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators freeDagger.{u})).pushouts).retracts ≤
        DaggerSSet.freeCofibrations :=
  freeBoundarySaturation_le freeDagger freeDaggerAdjunction

/-- An actual relative cell complex built from these boundaries is a free cofibration. -/
theorem freeCofibration_of_relativeCellComplex (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) {J : Type u} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{u}
      (fun (_ : J) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) f) :
    DaggerSSet.FreeCofibration f := by
  apply DaggerSSet.FreeCofibration.of_transfiniteCompositionOfShape (J := J)
  apply (c.transfiniteCompositionOfShape (fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι)).ofLE
  rw [MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
  exact freeBoundaryGenerators_le F adj

/-- Lifting against free dagger boundaries is precisely underlying boundary lifting. -/
theorem freeBoundary_rlp_iff (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) {X Y : DaggerSSet.{u}} (p : X ⟶ Y) :
    (freeBoundaryGenerators F).rlp p ↔
      ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom := by
  constructor
  · intro hp n
    exact (adj.hasLiftingProperty_iff _ p).1 (hp _ (.mk n))
  · intro hp A B f hf
    cases hf with
    | mk n => exact (adj.hasLiftingProperty_iff _ p).2 (hp n)

end DaggerModels
