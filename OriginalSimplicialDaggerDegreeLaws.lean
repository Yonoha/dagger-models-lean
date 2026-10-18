import DaggerModels.DaggerSimplicialCategory
import OriginalSimplicialGroupoidCompletionAdjunction

/-!
# The original dagger in every original degree category

Evaluate the existing enriched dagger laws in the unchanged degree categories. The
covariant seed sending an original arrow to the inverse of its localized dagger is
then a genuine functor to the native free groupoid, without any invertibility premise
on the original arrow.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory

universe u

namespace DaggerOriginalSimplicialDaggerDegreeLaws

noncomputable section

/-- Evaluate the original dagger on the actual ordinary degree Hom. -/
def degreeDagger (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) : y ⟶ x :=
  (@DaggerSimplicialStructure.dagger C.Obj C.toSimplicialCat.enriched
    C.daggerStructure x y).app n f

/-- The original enriched dagger reverses the original degree identities. -/
theorem degreeDagger_id (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (x : degreeObjects C.toSimplicialCat n) : degreeDagger C n (𝟙 x) = 𝟙 x := by
  exact congrFun (congrArg (fun F ↦ F.app n)
    (@DaggerSimplicialStructure.dagger_id C.Obj C.toSimplicialCat.enriched
      C.daggerStructure x)) PUnit.unit

/-- The original enriched dagger reverses every original degree composition. -/
theorem degreeDagger_comp (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    {x y z : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) (g : y ⟶ z) :
    degreeDagger C n (f ≫ g) = degreeDagger C n g ≫ degreeDagger C n f := by
  exact congrFun (congrArg (fun F ↦ F.app n)
    (@DaggerSimplicialStructure.dagger_comp C.Obj C.toSimplicialCat.enriched
      C.daggerStructure x y z)) (f, g)

/-- The original enriched dagger is involutive in every original degree. -/
theorem degreeDagger_involutive (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) :
    degreeDagger C n (degreeDagger C n f) = f := by
  exact congrFun (congrArg (fun F ↦ F.app n)
    (@DaggerSimplicialStructure.dagger_involutive C.Obj C.toSimplicialCat.enriched
      C.daggerStructure x y)) f

/-- Every original simplicial operator commutes with the original degree dagger. -/
theorem degreeDagger_naturality (C : DaggerSimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    {x y : degreeObjects C.toSimplicialCat n} (f : x ⟶ y) :
    (degreeMap C.toSimplicialCat i).map (degreeDagger C n f) =
      degreeDagger C m ((degreeMap C.toSimplicialCat i).map f) :=
  (congrFun ((@DaggerSimplicialStructure.dagger C.Obj C.toSimplicialCat.enriched
    C.daggerStructure x y).naturality i) f).symm

/-- Localized inverse dagger on the original degree arrows is covariant. -/
def degreeSigmaSeed (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeObjects C.toSimplicialCat n ⥤ FreeGroupoid (degreeObjects C.toSimplicialCat n) where
  obj := (FreeGroupoid.of _).obj
  map f := inv ((FreeGroupoid.of _).map (degreeDagger C n f))
  map_id x := by
    rw [degreeDagger_id, (FreeGroupoid.of _).map_id]
    exact IsIso.inv_id
  map_comp f g := by
    rw [degreeDagger_comp, (FreeGroupoid.of _).map_comp]
    exact IsIso.inv_comp

end

end DaggerOriginalSimplicialDaggerDegreeLaws
