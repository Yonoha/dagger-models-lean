import OriginalSimplicialDegreeCategory
import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-!
# Degreewise groupoid completion of the original simplicial category

Apply Mathlib's free groupoid on a category to each original ordinary degree category.
Its strict functoriality supplies every simplicial operator on the completed Hom objects.
Native groupoid identities and composition give a simplicial category on exactly the same
original object type. The original localization is the identity on objects and evaluates
degreewise to the native localization functor, with no weak-equivalence assumption.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory

universe u

namespace DaggerOriginalSimplicialGroupoidCompletion

noncomputable section

/-- The original object, included in precisely its degreewise native free groupoid. -/
def completedObject (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x : C.Obj) :
    FreeGroupoid (degreeObjects C n) := (FreeGroupoid.of (degreeObjects C n)).obj x

/-- Every completed Hom degree is the literal native groupoid-completed original Hom. -/
def completedHom (C : SimplicialCat.{u, u}) (x y : C.Obj) : SSet.{u} where
  obj n := completedObject C n x ⟶ completedObject C n y
  map i f := (FreeGroupoid.map (degreeMap C i)).map f
  map_id n := by
    funext f
    change (FreeGroupoid.map (degreeMap C (𝟙 n))).map f = f
    have he := (congrArg FreeGroupoid.map (degreeMap_id C n)).trans
      (FreeGroupoid.map_id (degreeObjects C n))
    have h := CategoryTheory.Functor.congr_hom he f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, CategoryTheory.Functor.id_map]
      using h
  map_comp i j := by
    funext f
    change (FreeGroupoid.map (degreeMap C (i ≫ j))).map f =
      (FreeGroupoid.map (degreeMap C j)).map ((FreeGroupoid.map (degreeMap C i)).map f)
    have he := (congrArg FreeGroupoid.map (degreeMap_comp C i j)).trans
      (FreeGroupoid.map_comp (degreeMap C i) (degreeMap C j))
    have h := CategoryTheory.Functor.congr_hom he f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_map] using h

/-- The original completed identity, in every degree, is the native groupoid identity. -/
def completedId (C : SimplicialCat.{u, u}) (x : C.Obj) : 𝟙_ SSet.{u} ⟶ completedHom C x x where
  app n _ := 𝟙 (completedObject C n x)
  naturality n m i := by
    funext p
    exact ((FreeGroupoid.map (degreeMap C i)).map_id (completedObject C n x)).symm

/-- Completed composition is exactly native groupoid composition in the same degree. -/
def completedComp (C : SimplicialCat.{u, u}) (x y z : C.Obj) :
    completedHom C x y ⊗ completedHom C y z ⟶ completedHom C x z where
  app _ p := p.1 ≫ p.2
  naturality n m i := by
    funext p
    exact ((FreeGroupoid.map (degreeMap C i)).map_comp p.1 p.2).symm

/-- Native pointwise groupoid laws give the full enriched category on the original objects. -/
def completedEnriched (C : SimplicialCat.{u, u}) : EnrichedCategory SSet.{u} C.Obj where
  Hom := completedHom C
  id := completedId C
  comp := completedComp C
  id_comp x y := by
    ext n f
    exact Category.id_comp f
  comp_id x y := by
    ext n f
    exact Category.comp_id f
  assoc w x y z := by
    ext n ⟨f, g, h⟩
    exact Category.assoc f g h

/-- Degreewise groupoid completion retains the exact original object type. -/
def completion (C : SimplicialCat.{u, u}) : SimplicialCat.{u, u} :=
  ⟨C.Obj, completedEnriched C⟩

/-- The original degreewise localization Hom map, including every simplicial operator. -/
def localizationHom (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    C.enriched.Hom x y ⟶ completedHom C x y where
  app n f := (FreeGroupoid.of (degreeObjects C n)).map f
  naturality n m i := by
    funext f
    rfl

/-- The actual localization is the identity on objects and uses the native localization Hom map.
-/
def localization (C : SimplicialCat.{u, u}) : C ⟶ completion C where
  obj x := x
  map := localizationHom C
  map_id x := by
    ext n p
    exact (FreeGroupoid.of (degreeObjects C n)).map_id x
  map_comp x y z := by
    ext n ⟨f, g⟩
    exact (FreeGroupoid.of (degreeObjects C n)).map_comp f g

/-- The original completion localization is literally the identity on the original objects. -/
theorem localization_obj (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (localization C).obj x = x := rfl

/-- All completed degree Hom arrows are invertible in the original native degree groupoid. -/
theorem completedHom_isIso (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) (x y : C.Obj)
    (f : (completedHom C x y).obj n) : IsIso f := inferInstance

end

end DaggerOriginalSimplicialGroupoidCompletion
