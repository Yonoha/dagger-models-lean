import OriginalSimplicialGroupoidCompletionFunctor
import OriginalSimplicialPiZeroCategory

/-!
# The full original diagonal nerve used in the DK80 proof

In each degree use precisely the original ordinary degree category, apply the
native nerve functor, uncurry the resulting bisimplicial set, and restrict along
the native diagonal functor. This keeps the same original degree operators and
all enriched-functor Hom maps. No nerve weak-equivalence or quasifibration
assertion is assumed. The actual completion unit gives its actual diagonal map.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion DaggerOriginalSimplicialGroupoidCompletionFunctor
universe u
namespace DaggerOriginalSimplicialCategoryDiagonalNerve
noncomputable section

/-- The actual category in every original simplicial degree, with its original operators. -/
def degreeCategoryDiagram (C : SimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ Cat.{u, u} where
  obj n := Cat.of (degreeObjects C n)
  map i := (degreeMap C i).toCatHom
  map_id n := by
    rw [degreeMap_id]
    rfl
  map_comp i j := by
    rw [degreeMap_comp]
    rfl

/-- Every whole original enriched functor gives the original degree functors naturally. -/
def degreeCategoryMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    degreeCategoryDiagram C ⟶ degreeCategoryDiagram D where
  app n := (degreeFunctor F n).toCatHom
  naturality n m i := by
    change (degreeMap C i ⋙ degreeFunctor F m).toCatHom =
      (degreeFunctor F n ⋙ degreeMap D i).toCatHom
    exact congrArg Functor.toCatHom (degreeFunctor_naturality F i)

/-- Package all the unchanged original degree categories and degree functors. -/
def degreeCategoryFunctor : SimplicialCat.{u, u} ⥤ SimplexCategoryᵒᵖ ⥤ Cat.{u, u} where
  obj := degreeCategoryDiagram
  map := degreeCategoryMap
  map_id C := by
    apply NatTrans.ext
    funext n
    rfl
  map_comp F G := by
    apply NatTrans.ext
    funext n
    rfl

/-- The whole original bisimplicial nerve, before taking its diagonal. -/
def bisimplicialNerveFunctor :
    SimplicialCat.{u, u} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  degreeCategoryFunctor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ Cat.{u, u} SSet.{u}).obj nerveFunctor

/-- The actual diagonal classifying complex of the original simplicial category. -/
def diagonalNerveFunctor : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  bisimplicialNerveFunctor ⋙
    Functor.uncurry ⋙
      (Functor.whiskeringLeft SimplexCategoryᵒᵖ
        (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj
        (Functor.diag SimplexCategoryᵒᵖ)

/-- Every diagonal degree is literally the nerve of the same original degree category. -/
theorem diagonalNerve_obj (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    (diagonalNerveFunctor.obj C).obj n = (nerve (degreeObjects C n)).obj n := rfl

/-- The full diagonal map retains the same original degree functor on every simplex. -/
theorem diagonalNerve_map_apply {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (n : SimplexCategoryᵒᵖ) (a : (diagonalNerveFunctor.obj C).obj n) :
    (diagonalNerveFunctor.map F).app n a = (nerveMap (degreeFunctor F n)).app n a := rfl

/-- The actual degreewise completion unit induces its exact original diagonal nerve map. -/
def diagonalLocalization (C : SimplicialCat.{u, u}) :
    diagonalNerveFunctor.obj C ⟶ diagonalNerveFunctor.obj (completion C) :=
  diagonalNerveFunctor.map (localization C)

/-- Full naturality retains the original completion map and both actual localization maps. -/
theorem diagonalLocalization_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    diagonalLocalization C ≫ diagonalNerveFunctor.map (completionMap F) =
      diagonalNerveFunctor.map F ≫ diagonalLocalization D := by
  simp only [diagonalLocalization, ← Functor.map_comp]
  exact congrArg (fun f ↦ diagonalNerveFunctor.map f) (localization_naturality F)

end
end DaggerOriginalSimplicialCategoryDiagonalNerve
