import OriginalSimplicialGroupoidCompletion

/-!
# Functoriality of original degreewise simplicial groupoid completion

Every original simplicial functor induces the native free-groupoid functor in every degree.
Strict native functoriality and the already proved degree naturality assemble the original
completion into a functor on the full original simplicial-category category. The original
localization is an actual natural transformation, with its same identity object map.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialGroupoidCompletion

universe u

namespace DaggerOriginalSimplicialGroupoidCompletionFunctor

noncomputable section

/-- The original identity simplicial functor induces the literal identity degree functor. -/
theorem degreeFunctor_id (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    degreeFunctor (𝟙 C) n = 𝟭 (degreeObjects C n) := by
  refine CategoryTheory.Functor.hext (F := degreeFunctor (𝟙 C) n)
    (G := 𝟭 (degreeObjects C n)) (fun _ ↦ rfl) ?_
  intro x y f
  rfl

/-- Original simplicial functor composition is the same composition in each degree. -/
theorem degreeFunctor_comp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E)
    (n : SimplexCategoryᵒᵖ) : degreeFunctor (F ≫ G) n = degreeFunctor F n ⋙ degreeFunctor G n := by
  refine CategoryTheory.Functor.hext (F := degreeFunctor (F ≫ G) n)
    (G := degreeFunctor F n ⋙ degreeFunctor G n) (fun _ ↦ rfl) ?_
  intro x y f
  rfl

/-- Strict native free-groupoid degree functors commute with every original simplicial operator.
-/
theorem completedDegreeFunctor_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    FreeGroupoid.map (degreeMap C i) ⋙ FreeGroupoid.map (degreeFunctor F m) =
      FreeGroupoid.map (degreeFunctor F n) ⋙ FreeGroupoid.map (degreeMap D i) := by
  rw [← FreeGroupoid.map_comp, ← FreeGroupoid.map_comp, degreeFunctor_naturality]

/-- The same original simplicial functor induces its degreewise completed Hom map. -/
def completionHomMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) :
    completedHom C x y ⟶ completedHom D (F.obj x) (F.obj y) where
  app n f := (FreeGroupoid.map (degreeFunctor F n)).map f
  naturality n m i := by
    funext f
    have h := CategoryTheory.Functor.congr_hom (completedDegreeFunctor_naturality F i) f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
      CategoryTheory.Functor.comp_map] using h

/-- The completion of an original simplicial functor retains its exact original object map. -/
def completionMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : completion C ⟶ completion D where
  obj := F.obj
  map := completionHomMap F
  map_id x := by
    ext n p
    exact (FreeGroupoid.map (degreeFunctor F n)).map_id (completedObject C n x)
  map_comp x y z := by
    ext n ⟨f, g⟩
    exact (FreeGroupoid.map (degreeFunctor F n)).map_comp f g

/-- Completion of the original identity is exactly the identity simplicial functor. -/
theorem completionMap_id (C : SimplicialCat.{u, u}) :
    completionMap (𝟙 C) = 𝟙 (completion C) := by
  refine EnrichedFunctor.ext SSet.{u} (F := completionMap (𝟙 C)) (G := 𝟙 (completion C))
    (fun _ ↦ rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  have he := (congrArg FreeGroupoid.map (degreeFunctor_id C n)).trans
    (FreeGroupoid.map_id (degreeObjects C n))
  have h := CategoryTheory.Functor.congr_hom he f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.id_map] using h

/-- Completion of the original composite is exactly the composite of the completed functors. -/
theorem completionMap_comp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    completionMap (F ≫ G) = completionMap F ≫ completionMap G := by
  refine EnrichedFunctor.ext SSet.{u} (F := completionMap (F ≫ G))
    (G := completionMap F ≫ completionMap G)
    (fun _ ↦ rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  have he := (congrArg FreeGroupoid.map (degreeFunctor_comp F G n)).trans
    (FreeGroupoid.map_comp (degreeFunctor F n) (degreeFunctor G n))
  have h := CategoryTheory.Functor.congr_hom he f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.comp_map] using h

/-- The actual degreewise completion is a functor on the full original simplicial categories. -/
def completionFunctor : SimplicialCat.{u, u} ⥤ SimplicialCat.{u, u} where
  obj := completion
  map := completionMap
  map_id := completionMap_id
  map_comp := completionMap_comp

/-- Original localization commutes strictly with every original simplicial functor. -/
theorem localization_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    localization C ≫ completionMap F = F ≫ localization D := by
  refine EnrichedFunctor.ext SSet.{u} (F := localization C ≫ completionMap F)
    (G := F ≫ localization D) (fun _ ↦ rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  ext n f
  rfl

/-- The actual localization maps form a natural transformation without changing their objects.
-/
def localizationNatTrans : 𝟭 (SimplicialCat.{u, u}) ⟶ completionFunctor where
  app := localization
  naturality _ _ F := (localization_naturality F).symm

end

end DaggerOriginalSimplicialGroupoidCompletionFunctor
