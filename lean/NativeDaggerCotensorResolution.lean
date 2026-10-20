import NativeDaggerDegreeCotensor
import NativeCoherentCotensorResolutionNaturality

/-! The original coherent cotensor resolution carries dagger in its OUTER nerve index. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerModels OrdinaryRigidification DaggerNativeDaggerDegreeCotensor
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectCotensorPoints DaggerNativeCoherentCotensorConstants
universe u
namespace DaggerNativeDaggerCotensorResolution
noncomputable section

/-- Parameter restriction uses the old fixed-object dagger restriction. -/
def restriction {K L : SSet.{u}} (i : K ⟶ L) (C : DaggerSimplicialCat.{u, u}) :
    originalDaggerCotensor L C ⟶ originalDaggerCotensor K C :=
  originalDaggerHom (daggerCotensorPre i ⟨⟨C.enriched⟩, C.daggerStructure⟩)

/-- Constants retain the old original enriched functor and its dagger. -/
def constants (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    C ⟶ originalDaggerCotensor K C :=
  originalDaggerHom (daggerConstant K ⟨⟨C.enriched⟩, C.daggerStructure⟩)

/-- All original dagger functors, including object-changing ones, act on cotensors. -/
def map (K : SSet.{u}) {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    originalDaggerCotensor K C ⟶ originalDaggerCotensor K D where
  toEnrichedFunctor := DaggerNativeOriginalCotensorFunctor.map K F.toEnrichedFunctor
  map_dagger x y := by
    change (ihom K).map _ ≫ (ihom K).map _ = (ihom K).map _ ≫ (ihom K).map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (ihom K).map (F.map_dagger x y)

/-- Only the cotensor parameter varies here; dagger does not reverse this index. -/
def parameterDiagram (C : DaggerSimplicialCat.{u, u}) :
    SimplexCategoryᵒᵖ ⥤ DaggerSimplicialCat.{u, u} where
  obj n := originalDaggerCotensor (SSet.stdSimplex.obj n.unop) C
  map a := restriction (SSet.stdSimplex.map a.unop) C
  map_id n := by
    apply DaggerSimplicialCat.Hom.ext
    exact (DaggerOriginalCoherentCotensorResolution.parameterDiagram C.toSimplicialCat).map_id n
  map_comp a b := by
    apply DaggerSimplicialCat.Hom.ext
    exact (DaggerOriginalCoherentCotensorResolution.parameterDiagram C.toSimplicialCat).map_comp a b

/-- Applying the original dagger coherent nerve supplies the outer real action. -/
def resolution (C : DaggerSimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ DaggerSSet.{u} :=
  parameterDiagram C ⋙ DaggerNerve.daggerCoherentNerve

/-- The same constants lift to a natural transformation of dagger simplicial sets. -/
def constantComparison (C : DaggerSimplicialCat.{u, u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (DaggerNerve.daggerCoherentNerve.obj C) ⟶
      resolution C where
  app n := DaggerNerve.daggerCoherentNerve.map (constants (SSet.stdSimplex.obj n.unop) C)
  naturality n m a := by
    apply DaggerSSet.Hom.ext
    exact (DaggerOriginalCoherentCotensorResolution.constantComparison
      C.toSimplicialCat).naturality a

/-- The whole underlying component is the old comparison, not a replacement map. -/
theorem constantComparison_hom (C : DaggerSimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) :
    ((constantComparison C).app n).hom =
      (DaggerOriginalCoherentCotensorResolution.constantComparison C.toSimplicialCat).app n :=
  rfl

end
end DaggerNativeDaggerCotensorResolution
