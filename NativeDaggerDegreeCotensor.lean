import NativeDegreeCotensorYoneda
import OriginalSimplicialDaggerDegreeLaws

/-! The SAME degree-to-cotensor functor preserves the original dagger. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerNativeDegreeCotensorYoneda
universe u
namespace DaggerNativeDaggerDegreeCotensor
noncomputable section

/-- The existing dagger, evaluated in the original degree category. -/
def degreeDaggerCategory (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    DaggerCategory (degreeObjects C.toSimplicialCat n) where
  dagger := degreeDagger C n
  dagger_involutive := degreeDagger_involutive C n
  dagger_id := degreeDagger_id C n
  dagger_comp := degreeDagger_comp C n

/-- Reuse the original constant enrichment, with this original degree dagger. -/
def degreeEnrichment (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ) :
    DaggerSimplicialCat.{u, u} := by
  letI := degreeDaggerCategory C n
  exact DaggerUnitaryDiscrete.ordinaryEnrichment (degreeObjects C.toSimplicialCat n)

/-- The existing fixed-object cotensor, bundled with its existing transported dagger. -/
def originalDaggerCotensor (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    DaggerSimplicialCat.{u, u} :=
  originalDagger (daggerCotensor K ⟨⟨C.enriched⟩, C.daggerStructure⟩)

/-- Yoneda commutes with every actual simplicial Hom map, including the dagger. -/
theorem homMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory) :
    homMap X n ≫ (ihom (SSet.stdSimplex.obj n)).map f =
      DaggerUnitaryDiscrete.constMap (f.app (op n)) ≫ homMap Y n := by
  apply NatTrans.ext
  funext q a
  apply Functor.HomObj.ext
  funext r i k
  exact congrFun (f.naturality (SSet.stdSimplex.objEquiv k).op) a

/-- No object or Hom map of the old Yoneda comparison is changed. -/
def degreeToDaggerCotensor (C : DaggerSimplicialCat.{u, u}) (n : SimplexCategory) :
    degreeEnrichment C (op n) ⟶ originalDaggerCotensor (SSet.stdSimplex.obj n) C where
  toEnrichedFunctor := degreeToCotensor C.toSimplicialCat n
  map_dagger x y := homMap_naturality (C.daggerStructure.dagger x y) n

/-- The entire underlying enriched functor is literally the previously verified one. -/
theorem degreeToDaggerCotensor_underlying (C : DaggerSimplicialCat.{u, u})
    (n : SimplexCategory) :
    (degreeToDaggerCotensor C n).toEnrichedFunctor =
      degreeToCotensor C.toSimplicialCat n := rfl

end
end DaggerNativeDaggerDegreeCotensor
