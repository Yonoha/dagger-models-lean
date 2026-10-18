import OriginalArbitraryParameterPrecomposition
import NativeIhomProductSectionTransport
import OriginalFixedObjectCotensorRepresentation

/-! Original fixed-object cotensor precomposition is weak under the original pi0 groupoid input. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial HomotopicalAlgebra
open DaggerModels DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectCotensors
open DaggerOriginalFixedObjectCotensorRepresentation
open DaggerOriginalFixedObjectSimplicialEnrichment
open DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalArbitraryParameterPrecomposition DaggerNativeIhomProductSectionTransport
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalCotensorPrecompositionWeak
noncomputable section

def originalCotensor (K : SSet.{u}) (C : SimplicialCat.{u, u}) : SimplicialCat.{u, u} :=
  original C.Obj (cotensor K ⟨C.enriched⟩)

def vertexMap (K : SSet.{u}) (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : ((originalCotensor K C).enriched.Hom x y) _⦋0⦌) : K ⟶ C.enriched.Hom x y :=
  MonoidalClosed.curryHomEquiv'.symm (vertexPoint (originalCotensor K C) a)

theorem vertexMap_curry' (K : SSet.{u}) (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : ((originalCotensor K C).enriched.Hom x y) _⦋0⦌) :
    MonoidalClosed.curry' (vertexMap K C a) = vertexPoint (originalCotensor K C) a := by
  let e : (K ⟶ C.enriched.Hom x y) ≃
      (𝟙_ SSet.{u} ⟶ (ihom K).obj (C.enriched.Hom x y)) := MonoidalClosed.curryHomEquiv'
  change e (e.symm (vertexPoint (originalCotensor K C) a)) = _
  exact e.apply_symm_apply _

theorem cotensor_precompose_eq (K : SSet.{u}) (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : ((originalCotensor K C).enriched.Hom x y) _⦋0⦌) (z : C.Obj) :
    precomposeVertex (originalCotensor K C) a z =
      sectionTransport (relativeParameterPrecompose C (vertexMap K C a) z) := by
  apply NatTrans.ext
  funext n f
  apply Functor.HomObj.ext
  funext m i k
  rw [sectionTransport_app]
  change (((cotensor K ⟨C.enriched⟩).enriched.comp x y z).app n
    ((vertexPoint (originalCotensor K C) a).app n PUnit.unit, f)).app m i k =
      (C.enriched.comp x y z).app m ((vertexMap K C a).app m k, f.app m i k)
  rw [cotensor_point_comp, ← vertexMap_curry' K C a]
  rfl

theorem cotensor_precompose_weak (K : SSet.{u}) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj}
    (a : ((originalCotensor K C).enriched.Hom x y) _⦋0⦌) (z : C.Obj)
    [(C.enriched.Hom y z).KanComplex] [(C.enriched.Hom x z).KanComplex] :
    WeakEquivalence (precomposeVertex (originalCotensor K C) a z) := by
  rw [cotensor_precompose_eq]
  have : WeakEquivalence (relativeParameterPrecompose C (vertexMap K C a) z) :=
    relativeParameterPrecompose_weak C hC _ z
  exact sectionTransport_weak _ (relativeParameterPrecompose_fst C _ z)

end
end DaggerOriginalCotensorPrecompositionWeak
