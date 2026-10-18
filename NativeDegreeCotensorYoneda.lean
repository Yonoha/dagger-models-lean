import NativeOriginalCotensorFunctor
import ActualConstantEnrichmentFunctor
import OriginalSimplicialCategoryDiagonalNerve

/-! Yoneda sends every original degree category to its original simplex cotensor. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerActualConstantSimplicialCategory DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
universe u
namespace DaggerNativeDegreeCotensorYoneda
noncomputable section

/-- Every original simplex determines its actual global point in the internal Hom. -/
def homMap (X : SSet.{u}) (n : SimplexCategory) :
    (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (X.obj (op n)) ⟶
      (ihom (SSet.stdSimplex.obj n)).obj X where
  app q a := (MonoidalClosed.curry'
    ((SSet.yonedaEquiv (X := X) (n := n)).symm a)).app q PUnit.unit
  naturality q r i := by
    funext a
    exact congrFun ((MonoidalClosed.curry'
      ((SSet.yonedaEquiv (X := X) (n := n)).symm a)).naturality i) PUnit.unit

local instance (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    EnrichedCategory SSet.{u} (degreeObjects C (op n)) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- Objects are unchanged and every degree arrow is sent to its SAME Yoneda simplex. -/
def degreeToCotensor (C : SimplicialCat.{u, u}) (n : SimplexCategory) :
    constant (degreeObjects C (op n)) ⟶ originalCotensor (SSet.stdSimplex.obj n) C where
  obj x := x
  map x y := homMap (C.enriched.Hom x y) n
  map_id x := by
    ext q p
    apply Functor.HomObj.ext
    funext r i k
    change (C.enriched.Hom x x).map (SSet.stdSimplex.objEquiv k).op
      ((C.enriched.id x).app (op n) PUnit.unit) =
        (C.enriched.id x).app r PUnit.unit
    exact (congrFun ((C.enriched.id x).naturality
      (SSet.stdSimplex.objEquiv k).op) PUnit.unit).symm
  map_comp x y z := by
    ext q p
    apply Functor.HomObj.ext
    funext r i k
    change ((homMap (C.enriched.Hom x z) n).app q
      ((C.enriched.comp x y z).app (op n) (p.1, p.2))).app r i k =
        (((cotensor (SSet.stdSimplex.obj n) ⟨C.enriched⟩).enriched.comp x y z).app q
          ((homMap (C.enriched.Hom x y) n).app q p.1,
            (homMap (C.enriched.Hom y z) n).app q p.2)).app r i k
    rw [cotensor_point_comp]
    change (C.enriched.Hom x z).map (SSet.stdSimplex.objEquiv k).op
      ((C.enriched.comp x y z).app (op n) (p.1, p.2)) =
        (C.enriched.comp x y z).app r
          ((C.enriched.Hom x y).map (SSet.stdSimplex.objEquiv k).op p.1,
            (C.enriched.Hom y z).map (SSet.stdSimplex.objEquiv k).op p.2)
    exact (congrFun ((C.enriched.comp x y z).naturality
      (SSet.stdSimplex.objEquiv k).op) (p.1, p.2)).symm

end
end DaggerNativeDegreeCotensorYoneda
