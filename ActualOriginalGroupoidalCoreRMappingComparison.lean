import NativeFixedDaggerPartMappingIso
import ActualOriginalCoreEnrichedMappingZigzag

/-! The EXACT original completed core versus the FULL original native R mapping target.
The original five-arrow Kan zigzag is followed by the SAME original part-inclusion mapping ISO.
All original quasi inputs, original endpoints (also repeats), and original native R are retained.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerActualOriginalFixedRCoreZigzag DaggerActualOriginalBipointedRCoreZigzag
open DaggerNativeOriginalFixedDaggerReplacement DaggerNativeOriginalRReplacedMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalGroupoidalCoreRMappingComparison
noncomputable section

def fullTarget (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :=
  (replacement R).obj (ambient X (labels X x y))

def partMap (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (A ⟶[SSet.{u}] replacedPart R X (labels X x y)) ⟶ (A ⟶[SSet.{u}] fullTarget R X x y) :=
  eHomWhiskerLeft SSet A (DaggerNativeFixedDaggerIsomorphismPart.inclusion (fullTarget R X x y))

def partIso (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (A ⟶[SSet.{u}] replacedPart R X (labels X x y)) ≅ (A ⟶[SSet.{u}] fullTarget R X x y) :=
  DaggerNativeFixedDaggerPartMappingIso.mappingIso A (fullTarget R X x y) hA

theorem partIso_hom (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (partIso R A hA X x y).hom = partMap R A X x y := rfl

theorem full_mapping_kan (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (A ⟶[SSet.{u}] fullTarget R X x y).KanComplex := by
  have : IsFibrant (fullTarget R X x y) := replacement_fibrant R (ambient X (labels X x y))
  exact DaggerNativeAmbientDaggerMappingKan.mapping_kan A _

def comparisonIso (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    kanWeak.Q.obj (A ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) ≅
      kanWeak.Q.obj (A ⟶[SSet.{u}] fullTarget R X x y) :=
  DaggerActualOriginalCoreEnrichedMappingZigzag.kanLocalizationIso R A X x y ≪≫
    kanWeak.Q.mapIso (partIso R A hA X x y)

theorem comparison_hom (R : FunctorialFibrantReplacement.{u})
    (A : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}) [IsCofibrant A]
    (hA : HasActualComponentGroupoid (originalDagger A).toSimplicialCat)
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    (comparisonIso R A hA X x y).hom =
      (DaggerActualOriginalCoreEnrichedMappingZigzag.kanLocalizationIso R A X x y).hom ≫
        kanWeak.Q.map (partMap R A X x y) := rfl

end
end DaggerActualOriginalGroupoidalCoreRMappingComparison
