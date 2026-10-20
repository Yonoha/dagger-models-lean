import OriginalCofibrantLocalizationCriterion
import OriginalFixedObjectCompletedIntervalComparison
import NativeFixedDaggerCompletionWeakBridge
import ActualOriginalGroupoidalCoreRMappingComparison

/-! The ORIGINAL cofibrant weak interval discharges both remaining source hypotheses.
Reuse the exact existing DK80 criterion, the original completion and original free EC2.
The full native R mapping comparison uses the original augmentation, no assumed pi0 groupoid.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectFreePointInterval DaggerOriginalFreeEC2DaggerGroupoidComparison
open DaggerOriginalFixedObjectCompletedIntervalComparison
open DaggerActualOriginalGroupoidalCoreRMappingComparison DaggerNativeOriginalRReplacedMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualCofibrantDaggerIntervalMappingComparison
noncomputable section

theorem interval_unit_weak {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [IsCofibrant H] [WeakEquivalence f] :
    WeakEquivalence (fixedDaggerLocalization H) :=
  DaggerNativeFixedDaggerCompletionWeakBridge.unit_weak_of_homs H
    (DaggerOriginalCofibrantLocalizationCriterion.interval_localizationHom_weak f)

def completionToFree {H : FixedDaggerCategory TwoObjects.{u}} (f : H ⟶ unitaryInterval.obj)
    [IsCofibrant H] [WeakEquivalence f] :
    (fixedDaggerCompletion TwoObjects).obj H ⟶ freeEC2 :=
  have := interval_unit_weak f
  completedToFree f

theorem completionToFree_triangle {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H] [WeakEquivalence f] :
    completionToFree f ≫ augmentation = completedAugmentation f := by
  have := interval_unit_weak f
  exact completedToFree_triangle f

theorem completionToFree_weak {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H] [WeakEquivalence f] :
    WeakEquivalence (completionToFree f) := by
  have := interval_unit_weak f
  exact completedToFree_weakEquivalence f

theorem completion_cofibrant {O : Type u} (H : FixedDaggerCategory O) [IsCofibrant H] :
    IsCofibrant ((fixedDaggerCompletion O).obj H) :=
  DaggerOriginalFixedObjectDaggerDerivedCompletion.completion_isCofibrant H

def originalRComparison (R : FunctorialFibrantReplacement.{u})
    {H : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}} [IsCofibrant H]
    (f : H ⟶ terminalFixedDagger DaggerUnitaryInterval.Vertex) [WeakEquivalence f]
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    kanWeak.Q.obj (H ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) ≅
      kanWeak.Q.obj (H ⟶[SSet.{u}] fullTarget R X x y) :=
  comparisonIso R H (interval_hasActualComponentGroupoid f) X x y

theorem originalRComparison_hom (R : FunctorialFibrantReplacement.{u})
    {H : FixedDaggerCategory DaggerUnitaryInterval.Vertex.{u}} [IsCofibrant H]
    (f : H ⟶ terminalFixedDagger DaggerUnitaryInterval.Vertex) [WeakEquivalence f]
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    (originalRComparison R f X x y).hom =
      (DaggerActualOriginalCoreEnrichedMappingZigzag.kanLocalizationIso R H X x y).hom ≫
        kanWeak.Q.map (partMap R H X x y) := rfl

end
end DaggerActualCofibrantDaggerIntervalMappingComparison
