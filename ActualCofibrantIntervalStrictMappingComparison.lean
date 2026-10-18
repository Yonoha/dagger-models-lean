import ActualCofibrantDaggerIntervalMappingComparison
import OriginalFixedObjectNativeMappingComparison
import OriginalStrictDaggerMappingSourceInvariance
import OriginalStrictDaggerMappingCofibrantKan

/-! The actual strict free EC2 mapping space compares to the actual ambient interval mapping.
Only STRICT cofibrancy of freeEC2 is used; no ambient cofibrancy of freeEC2 is asserted.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectFreePointInterval DaggerOriginalFreeEC2DaggerGroupoidComparison
open DaggerActualCofibrantDaggerIntervalMappingComparison DaggerNativeOriginalRReplacedMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualCofibrantIntervalStrictMappingComparison
noncomputable section

def comparisonMap {H : FixedDaggerCategory TwoObjects.{u}} (f : H ⟶ unitaryInterval.obj)
    [IsCofibrant H] [WeakEquivalence f] (D : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (freeEC2 ⟶[SSet.{u}] D) ⟶ (H ⟶[SSet.{u}] D.obj) :=
  eHomWhiskerRight SSet (completionToFree f) D ≫
    (DaggerOriginalFixedObjectNativeMappingComparison.daggerCompletionMappingIso H D).hom

theorem comparisonMap_weak {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H] [WeakEquivalence f]
    (D : FixedStrictDaggerGroupoids TwoObjects.{u}) : WeakEquivalence (comparisonMap f D) := by
  have : IsCofibrant ((fixedDaggerCompletion TwoObjects).obj H) := completion_cofibrant H
  have : IsCofibrant freeEC2.{u} := augmentation_source_isCofibrant
  have : WeakEquivalence (completionToFree f) := completionToFree_weak f
  have : WeakEquivalence (eHomWhiskerRight SSet (completionToFree f) D) :=
    DaggerOriginalStrictDaggerMappingSourceInvariance.mappingSource_weakEquivalence _ D
  change WeakEquivalence (eHomWhiskerRight SSet (completionToFree f) D ≫
    (DaggerOriginalFixedObjectNativeMappingComparison.daggerCompletionMappingIso H D).hom)
  infer_instance

theorem freeMapping_kan (D : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (freeEC2 ⟶[SSet.{u}] D).KanComplex := by
  have : IsCofibrant freeEC2.{u} := augmentation_source_isCofibrant
  exact DaggerOriginalStrictDaggerMappingCofibrantKan.mapping_kan _ D

theorem ambientMapping_kan {O : Type u} (H : FixedDaggerCategory O) [IsCofibrant H]
    (D : FixedStrictDaggerGroupoids O) : (H ⟶[SSet.{u}] D.obj).KanComplex := by
  have : IsFibrant D.obj :=
    DaggerOriginalFixedObjectDaggerDerivedCompletion.inclusion_isFibrant D
  exact DaggerNativeAmbientDaggerMappingKan.mapping_kan H D.obj

def comparisonIso {H : FixedDaggerCategory TwoObjects.{u}} (f : H ⟶ unitaryInterval.obj)
    [IsCofibrant H] [WeakEquivalence f] (D : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    kanWeak.Q.obj (freeEC2 ⟶[SSet.{u}] D) ≅ kanWeak.Q.obj (H ⟶[SSet.{u}] D.obj) :=
  have := comparisonMap_weak f D
  have : IsIso (kanWeak.Q.map (comparisonMap f D)) :=
    Localization.inverts kanWeak.Q kanWeak _ (mem_weakEquivalences _)
  asIso (kanWeak.Q.map (comparisonMap f D))

theorem comparison_hom {H : FixedDaggerCategory TwoObjects.{u}} (f : H ⟶ unitaryInterval.obj)
    [IsCofibrant H] [WeakEquivalence f] (D : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (comparisonIso f D).hom = kanWeak.Q.map (comparisonMap f D) := rfl

end
end DaggerActualCofibrantIntervalStrictMappingComparison
