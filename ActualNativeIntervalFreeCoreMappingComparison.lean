import ActualNativeDaggerIntervalPresentation
import ActualCofibrantIntervalStrictMappingComparison
import NativeStrictDaggerObjectRestriction

/-! The ORIGINAL native Interval record, free EC2 and full original R mapping target.
No extra source-cofibrancy, pi0-groupoid, completion-unit weakness or target-strictness premise
is imposed. Completion is on the FULL original core before the SAME two labels are selected.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerOriginalFreeEC2DaggerGroupoidComparison DaggerNativeOriginalRReplacedMapping
open DaggerActualNativeDaggerIntervalPresentation DaggerNativeStrictDaggerObjectRestriction
open DaggerActualOriginalGroupoidalCoreRMappingComparison
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerModel
  DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualNativeIntervalFreeCoreMappingComparison
noncomputable section

def originalRComparison (R : FunctorialFibrantReplacement.{u})
    (H : DaggerUnitaryInterval.Interval.{u}) (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    kanWeak.Q.obj ((obj H) ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) ≅
      kanWeak.Q.obj ((obj H) ⟶[SSet.{u}] fullTarget R X x y) :=
  have : IsCofibrant (obj H) := obj_cofibrant H
  have : WeakEquivalence (augmentation H) := augmentation_weak H
  DaggerActualCofibrantDaggerIntervalMappingComparison.originalRComparison R
    (augmentation H) X x y

def freeToCoreMap (H : DaggerUnitaryInterval.Interval.{u})
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    (freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y) ⟶
      ((obj H) ⟶[SSet.{u}] DaggerActualDaggerCoreEndpointRestriction.target X x y) :=
  have : IsCofibrant (obj H) := obj_cofibrant H
  have : WeakEquivalence (augmentation H) := augmentation_weak H
  DaggerActualCofibrantIntervalStrictMappingComparison.comparisonMap
    (augmentation H) (strictCoreTarget X x y)

theorem freeToCoreMap_weak (H : DaggerUnitaryInterval.Interval.{u})
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (freeToCoreMap H X x y) := by
  have : IsCofibrant (obj H) := obj_cofibrant H
  have : WeakEquivalence (augmentation H) := augmentation_weak H
  exact DaggerActualCofibrantIntervalStrictMappingComparison.comparisonMap_weak
    (augmentation H) (strictCoreTarget X x y)

def comparisonIso (R : FunctorialFibrantReplacement.{u})
    (H : DaggerUnitaryInterval.Interval.{u}) (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    kanWeak.Q.obj (freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y) ≅
      kanWeak.Q.obj ((obj H) ⟶[SSet.{u}] fullTarget R X x y) := by
  have : IsCofibrant (obj H) := obj_cofibrant H
  have : WeakEquivalence (augmentation H) := augmentation_weak H
  exact DaggerActualCofibrantIntervalStrictMappingComparison.comparisonIso
    (augmentation H) (strictCoreTarget X x y) ≪≫ originalRComparison R H X x y

theorem comparison_hom (R : FunctorialFibrantReplacement.{u})
    (H : DaggerUnitaryInterval.Interval.{u}) (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (comparisonIso R H X x y).hom =
      kanWeak.Q.map (freeToCoreMap H X x y) ≫ (originalRComparison R H X x y).hom := rfl

theorem free_mapping_kan (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (freeEC2 ⟶[SSet.{u}] strictCoreTarget X x y).KanComplex :=
  DaggerActualCofibrantIntervalStrictMappingComparison.freeMapping_kan (strictCoreTarget X x y)

theorem full_R_mapping_kan (R : FunctorialFibrantReplacement.{u})
    (H : DaggerUnitaryInterval.Interval.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) : ((obj H) ⟶[SSet.{u}] fullTarget R X x y).KanComplex :=
  have : IsCofibrant (obj H) := obj_cofibrant H
  full_mapping_kan R (obj H) X x y

end
end DaggerActualNativeIntervalFreeCoreMappingComparison
