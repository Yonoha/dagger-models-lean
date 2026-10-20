import ActualOriginalFixedRCoreZigzag
import ActualDaggerCoreEndpointRestriction

/-! Specialize the original R/core zigzag to BOTH canonical original endpoints.
R is applied to EXACTLY the native twoObjectCopy, including coincident endpoints.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerUnitaryInvariance DaggerActualDaggerOrdinaryCore
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerActualOriginalFixedRCoreZigzag
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualOriginalBipointedRCoreZigzag
noncomputable section

def coreLabels (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj (coreDagger X)).Obj :=
  endpoint (DaggerRigidification.obj (coreDagger X))
    (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x)
    (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X y)

def labels (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    DaggerUnitaryInterval.Vertex.{u} → (DaggerRigidification.obj X).Obj :=
  endpoint (DaggerRigidification.obj X)
    (RigidificationVertices.vertexEquiv X.toSSet x)
    (RigidificationVertices.vertexEquiv X.toSSet y)

theorem comparison_endpoint (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x : X.toSSet.obj (op ⦋0⦌)) :
    (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj
        (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x) =
      RigidificationVertices.vertexEquiv X.toSSet x := by
  change (rigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X).hom).obj
    (RigidificationVertices.vertexEquiv _ ((coreVerticesEquiv X).symm x)) = _
  rw [RigidificationVertices.vertexEquiv_naturality]
  rfl

theorem labels_compatible (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj ∘ coreLabels X x y =
      labels X x y := by
  funext i
  change (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj
    (if i.down then DaggerActualRigidifiedDaggerCoreCompletion.endpoint X y
      else DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x) = _
  cases hi : i.down <;> simp only [hi, Bool.false_eq_true, ↓reduceIte, labels, endpoint]
  · exact comparison_endpoint X x
  · exact comparison_endpoint X y

theorem ambient_native_twoObjectCopy (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    toLegacyObject (ambient X (labels X x y)) =
      twoObjectCopy (DaggerRigidification.obj X)
        (RigidificationVertices.vertexEquiv X.toSSet x)
        (RigidificationVertices.vertexEquiv X.toSSet y) := rfl

theorem core_source_original (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    DaggerNativeDaggerObjectRestriction.restriction (DaggerRigidification.obj (coreDagger X))
        (coreLabels X x y) = DaggerActualDaggerCoreEndpointRestriction.source X x y := rfl

theorem completion_original (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    DaggerActualDaggerKanObjectRestriction.comparison (coreDagger X) (coreLabels X x y) =
      DaggerActualDaggerCoreEndpointRestriction.comparison X x y := rfl

theorem all_three_arrows_weak (R : FunctorialFibrantReplacement.{u})
    (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (post R X (labels X x y)) ∧
    WeakEquivalence (DaggerActualFixedDaggerCoreComparison.comparison X
      (coreLabels X x y) (labels X x y) (labels_compatible X x y)) ∧
    WeakEquivalence (DaggerActualDaggerCoreEndpointRestriction.comparison X x y) :=
  DaggerActualOriginalFixedRCoreZigzag.all_three_arrows_weak R X
    (coreLabels X x y) (labels X x y) (labels_compatible X x y)

theorem original_R_unit_exact (R : FunctorialFibrantReplacement.{u}) (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    toLegacyHom (DaggerNativeOriginalFixedDaggerReplacement.unit R (ambient X (labels X x y))) =
      R.unit.app (twoObjectCopy (DaggerRigidification.obj X)
        (RigidificationVertices.vertexEquiv X.toSSet x)
        (RigidificationVertices.vertexEquiv X.toSSet y)) :=
  DaggerActualOriginalFixedRCoreZigzag.original_R_unit_exact R X (labels X x y)

end
end DaggerActualOriginalBipointedRCoreZigzag
