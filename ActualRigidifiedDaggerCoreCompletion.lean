import ActualDaggerOrdinaryCoreMaps
import NativeFixedDaggerCompletionWeakBridge
import ActualKanRigidificationCompletionWeak
import ActualDaggerRigidificationQuillen

/-! Actual dagger rigidification/core/completion retains the original objects and endpoint Homs. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerNativeFixedDaggerCompletionWeakBridge DaggerActualDaggerOrdinaryCore
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualRigidifiedDaggerCoreCompletion
noncomputable section

theorem rigidification_unit_weak (K : DaggerSSet.{u}) [K.toSSet.KanComplex] :
    WeakEquivalence
      (fixedDaggerLocalization (fixedOfDagger (DaggerRigidification.obj K))) := by
  apply fixed_unit_weak
  intro x y
  exact DaggerActualKanRigidificationCompletionWeak.localizationHom_weak K.toSSet x y

def fixedCore (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    FixedDaggerCategory (DaggerRigidification.obj (coreDagger X)).Obj :=
  fixedOfDagger (DaggerRigidification.obj (coreDagger X))

def completion (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    FixedDaggerCategory (DaggerRigidification.obj (coreDagger X)).Obj :=
  fixedDaggerCompleted (fixedCore X)

def unit (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] : fixedCore X ⟶ completion X :=
  fixedDaggerLocalization (fixedCore X)

theorem unit_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    WeakEquivalence (unit X) := by
  letI := coreDagger_kan X
  exact rigidification_unit_weak (coreDagger X)

theorem unit_hom_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : (DaggerRigidification.obj (coreDagger X)).Obj) :
    WeakEquivalence ((unit X).underlying.map x y) :=
  (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original _).mp (unit_weak X)
    x y

def endpoint (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] (x : X.toSSet _⦋0⦌) :
    (DaggerRigidification.obj (coreDagger X)).Obj :=
  RigidificationVertices.vertexEquiv (coreDagger X).toSSet ((coreVerticesEquiv X).symm x)

theorem endpoint_hom_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : X.toSSet _⦋0⦌) :
    WeakEquivalence ((unit X).underlying.map (endpoint X x) (endpoint X y)) :=
  unit_hom_weak X (endpoint X x) (endpoint X y)

end
end DaggerActualRigidifiedDaggerCoreCompletion
