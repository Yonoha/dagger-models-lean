import NativeDaggerObjectRestriction
import ActualRigidifiedDaggerCoreCompletion

/-! Restrict the actual completion unit after completing the entire rigidified Kan input. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalFixedObjectDaggerCategories DaggerNativeDaggerObjectRestriction
open DaggerOriginalSimplicialGroupoidCompletionDagger
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualDaggerKanObjectRestriction
noncomputable section

def comparison {O : Type u} (K : DaggerSSet.{u})
    (θ : O → (DaggerRigidification.obj K).Obj) :
    restriction (DaggerRigidification.obj K) θ ⟶
      restriction (daggerCompletion (DaggerRigidification.obj K)) θ :=
  DaggerNativeDaggerObjectRestriction.map
    (daggerLocalization (DaggerRigidification.obj K)) θ

theorem comparison_hom {O : Type u} (K : DaggerSSet.{u})
    (θ : O → (DaggerRigidification.obj K).Obj) (i j : O) :
    (comparison K θ).underlying.map i j =
      (daggerLocalization (DaggerRigidification.obj K)).map (θ i) (θ j) :=
  rfl

theorem comparison_weak {O : Type u} (K : DaggerSSet.{u}) [K.toSSet.KanComplex]
    (θ : O → (DaggerRigidification.obj K).Obj) :
    WeakEquivalence (comparison K θ) := by
  apply DaggerNativeDaggerObjectRestriction.map_weak
  intro a b
  exact
    (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original _).mp
      (DaggerActualRigidifiedDaggerCoreCompletion.rigidification_unit_weak K) a b

end
end DaggerActualDaggerKanObjectRestriction
