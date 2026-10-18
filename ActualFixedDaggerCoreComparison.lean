import NativeFixedDaggerPartRestrictionIso
import ActualFirstCoreComparisonAllQuasicategories
import ActualDaggerKanObjectRestriction

/-! The SAME original first core comparison at ANY fixed collection of original labels.
Its target is the SAME isomorphism-component part of the selected full original category.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualDaggerOrdinaryCore DaggerOriginalFixedObjectDaggerCategories
open DaggerNativeDaggerObjectRestriction DaggerNativeDaggerLabelTransport
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerActualFixedDaggerCoreComparison
noncomputable section

def comparison {O : Type u} (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : O → (DaggerRigidification.obj (coreDagger X)).Obj)
    (b : O → (DaggerRigidification.obj X).Obj)
    (h : (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj ∘ a = b) :
    restriction (DaggerRigidification.obj (coreDagger X)) a ⟶
      DaggerNativeFixedDaggerIsomorphismPart.part (restriction (DaggerRigidification.obj X) b) :=
  mapAlong (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X) a b h ≫
    (DaggerNativeFixedDaggerPartRestrictionIso.comparisonIso (DaggerRigidification.obj X) b).hom

theorem comparison_weak {O : Type u} (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : O → (DaggerRigidification.obj (coreDagger X)).Obj)
    (b : O → (DaggerRigidification.obj X).Obj)
    (h : (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj ∘ a = b) :
    WeakEquivalence (comparison X a b h) := by
  have := mapAlong_weak
    (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X) a b h
    (DaggerActualFirstCoreComparisonAllQuasicategories.dagger_hom_weak X)
  unfold comparison
  infer_instance

theorem comparison_triangle {O : Type u} (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : O → (DaggerRigidification.obj (coreDagger X)).Obj)
    (b : O → (DaggerRigidification.obj X).Obj)
    (h : (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).obj ∘ a = b) :
    comparison X a b h ≫ DaggerNativeFixedDaggerIsomorphismPart.inclusion
        (restriction (DaggerRigidification.obj X) b) =
      mapAlong (DaggerRigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X))
        a b h := by
  subst b
  apply DaggerOriginalFixedObjectDaggerCategories.fixedDaggerHom_ext
  apply DaggerOriginalFixedObjectSimplicialCategories.fixedHom_ext
  intro i j
  apply NatTrans.ext
  funext q s
  rfl

theorem completion_weak {O : Type u} (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a : O → (DaggerRigidification.obj (coreDagger X)).Obj) :
    WeakEquivalence (DaggerActualDaggerKanObjectRestriction.comparison (coreDagger X) a) := by
  have := coreDagger_kan X
  exact DaggerActualDaggerKanObjectRestriction.comparison_weak (coreDagger X) a

end
end DaggerActualFixedDaggerCoreComparison
