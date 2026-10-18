import ActualRigHomWeakCoreRigidification
import ActualFirstCoreComparisonWeakReduction

/-! The EXISTING ORIGINAL first core comparison is locally weak for EVERY original quasi X.
The original core, ALL isomorphism components and exact original dagger comparison are retained.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerActualDaggerOrdinaryCore
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualFirstCoreComparisonAllQuasicategories
noncomputable section

theorem original_gadget_core_unit_hom_weak (X : SSet.{u}) [X.Quasicategory]
    (a b : (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})).Obj) :
    WeakEquivalence ((rigidification.map
      (ordinaryCoreCandidateMap (DaggerActualFibrantGadgetData.unit.app X))).map a b) := by
  have : (DaggerActualFibrantGadgetData.gadget.obj X).Quasicategory :=
    DaggerActualFibrantGadgetExtensions.gadget_quasicategory X
  exact DaggerActualRigHomWeakCoreRigidification.rigidified_core_hom_weak
    (X := X) (Y := DaggerActualFibrantGadgetData.gadget.obj X)
    (DaggerActualFibrantGadgetData.unit.app X)
    (DaggerActualFibrantGadgetRigidificationWeak.hom_weak X) a b

theorem ordinary_hom_weak (X : SSet.{u}) [X.Quasicategory]
    (a b : (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})).Obj) :
    WeakEquivalence ((DaggerActualOrdinaryCoreIsomorphismComparison.comparison X).map a b) :=
  (DaggerActualFirstCoreComparisonWeakReduction.hom_weak_iff X a b).mpr
    (original_gadget_core_unit_hom_weak X a b)

theorem dagger_hom_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a b : (DaggerRigidification.obj (coreDagger X)).Obj) :
    WeakEquivalence
      ((DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).map a b) :=
  (DaggerActualFirstCoreComparisonWeakReduction.dagger_hom_weak_iff X a b).mpr
    (original_gadget_core_unit_hom_weak X.toSSet a b)

end
end DaggerActualFirstCoreComparisonAllQuasicategories
