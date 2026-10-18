import ActualGeneralRightConeNaturality
import ActualQQuillenEquivalence

/-! Reuse the SAME original Q Quillen equivalence on EVERY original quasi-category mapping space. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerActualGeneralRightConeMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualGeneralRightMappingQKanBridge
noncomputable section

theorem counit_weak (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (realizationSingularAdjunction.counit.app (rightMapping X a b)) := by
  have := DaggerActualGeneralRightConeKan.rightMapping_kan X a b
  exact DaggerActualQKanCounitWeakEquivalence.counit_weakEquivalence _

theorem realization_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (realization.map (DaggerActualGeneralRightConeMapping.map f a b)) ↔
      WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b) :=
  DaggerActualQRealizationWeakReflection.realization_weakEquivalence_iff _

end
end DaggerActualGeneralRightMappingQKanBridge
