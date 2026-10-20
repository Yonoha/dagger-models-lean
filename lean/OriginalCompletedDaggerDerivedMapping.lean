import OriginalCompletedDaggerMappingFibrancy
import OriginalSimplicialEquivariantEnrichedQuillen

/-!
# Fibrant original equivariant mapping objects of dagger completion

The original product-enriched right adjoint sends the actual completed mapping action to
a native Kan complex. Its original Ebullet C2 specialization is the actual equivariant
mapping simplicial set appearing in the completed dagger construction. No fibrancy
assumption on the original input dagger category is required.
-/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalCompletedDaggerMappingAction DaggerOriginalCompletedDaggerMappingFibrancy
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalSimplicialEquivariantEnrichedQuillen
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u

namespace DaggerOriginalCompletedDaggerDerivedMapping

noncomputable section

/-- The literal enriched right adjoint sends every projectively fibrant target to native Kan. -/
theorem enrichedMapping_kan (E X : Action SSet.{u} C2.{u}) [IsCofibrant E] [IsFibrant X] :
    (enrichedMapping E X).KanComplex := by
  have : (enrichedMappingFunctor E).IsRightAdjoint := (enrichedAdjunction E).isRightAdjoint
  let ht : IsTerminal ((enrichedMappingFunctor E).obj (⊤_ (Action SSet.{u} C2.{u}))) :=
    IsTerminal.isTerminalObj (enrichedMappingFunctor E) _ terminalIsTerminal
  apply (isFibrant_iff_of_isTerminal ((enrichedMappingFunctor E).map (terminal.from X)) ht).2
  have : Fibration (terminal.from X) := (isFibrant_iff X).1 inferInstance
  exact enrichedMapping_map_fibration E (terminal.from X)

/-- Every cofibrant original parameter gives native Kan mappings into actual dagger completion. -/
theorem completed_enrichedMapping_kan (E : Action SSet.{u} C2.{u}) [IsCofibrant E]
    (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    (enrichedMapping E (completedMappingAction C x y)).KanComplex := by
  have : IsFibrant (completedMappingAction C x y) := completedMappingAction_fibrant C x y
  exact enrichedMapping_kan E _

/-- The actual Ebullet C2 equivariant mapping object of the unchanged completed dagger Hom. -/
def completedDerivedMapping (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) : SSet.{u} :=
  enrichedMapping simplicialAction (completedMappingAction C x y)

/-- The actual completed equivariant mapping simplicial set is native Kan for every input. -/
theorem completedDerivedMapping_kan (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj) :
    (completedDerivedMapping C x y).KanComplex :=
  completed_enrichedMapping_kan simplicialAction C x y

/-- Original dagger functors act by the original equivariant completed Hom map. -/
def completedDerivedMappingMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D)
    (x y : C.Obj) : completedDerivedMapping C x y ⟶ completedDerivedMapping D (F.obj x) (F.obj y) :=
  enrichedMappingMap simplicialAction (completedMappingActionMap F x y)

/-- Actual completed Hom weak equivalences induce weak equivalences on these Kan mappings. -/
theorem completedDerivedMappingMap_weakEquivalence {C D : DaggerSimplicialCat.{u, u}}
    (F : C ⟶ D) (x y : C.Obj)
    [WeakEquivalence (completedMappingActionMap F x y).hom] :
    WeakEquivalence (completedDerivedMappingMap F x y) := by
  have : IsFibrant (completedMappingAction C x y) := completedMappingAction_fibrant C x y
  have : IsFibrant (completedMappingAction D (F.obj x) (F.obj y)) :=
    completedMappingAction_fibrant D (F.obj x) (F.obj y)
  have : WeakEquivalence (completedMappingActionMap F x y) := by
    apply (DaggerOriginalSimplicialActionModelCategory.weakEquivalence_iff_underlying _).2
    exact inferInstanceAs (WeakEquivalence (completedMappingActionMap F x y).hom)
  exact originalEC2_enrichedMapping_map_weakEquivalence (completedMappingActionMap F x y)

end

end DaggerOriginalCompletedDaggerDerivedMapping
