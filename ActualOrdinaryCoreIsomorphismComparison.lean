import ActualSimplicialIsomorphismComponentFactor
import NativeKanSourceOriginalCoreFactor
import ActualKanRigidificationCompletionWeak
import ActualDaggerCoreIsomorphismComponentComparison
import NativeEnrichedHomRestrictionMonomorphism

/-! The same first core comparison for arbitrary original quasi-categories, with dagger anchor. -/
set_option autoImplicit false
open CategoryTheory DaggerModels OrdinaryRigidification
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerActualSimplicialIsomorphismComponentPart
universe u
namespace DaggerActualOrdinaryCoreIsomorphismComparison
noncomputable section

theorem inclusion_mono (C : SimplicialCat.{u, u}) : Mono (inclusion C) :=
  DaggerNativeEnrichedHomRestrictionMonomorphism.inclusion_mono C
    (homSubcomplex C) (id_mem C) (comp_mem C)

def comparison (X : SSet.{u}) [X.Quasicategory] :
    rigidification.obj (ordinaryCoreCandidate X : SSet.{u}) ⟶ part (rigidification.obj X) := by
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan X
  exact DaggerActualSimplicialIsomorphismComponentFactor.factor
    (rigidification.map (ordinaryCoreCandidate X).ι)
    (DaggerActualKanRigidificationCompletionWeak.component_groupoid _)

theorem comparison_comp_inclusion (X : SSet.{u}) [X.Quasicategory] :
    comparison X ≫ inclusion (rigidification.obj X) =
      rigidification.map (ordinaryCoreCandidate X).ι := by
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan X
  exact DaggerActualSimplicialIsomorphismComponentFactor.factor_comp_inclusion
    (rigidification.map (ordinaryCoreCandidate X).ι)
    (DaggerActualKanRigidificationCompletionWeak.component_groupoid _)

theorem dagger_underlying (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).toEnrichedFunctor =
      comparison X.toSSet := by
  have := inclusion_mono (rigidification.obj X.toSSet)
  apply (cancel_mono (inclusion (rigidification.obj X.toSSet))).mp
  exact (congrArg (fun F ↦ F.toEnrichedFunctor)
    (DaggerActualDaggerCoreIsomorphismComponentComparison.comparison_comp_inclusion X)).trans
      (comparison_comp_inclusion X.toSSet).symm

theorem naturality {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory] (f : X ⟶ Y) :
    comparison X ≫ DaggerActualSimplicialIsomorphismComponentMaps.map (rigidification.map f) =
      rigidification.map (ordinaryCoreCandidateMap f) ≫ comparison Y := by
  have := inclusion_mono (rigidification.obj Y)
  apply (cancel_mono (inclusion (rigidification.obj Y))).mp
  rw [Category.assoc, DaggerActualSimplicialIsomorphismComponentMaps.inclusion_natural,
    ← Category.assoc, comparison_comp_inclusion, Category.assoc, comparison_comp_inclusion,
    ← rigidification.map_comp, ← rigidification.map_comp, ordinaryCoreCandidateMap_comp_ι]

end
end DaggerActualOrdinaryCoreIsomorphismComparison
