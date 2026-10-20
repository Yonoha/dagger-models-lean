import NativeDaggerKanUnitaryCoreWeak
import ActualDaggerOrdinaryCoreMaps

/-! The SAME original greatest core inclusion induces a weak original unitary-core map.
No change of core, dagger, canonical vertices or full canonical subcomplex is made.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerNativeKanRigHomWeakRecognition DaggerNativeDaggerKanUnitaryCoreWeak
open DaggerActualDaggerOrdinaryCore
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualOriginalCoreInclusionUnitaryWeak
noncomputable section

theorem ordinary_core_inclusion_map (X : SSet.{u}) :
    ordinaryCoreCandidateMap (ordinaryCoreCandidate X).ι =
      (ordinaryCoreCandidate (ordinaryCoreCandidate X : SSet.{u})).ι := by
  apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
  exact ordinaryCoreCandidateMap_comp_ι (ordinaryCoreCandidate X).ι

theorem core_inclusion_core_map_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    WeakEquivalence (daggerCoreMap (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)).hom := by
  change WeakEquivalence (ordinaryCoreCandidateMap (ordinaryCoreCandidate X.toSSet).ι)
  rw [ordinary_core_inclusion_map]
  have := DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan X.toSSet
  have := core_inclusion_isIso (ordinaryCoreCandidate X.toSSet : SSet.{u})
  infer_instance

theorem unitary_core_inclusion_weak (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    WeakEquivalence
      (unitaryCoreFunctor.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)) := by
  have := core_inclusion_core_map_weak X
  exact DaggerOriginalUnitaryCoreWeakEquivalenceRestriction.unitaryCore_map_weakEquivalence
    (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)
    (mapπ₀_surjective_of_vertices _ (unitary_vertices_surjective
      (DaggerActualDaggerOrdinaryCoreMaps.inclusion X) (coreVerticesEquiv X).surjective))

end
end DaggerActualOriginalCoreInclusionUnitaryWeak
