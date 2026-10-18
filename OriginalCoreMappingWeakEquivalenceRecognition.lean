import OriginalKanMappingHomotopyRecognition
import OriginalCoreLeftMappingWeakEquivalences
import OriginalOrdinaryCoreHomotopyMapRecognition

/-!
# Recognition of weak equivalence of the actual original ordinary core map

Full faithfulness of the original ambient homotopy map reflects equality
of original core components. The original core mapping-space comparisons
and the exact vertex-coslice boundary bijections give all positive homotopy
degrees. Original core component coverage therefore gives a native weak
equivalence of the same original greatest-core restriction itself.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreInnerHorns DaggerOriginalOrdinaryCoreKan
open DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalUnitaryCoreOrdinaryEssentialSurjectivity
open DaggerOriginalOrdinaryCoreHomotopyMapRecognition
open DaggerOriginalLeftMappingFunctoriality DaggerOriginalLeftMappingFullFaithfulness
open DaggerOriginalCoreLeftMappingWeakEquivalences
open DaggerOriginalKanMappingHomotopyRecognition

universe u

namespace DaggerOriginalCoreMappingWeakEquivalenceRecognition

noncomputable section

/-- Ambient full faithfulness reflects equality of actual original core components. -/
theorem core_mapπ₀_injective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    [(SSet.hoFunctor.map f).toFunctor.Full] [(SSet.hoFunctor.map f).toFunctor.Faithful] :
    Function.Injective (SSet.mapπ₀ (ordinaryCoreCandidateMap f)) := by
  intro c d h
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective d
  have heq : SSet.π₀.mk ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a) =
      SSet.π₀.mk ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b) := by
    simpa only [SSet.mapπ₀_mk] using h
  obtain ⟨e⟩ := core_homotopy_iso_of_pi0_eq Y hY heq
  haveI := coreHomotopyMap_full f hX hY
  obtain ⟨g, _⟩ := (coreHomotopyMap f).map_surjective
    (X := SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) a)
    (Y := SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) b) e.hom
  obtain ⟨k, _⟩ := original_homMk_surjective (ordinaryCoreCandidate X : SSet.{u})
    (innerHornFillers_ordinaryCoreCandidate X hX) g
  exact SSet.π₀.sound k.edge k.src_eq k.tgt_eq

/-- Actual mapping-space weak equivalences and actual core component coverage imply weak
 equivalence of the original greatest-core restriction itself. -/
theorem ordinaryCore_map_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hmap : ∀ x y : X.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f x y))
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (ordinaryCoreCandidateMap f))) :
    WeakEquivalence (ordinaryCoreCandidateMap f) := by
  haveI := ordinaryCoreCandidate_kan X hX
  haveI := ordinaryCoreCandidate_kan Y hY
  haveI := homotopyMap_faithful_of_mapping_weakEquivalences f hX hY hmap
  haveI := homotopyMap_full_of_mapping_weakEquivalences f hX hY hmap
  apply weakEquivalence_of_components_and_leftMappingWeakEquivalences
  · exact ⟨core_mapπ₀_injective f hX hY, hπ₀⟩
  · intro a
    exact coreMappingMap_weakEquivalence f hX hY hmap a a

end

end DaggerOriginalCoreMappingWeakEquivalenceRecognition
