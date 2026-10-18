import OriginalCoreLeftMappingHomotopyComparison
import OriginalOrdinaryCoreHomotopyMapRecognition

/-!
# The actual mapping-space map of the original ordinary-core restriction

The native mapFiber map for the same original core restriction commutes with
the two literal core mapping inclusions and the original ambient mapping map.
Full faithfulness of the original ambient native homotopy functor gives
bijectivity on the actual core mapping-space components, via the already
verified native core homotopy functor and exact component-to-Hom comparison.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingPiZeroHom
open DaggerOriginalLeftMappingFunctoriality DaggerOriginalCoreLeftMappingFullComparison
open DaggerOriginalOrdinaryCoreHomotopyMapRecognition

universe u

namespace DaggerOriginalCoreLeftMappingFunctoriality

noncomputable section

/-- The actual mapping-space map induced by the same original ordinary-core restriction. -/
def coreMappingMap {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) :
    leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b ⟶
      leftMappingSpace (ordinaryCoreCandidate Y : SSet.{u})
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b) :=
  leftMappingMap (ordinaryCoreCandidateMap f) a b

/-- The same actual core mapping map commutes with the literal original ambient mapping map. -/
theorem coreMappingMap_comp_inclusion {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) :
    coreMappingMap f a b ≫ coreMappingInclusion Y
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b) =
      coreMappingInclusion X a b ≫ leftMappingMap f a.val b.val := by
  ext n v
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Original ambient native full faithfulness gives bijectivity on actual core mapping
 components. -/
theorem coreMappingMap_piZero_bijective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    [(SSet.hoFunctor.map f).toFunctor.Full] [(SSet.hoFunctor.map f).toFunctor.Faithful]
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) :
    Function.Bijective (SSet.mapπ₀ (coreMappingMap f a b)) := by
  haveI := coreHomotopyMap_faithful f hX
  haveI := coreHomotopyMap_full f hX hY
  let a' := (ordinaryCoreCandidateMap f).app (op ⦋0⦌) a
  let b' := (ordinaryCoreCandidateMap f).app (op ⦋0⦌) b
  have hCX : innerHornFillers (ordinaryCoreCandidate X : SSet.{u}) :=
    innerHornFillers_ordinaryCoreCandidate X hX
  have hCY : innerHornFillers (ordinaryCoreCandidate Y : SSet.{u}) :=
    innerHornFillers_ordinaryCoreCandidate Y hY
  constructor
  · intro p q hpq
    apply piZeroToHom_injective hCX a b
    apply (coreHomotopyMap f).map_injective
    dsimp only [coreHomotopyMap]
    rw [← piZeroToHom_naturality, ← piZeroToHom_naturality]
    exact congrArg (piZeroToHom (ordinaryCoreCandidate Y : SSet.{u}) a' b') hpq
  · intro p
    obtain ⟨h, hh⟩ := (coreHomotopyMap f).map_surjective
      (X := SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) a)
      (Y := SSet.Truncated.HomotopyCategory.mk
        (V := (SSet.truncation 2).obj (ordinaryCoreCandidate X : SSet.{u})) b)
      (piZeroToHom (ordinaryCoreCandidate Y : SSet.{u}) a' b' p)
    obtain ⟨c, hc⟩ := piZeroToHom_surjective hCX a b h
    refine ⟨c, ?_⟩
    apply piZeroToHom_injective hCY a' b'
    change piZeroToHom (ordinaryCoreCandidate Y : SSet.{u}) a' b'
      (SSet.mapπ₀ (leftMappingMap (ordinaryCoreCandidateMap f) a b) c) = _
    rw [piZeroToHom_naturality, hc]
    exact hh

end

end DaggerOriginalCoreLeftMappingFunctoriality
