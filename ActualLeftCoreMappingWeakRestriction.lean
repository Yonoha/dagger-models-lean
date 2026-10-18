import ActualLeftMappingEquivalenceVerticesStable
import ActualRigHomWeakCorePullback

/-! Restrict the SAME original left-mapping weak map to the SAME original core mapping fibres.
Only ambient mapping weakness and exact original core-membership reflection are required.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalOrdinalJoinLeft DaggerActualQuasicategoryMappingFibres
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerActualMappingCoreVertexCharacterization
open DaggerActualCoreMappingFullVertexIso DaggerActualLeftMappingEquivalenceVerticesStable
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualLeftCoreMappingWeakRestriction
noncomputable section

variable {X Y : SSet.{u}} (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌))

def restrictedMap : (corePart X a b : SSet.{u}) ⟶
    (corePart Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) : SSet.{u}) :=
  SSet.Subcomplex.lift ((corePart X a b).ι ≫ map f ⦋0⦌ a b) (by
    intro q z hz
    obtain ⟨s, rfl⟩ := hz
    exact ((ordinaryCoreCandidateMap f).app (op ((ordinalJoinLeft ⦋0⦌).obj q.unop))
      ⟨s.val.val.val, s.property⟩).property)

theorem restrictedMap_ι : restrictedMap f a b ≫
    (corePart Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).ι =
      (corePart X a b).ι ≫ map f ⦋0⦌ a b := SSet.Subcomplex.lift_ι _ _

theorem corePart_inclusion_fibration (Y : SSet.{u}) [Y.Quasicategory]
    (c d : Y.obj (op ⦋0⦌)) : Fibration (corePart Y c d).ι := by
  rw [corePart_eq_fullVertex]
  exact selected_inclusion_fibration Y c d

theorem restrictedMap_weak [Y.Quasicategory]
    (hmem : ∀ q s, s ∈ (ordinaryCoreCandidate X).obj q ↔
      f.app q s ∈ (ordinaryCoreCandidate Y).obj q)
    [WeakEquivalence (map f ⦋0⦌ a b)] : WeakEquivalence (restrictedMap f a b) := by
  have : Fibration (corePart Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).ι :=
    corePart_inclusion_fibration Y _ _
  exact DaggerNativeSubcomplexWeakRestriction.weakEquivalence (map f ⦋0⦌ a b)
    (corePart X a b) (corePart Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b))
    (restrictedMap f a b) (restrictedMap_ι f a b)
    (fun q s ↦ hmem (op ((ordinalJoinLeft ⦋0⦌).obj q.unop)) s.val.val)

def coreMappingMap :
    leftMapping (ordinaryCoreCandidate X : SSet.{u}) (coreVertex X a) (coreVertex X b) ⟶
      leftMapping (ordinaryCoreCandidate Y : SSet.{u})
        (coreVertex Y (f.app (op ⦋0⦌) a)) (coreVertex Y (f.app (op ⦋0⦌) b)) :=
  map (ordinaryCoreCandidateMap f) ⦋0⦌ (coreVertex X a) (coreVertex X b)

theorem coreRestriction_square :
    (coreRestrictionIso X a b).hom ≫ restrictedMap f a b =
      coreMappingMap f a b ≫
        (coreRestrictionIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).hom := by
  apply NatTrans.ext
  funext q s
  rfl

theorem coreMappingMap_weak [Y.Quasicategory]
    (hmem : ∀ q s, s ∈ (ordinaryCoreCandidate X).obj q ↔
      f.app q s ∈ (ordinaryCoreCandidate Y).obj q)
    [WeakEquivalence (map f ⦋0⦌ a b)] : WeakEquivalence (coreMappingMap f a b) := by
  have : WeakEquivalence (restrictedMap f a b) := restrictedMap_weak f a b hmem
  have hc : WeakEquivalence ((coreRestrictionIso X a b).hom ≫ restrictedMap f a b) :=
    inferInstance
  rw [coreRestriction_square] at hc
  have : WeakEquivalence (coreMappingMap f a b ≫
      (coreRestrictionIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).hom) := hc
  exact weakEquivalence_of_postcomp (coreMappingMap f a b)
    (coreRestrictionIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).hom

end
end DaggerActualLeftCoreMappingWeakRestriction
