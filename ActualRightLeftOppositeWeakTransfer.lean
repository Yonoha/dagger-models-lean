import ActualGeneralRightConeNaturality
import ActualGeneralIntrinsicLocalComparison
import NativeSimplicialOppositeKanWeak

/-! Transfer the SAME actual right-map weakness to the SAME original opposite-left map. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualGeneralRightConeKan DaggerActualGeneralRightConeRigidificationLeg
open DaggerActualGeneralIntrinsicLocalComparison DaggerNativeSimplicialOppositeKanWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRightLeftOppositeWeakTransfer
noncomputable section

theorem right_weak_iff_opposite_map_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b) ↔
      WeakEquivalence (oppositeMap f a b) := by
  let E := (comparisonIso X a b).hom
  let F := (comparisonIso Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b)).hom
  let R := DaggerActualGeneralRightConeMapping.map f a b
  let L := oppositeMap f a b
  have hs : R ≫ F = E ≫ L := hom_naturality f a b
  constructor
  · intro h
    have : WeakEquivalence R := h
    have hc : WeakEquivalence (R ≫ F) := inferInstance
    have : WeakEquivalence (E ≫ L) := hs ▸ hc
    exact weakEquivalence_of_precomp E L
  · intro h
    have : WeakEquivalence L := h
    have hc : WeakEquivalence (E ≫ L) := inferInstance
    have : WeakEquivalence (R ≫ F) := hs.symm ▸ hc
    exact weakEquivalence_of_postcomp R F

theorem right_weak_iff_left_op_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map f a b) ↔
      WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map (SSet.opFunctor.map f)
        ⦋0⦌ (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a)) :=
  (right_weak_iff_opposite_map_weak f a b).trans (weak_op_iff _)

theorem left_op_map_weak_of_RigHom_weak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map (SSet.opFunctor.map f)
      ⦋0⦌ (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a)) := by
  have : WeakEquivalence ((rigidification.map f).map
      (RigidificationVertices.vertexEquiv X a) (RigidificationVertices.vertexEquiv X b)) :=
    hf _ _
  have hH : WeakEquivalence (homMap X a b f) := by
    unfold homMap DaggerModels.OriginalOrdinaryMovingHomColimits.castMap
      OriginalOrdinaryEndpointTransport.transport
    infer_instance
  exact (right_weak_iff_left_op_weak f a b).mp
    ((mapping_weak_iff_hom_weak f a b).mpr hH)

end
end DaggerActualRightLeftOppositeWeakTransfer
