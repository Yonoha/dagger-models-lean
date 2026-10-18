import ActualRightLeftOppositeWeakTransfer
import ActualLeftCoreMappingWeakRestriction
import NativePrefixMappingWeakIsoSquare
import ActualOrdinaryCoreOpposite

/-! Original core right-mapping maps are weak under ORIGINAL rigidification-local weakness.
Keep BOTH original endpoints and all original opposite/core naturality squares exactly.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerActualCoreOppositeMembership
open DaggerActualCoreMappingFullVertexIso DaggerActualOrdinaryCoreOpposite
open DaggerNativeQuasicategoryOpposite DaggerActualRightLeftOppositeWeakTransfer
open DaggerActualLeftCoreMappingWeakRestriction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRigHomWeakCoreMapping
noncomputable section

theorem op_core_mem_iff (X : SSet.{u}) [X.Quasicategory]
    (q : SimplexCategoryᵒᵖ) (s : X.op.obj q) :
    s ∈ (ordinaryCoreCandidate X.op).obj q ↔
      SSet.opObjEquiv s ∈ (ordinaryCoreCandidate X).obj q := by
  constructor
  · intro hs
    exact inv_mem_core X q ⟨s, hs⟩
  · intro hs
    exact op_mem_core X q ⟨s, hs⟩

theorem op_core_preimage_iff {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b))
    (q : SimplexCategoryᵒᵖ) (s : X.op.obj q) :
    s ∈ (ordinaryCoreCandidate X.op).obj q ↔
      (SSet.opFunctor.map f).app q s ∈ (ordinaryCoreCandidate Y.op).obj q := by
  rw [op_core_mem_iff, op_core_mem_iff]
  exact DaggerActualRigHomWeakCorePullback.mem_core_iff f hf q (SSet.opObjEquiv s)

theorem core_left_op_map_weak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (coreMappingMap (SSet.opFunctor.map f)
      (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a)) := by
  have : X.op.Quasicategory := quasicategory_op X
  have : Y.op.Quasicategory := quasicategory_op Y
  have := left_op_map_weak_of_RigHom_weak f hf a b
  exact coreMappingMap_weak (SSet.opFunctor.map f) _ _ (op_core_preimage_iff f hf)

theorem core_right_map_weak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (DaggerActualGeneralRightConeMapping.map (ordinaryCoreCandidateMap f)
      (coreVertex X a) (coreVertex X b)) := by
  have : X.op.Quasicategory := quasicategory_op X
  have : Y.op.Quasicategory := quasicategory_op Y
  let F := SSet.opFunctor.map (ordinaryCoreCandidateMap f)
  let G := ordinaryCoreCandidateMap (SSet.opFunctor.map f)
  let E := coreOppositeIso X
  let D := coreOppositeIso Y
  have hs : E.hom ≫ G = F ≫ D.hom := (coreOppositeIso_natural f).symm
  let α := SSet.opObjEquiv.symm (coreVertex X b)
  let β := SSet.opObjEquiv.symm (coreVertex X a)
  have hG : WeakEquivalence
      (DaggerNativePrefixMappingWeakIsoSquare.squareMap F G E D hs ⦋0⦌ α β) := by
    change WeakEquivalence (coreMappingMap (SSet.opFunctor.map f)
      (SSet.opObjEquiv.symm b) (SSet.opObjEquiv.symm a))
    exact core_left_op_map_weak f hf a b
  have hF : WeakEquivalence (DaggerActualQuasicategoryMappingFibres.map F ⦋0⦌ α β) :=
    (DaggerNativePrefixMappingWeakIsoSquare.map_weak_iff F G E D hs ⦋0⦌ α β).mpr hG
  exact (right_weak_iff_left_op_weak (ordinaryCoreCandidateMap f)
    (coreVertex X a) (coreVertex X b)).mpr hF

end
end DaggerActualRigHomWeakCoreMapping
