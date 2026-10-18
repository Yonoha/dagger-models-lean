import ActualRigHomWeakCoreMapping
import ActualGeneralIntrinsicLocalComparison

/-! Original rigidification-local weak maps induce ORIGINAL core-rigidification local weak maps.
Native DS is applied to the SAME cores and the SAME original core map, at ALL original objects.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeKanSourceOriginalCoreFactor
open DaggerActualCoreMappingFullVertexIso DaggerActualGeneralRightConeRigidificationLeg
open DaggerActualGeneralIntrinsicLocalComparison DaggerActualRigHomWeakCoreMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRigHomWeakCoreRigidification
noncomputable section

theorem castMap_weak_iff {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (a b : C.Obj) (c d : D.Obj) (ha : F.obj a = c) (hb : F.obj b = d) :
    WeakEquivalence (castMap F a b c d ha hb) ↔ WeakEquivalence (F.map a b) := by
  let T := OriginalOrdinaryEndpointTransport.transport D ha hb
  have : IsIso T := by unfold T OriginalOrdinaryEndpointTransport.transport; infer_instance
  change WeakEquivalence (F.map a b ≫ T) ↔ WeakEquivalence (F.map a b)
  exact weakEquivalence_postcomp_iff (F.map a b) T

theorem homMap_weak_iff_raw {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : X.obj (op ⦋0⦌)) :
    WeakEquivalence (homMap X a b f) ↔ WeakEquivalence
      ((rigidification.map f).map (RigidificationVertices.vertexEquiv X a)
        (RigidificationVertices.vertexEquiv X b)) :=
  castMap_weak_iff _ _ _ _ _ _ _

theorem rigidified_core_hom_weak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b))
    (x y : (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})).Obj) :
    WeakEquivalence ((rigidification.map (ordinaryCoreCandidateMap f)).map x y) := by
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex := native_quasi_core_kan X
  have : (ordinaryCoreCandidate Y : SSet.{u}).KanComplex := native_quasi_core_kan Y
  obtain ⟨a, rfl⟩ := (RigidificationVertices.vertexEquiv
    (ordinaryCoreCandidate X : SSet.{u})).surjective x
  obtain ⟨b, rfl⟩ := (RigidificationVertices.vertexEquiv
    (ordinaryCoreCandidate X : SSet.{u})).surjective y
  have hR := core_right_map_weak f hf a.val b.val
  have hH := (mapping_weak_iff_hom_weak (ordinaryCoreCandidateMap f)
    (coreVertex X a.val) (coreVertex X b.val)).mp hR
  exact (homMap_weak_iff_raw (ordinaryCoreCandidateMap f)
    (coreVertex X a.val) (coreVertex X b.val)).mp hH

end
end DaggerActualRigHomWeakCoreRigidification
