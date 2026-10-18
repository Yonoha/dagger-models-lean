import OriginalCoreMappingWeakEquivalenceRecognition
import ActualRightLeftOppositeWeakTransfer
import NativeKanSourceOriginalCoreFactor
import NativeKanSimplicialOpposite

/-! Reuse original Kan recognition via the exact original opposite-left comparison.
For native Kan inputs, Rig-Hom local weakness and original vertex coverage imply
weakness of the original whole map itself. No dagger structure is imposed.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes
open DaggerNativeHoIsoTriangles DaggerOriginalLeftMappingFunctoriality
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanRigHomWeakRecognition
noncomputable section

theorem mapπ₀_surjective_of_vertices {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective (f.app (op ⦋0⦌))) : Function.Surjective (SSet.mapπ₀ f) := by
  intro c
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective c
  obtain ⟨x, hx⟩ := hf y
  refine ⟨SSet.π₀.mk x, ?_⟩
  rw [SSet.mapπ₀_mk, hx]

theorem core_map_vertices_surjective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    Function.Surjective ((ordinaryCoreCandidateMap f).app (op ⦋0⦌)) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  exact ⟨⟨x, vertex_mem_ordinaryCoreCandidate X x⟩, Subtype.ext hx⟩

theorem core_inclusion_isIso (K : SSet.{u}) [K.KanComplex] :
    IsIso (ordinaryCoreCandidate K).ι := by
  rw [ordinaryCoreCandidate_eq_top_of_kan K]
  change IsIso (SSet.Subcomplex.topIso K).hom
  infer_instance

theorem weak_of_core_weak {X Y : SSet.{u}} [X.KanComplex] [Y.KanComplex] (f : X ⟶ Y)
    (hf : WeakEquivalence (ordinaryCoreCandidateMap f)) : WeakEquivalence f := by
  have := core_inclusion_isIso X
  have := core_inclusion_isIso Y
  have : WeakEquivalence (ordinaryCoreCandidateMap f) := hf
  have h : WeakEquivalence ((ordinaryCoreCandidate X).ι ≫ f) := by
    change WeakEquivalence (ordinaryCoreCandidateMap f ≫ (ordinaryCoreCandidate Y).ι)
    infer_instance
  exact weakEquivalence_of_precomp (ordinaryCoreCandidate X).ι f

theorem weak_of_rig_hom_weak_and_vertices {X Y : SSet.{u}}
    [X.KanComplex] [Y.KanComplex] (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b))
    (hv : Function.Surjective (f.app (op ⦋0⦌))) : WeakEquivalence f := by
  let g := SSet.opFunctor.map f
  have : X.op.KanComplex := DaggerNativeKanSimplicialOpposite.kan_op X
  have : Y.op.KanComplex := DaggerNativeKanSimplicialOpposite.kan_op Y
  have hg : Function.Surjective (g.app (op ⦋0⦌)) := hv
  have hleft (x y : X.op.obj (op ⦋0⦌)) : WeakEquivalence (leftMappingMap g x y) := by
    have h := DaggerActualRightLeftOppositeWeakTransfer.left_op_map_weak_of_RigHom_weak
      f hf (SSet.opObjEquiv y) (SSet.opObjEquiv x)
    simpa only [Equiv.symm_apply_apply] using h
  have hc : WeakEquivalence (ordinaryCoreCandidateMap g) :=
    DaggerOriginalCoreMappingWeakEquivalenceRecognition.ordinaryCore_map_weakEquivalence
      g (native_inner_fillers X.op) (native_inner_fillers Y.op) hleft
        (mapπ₀_surjective_of_vertices _ (core_map_vertices_surjective g hg))
  exact (DaggerNativeSimplicialOppositeKanWeak.weak_op_iff f).mp (weak_of_core_weak g hc)

end
end DaggerNativeKanRigHomWeakRecognition
