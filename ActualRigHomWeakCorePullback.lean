import ActualRigHomWeakHoFullyFaithful
import OriginalOrdinaryKanCoreEdgeMembership
import OriginalOrdinaryKanCoreCandidateFunctor
import NativeSubcomplexWeakRestriction

/-! The SAME core is the exact preimage under every original rigidification-local weak map.
All original simplicial sets are retained. No core weakness or quasi equivalence is assumed.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open OrdinaryRigidification DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership DaggerActualRigHomWeakHoFullyFaithful
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualRigHomWeakCorePullback
noncomputable section

theorem edge_invertible_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) (e : X.obj (op ⦋1⦌)) :
    edgeIsInvertible X e ↔ edgeIsInvertible Y (f.app (op ⦋1⦌) e) := by
  let H := (SSet.hoFunctor.map f).toFunctor
  have hH := ho_map_fully_faithful f hf
  have : H.Full := hH.1
  have : H.Faithful := hH.2
  have hn := congrFun
    (NatTrans.congr_app (homotopyCategoryUnit_natural f) (op ⦋1⦌)) e
  have hh := congrArg (fun s : (nerve (SSet.hoFunctor.obj Y)).obj (op ⦋1⦌) ↦
    IsIso s.hom) hn
  change IsIso (((homotopyCategoryUnit Y).app (op ⦋1⦌) (f.app (op ⦋1⦌) e)).hom) =
    IsIso (H.map (((homotopyCategoryUnit X).app (op ⦋1⦌) e).hom)) at hh
  unfold edgeIsInvertible
  rw [hh]
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    have := h
    exact isIso_of_reflects_iso _ H

theorem mem_core_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b))
    (q : SimplexCategoryᵒᵖ) (s : X.obj q) :
    s ∈ (ordinaryCoreCandidate X).obj q ↔ f.app q s ∈ (ordinaryCoreCandidate Y).obj q := by
  rw [mem_ordinaryCoreCandidate_iff_edges_iso, mem_ordinaryCoreCandidate_iff_edges_iso]
  apply forall_congr'
  intro α
  have hn := congrFun (f.naturality α.op) s
  change f.app (op ⦋1⦌) (X.map α.op s) = Y.map α.op (f.app q s) at hn
  rw [← hn]
  exact edge_invertible_iff f hf _

theorem core_eq_preimage {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) :
    ordinaryCoreCandidate X = (ordinaryCoreCandidate Y).preimage f := by
  ext q s
  exact mem_core_iff f hf q s

theorem core_isPullback {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ a b : (rigidification.obj X).Obj,
      WeakEquivalence ((rigidification.map f).map a b)) :
    IsPullback (ordinaryCoreCandidateMap f) (ordinaryCoreCandidate X).ι
      (ordinaryCoreCandidate Y).ι f :=
  DaggerNativeSubcomplexWeakRestriction.isPullback f (ordinaryCoreCandidate X)
    (ordinaryCoreCandidate Y) (ordinaryCoreCandidateMap f)
    (ordinaryCoreCandidateMap_comp_ι f) (mem_core_iff f hf)

end
end DaggerActualRigHomWeakCorePullback
