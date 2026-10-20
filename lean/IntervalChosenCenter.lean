import IntervalChosenHom
import ChosenFlagChosenSimplex

set_option autoImplicit false

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalChosenHom

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open NecklaceCode NecklaceThickening DaggerIntervalNecklaceCompletion

abbrev edgeFirst : (T.{u}.obj ⦋1⦌).Obj := ⟨ULift.up (0 : Fin 2)⟩
abbrev edgeLast : (T.{u}.obj ⦋1⦌).Obj := ⟨ULift.up (Fin.last 1)⟩

/-- The same original rho.inv/Kan unit and C.map of the supplied endpoint edge. -/
def edgeFunctor (a b : (E.{u}).obj (op ⦋0⦌)) : T.obj ⦋1⦌ ⟶ C.obj E :=
  thickeningUnit.app ⦋1⦌ ≫ C.map (endpointEdge a b)

theorem edgeFunctor_rho (a b : (E.{u}).obj (op ⦋0⦌)) :
    edgeFunctor a b = (ρ.app ⦋1⦌).inv ≫ C.map (endpointEdge a b) := rfl

theorem edgeFunctor_necklace (a b : (E.{u}).obj (op ⦋0⦌)) :
    (singleNCIso 1).inv ≫ overChosenFunctor (edgeObject a b) = edgeFunctor a b := by
  unfold overChosenFunctor edgeFunctor
  simp only [edgeObject]
  rw [chosenNecklaceIso_single]
  simp only [singleChosenIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [representable_inv]
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]

theorem edgeFunctor_first (a b : (E.{u}).obj (op ⦋0⦌)) :
    (edgeFunctor a b).obj edgeFirst = RV E a := by
  rw [← edgeFunctor_necklace]
  exact overChosenFunctor_first (edgeObject a b)

theorem edgeFunctor_last (a b : (E.{u}).obj (op ⦋0⦌)) :
    (edgeFunctor a b).obj edgeLast = RV E b := by
  rw [← edgeFunctor_necklace]
  exact overChosenFunctor_last (edgeObject a b)

def edgePathCenter : (edgeFirst.{u} ⟶[SSet.{u}] edgeLast).obj (op ⦋0⦌) :=
  DaggerOriginalPathContraction.center (ULift.up (0 : Fin 2))
    (ULift.up (Fin.last 1)) (Fin.zero_le _)

def edgeCenter (a b : (E.{u}).obj (op ⦋0⦌)) :
    (RV E a ⟶[SSet.{u}] RV E b).obj (op ⦋0⦌) :=
  (targetHomTransport (edgeFunctor_first a b) (edgeFunctor_last a b)).app (op ⦋0⦌)
    (((edgeFunctor a b).map edgeFirst edgeLast).app (op ⦋0⦌) edgePathCenter)

theorem edge_bottom_path :
    ((singleNCIso 1).hom.map (outerLeft (single 1)) (outerRight (single 1))).app
      (op ⦋0⦌) ((outerFlagIso (single 1)).hom.app (op ⦋0⦌)
        (DaggerOriginalIntervalFlagContraction.bottomFlag 1 0)) = edgePathCenter.{u} := by
  exact CategoryTheory.Functor.ext (fun _ ↦ CategoryTheory.SimplicialThickening.Path.ext rfl)

theorem edge_bottom_joint :
    ((singleNCIso 1).inv.map edgeFirst edgeLast).app (op ⦋0⦌) edgePathCenter =
      (outerFlagIso (single 1)).hom.app (op ⦋0⦌)
        (DaggerOriginalIntervalFlagContraction.bottomFlag 1 0) := by
  exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

theorem chosen_center_edge (a b : (E.{u}).obj (op ⦋0⦌)) :
    (flagOriginalHomIso E a b).hom.app (op ⦋0⦌)
      (DaggerOriginalIntervalFlagContraction.center (a := a) (b := b)) = edgeCenter a b := by
  change (flagOriginalHomIso E a b).hom.app (op ⦋0⦌)
    (Quot.mk _ ⟨edgeObject a b, DaggerOriginalIntervalFlagContraction.bottomFlag 1 0⟩) = _
  rw [flagOriginalHomIso_raw]
  unfold chosenFlagLeg edgeCenter
  have H := enrichedFunctor_hom_congr_to_fixed (edgeFunctor_necklace a b)
    edgeFirst edgeLast (RV E a) (RV E b)
    (overChosenFunctor_first (edgeObject a b))
    (overChosenFunctor_last (edgeObject a b))
    (edgeFunctor_first a b) (edgeFunctor_last a b)
  have Hpoint := congrFun (NatTrans.congr_app H (op ⦋0⦌)) edgePathCenter
  simpa only [DaggerModels.SimplicialCat.comp_map, NatTrans.comp_app,
    Function.comp_apply, edge_bottom_joint] using Hpoint

theorem originalCenter_edge (z w : (C.{u}.obj E).Obj) :
    originalCenter z w =
      (targetHomTransport (sourceVertex_endpoint z) (sourceVertex_endpoint w)).app (op ⦋0⦌)
        (edgeCenter (sourceVertex z) (sourceVertex w)) := by
  rw [originalCenter_raw, originalFlagHomIso_hom]
  exact congrArg
    ((targetHomTransport (sourceVertex_endpoint z) (sourceVertex_endpoint w)).app (op ⦋0⦌))
    (chosen_center_edge (sourceVertex z) (sourceVertex w))

theorem originalCenter_diagonal (z : (C.{u}.obj E).Obj) :
    originalCenter z z = (eId SSet z).app (op ⦋0⦌) PUnit.unit := by
  rw [originalCenter_raw, originalFlagHomIso_hom,
    DaggerOriginalIntervalFlagContraction.center_diagonal]
  have H := congrFun (NatTrans.congr_app
    (flagOriginalHomIso_identity E (sourceVertex z)) (op ⦋0⦌)) PUnit.unit
  change (flagOriginalHomIso E (sourceVertex z) (sourceVertex z)).hom.app (op ⦋0⦌)
    ((flagIdentity E (sourceVertex z)).app (op ⦋0⦌) PUnit.unit) = _ at H
  change (targetHomTransport (sourceVertex_endpoint z) (sourceVertex_endpoint z)).app
    (op ⦋0⦌) ((flagOriginalHomIso E (sourceVertex z) (sourceVertex z)).hom.app (op ⦋0⦌)
      ((flagIdentity E (sourceVertex z)).app (op ⦋0⦌) PUnit.unit)) = _
  rw [H]
  have HI := targetHomTransport_id (𝟙 (C.obj E)) (RV E (sourceVertex z)) z
    (sourceVertex_endpoint z)
  change eId SSet (RV E (sourceVertex z)) ≫
    targetHomTransport (sourceVertex_endpoint z) (sourceVertex_endpoint z) = eId SSet z at HI
  exact congrFun (NatTrans.congr_app HI (op ⦋0⦌)) PUnit.unit

theorem originalCenter_diagonal_map (z : (C.{u}.obj E).Obj) :
    (SSet.const (originalCenter z z) : 𝟙_ SSet.{u} ⟶ originalHom z z) = eId SSet z := by
  ext q t
  cases t
  rw [originalCenter_diagonal]
  change (originalHom z z).map (q.unop.const ⦋0⦌ 0).op
    ((eId SSet z).app (op ⦋0⦌) PUnit.unit) = _
  exact (congrFun ((eId SSet z).naturality (q.unop.const ⦋0⦌ 0).op) PUnit.unit).symm

end

end DaggerOriginalIntervalChosenHom
