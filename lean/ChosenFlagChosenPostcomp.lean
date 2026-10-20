import ChosenFlagChosenFunctor
import ChosenFlagFunctor

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem overChosenFunctor_postcomp (f : X ⟶ Y) (P : NecklacesOver X a b) :
    overChosenFunctor ((NecklacesOver.postcomp f).obj P) =
      overChosenFunctor P ≫ C.map f := by
  unfold overChosenFunctor
  change (chosenNecklaceIso P.code).inv ≫ C.map (P.map ≫ f) = _
  rw [C.map_comp, Category.assoc]

/-- Literal raw-leg postcomposition, with both RV equalities in their original direction. -/
theorem chosenFlagLeg_postcomp (f : X ⟶ Y) (P : NecklacesOver X a b) :
    chosenFlagLeg ((NecklacesOver.postcomp f).obj P) =
      chosenFlagLeg P ≫ (C.map f).map (RV X a) (RV X b) ≫
        targetHomTransport
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f a)
          (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f b)
    := by
  let F := overChosenFunctor P
  let ha := DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f a
  let hb := DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f b
  let hx := (congrArg (C.map f).obj (overChosenFunctor_first P)).trans ha
  let hy := (congrArg (C.map f).obj (overChosenFunctor_last P)).trans hb
  have H := enrichedFunctor_hom_congr_to_fixed (overChosenFunctor_postcomp f P)
    (outerLeft P.code) (outerRight P.code) (RV Y (f.app _ a)) (RV Y (f.app _ b))
    (overChosenFunctor_first ((NecklacesOver.postcomp f).obj P))
    (overChosenFunctor_last ((NecklacesOver.postcomp f).obj P)) hx hy
  unfold chosenFlagLeg
  simp only [Category.assoc]
  rw [← Category.assoc (targetHomTransport (overChosenFunctor_first P)
    (overChosenFunctor_last P)), enriched_map_endpoint_transport]
  simp only [Category.assoc]
  rw [targetHomTransport_trans]
  change (outerFlagIso P.code).hom ≫
    ((overChosenFunctor ((NecklacesOver.postcomp f).obj P)).map
      (outerLeft P.code) (outerRight P.code) ≫
      targetHomTransport
        (overChosenFunctor_first ((NecklacesOver.postcomp f).obj P))
        (overChosenFunctor_last ((NecklacesOver.postcomp f).obj P))) =
    (outerFlagIso P.code).hom ≫
      ((overChosenFunctor P ≫ C.map f).map (outerLeft P.code) (outerRight P.code) ≫
        targetHomTransport hx hy)
  rw [H]

theorem chosenFlagFunctor_naturality (f : X ⟶ Y) :
    EMap f ≫ chosenFlagFunctor Y = chosenFlagFunctor X ≫ C.map f := by
  have ho : ∀ x : (E X).Obj,
      (EMap f ≫ chosenFlagFunctor Y).obj x =
        (chosenFlagFunctor X ≫ C.map f).obj x :=
    fun x ↦ (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality
      f x).symm
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply NatTrans.ext
  funext q t
  induction t using Quot.ind with | _ p
  have H := congrFun (NatTrans.congr_app (chosenFlagLeg_postcomp f p.1) q) p.2
  change (targetHomTransport (ho x) (ho y)).app q
    ((chosenFlagLeg ((NecklacesOver.postcomp f).obj p.1)).app q p.2) = _
  rw [H]
  change ((chosenFlagLeg p.1 ≫ (C.map f).map (RV X x) (RV X y) ≫
    targetHomTransport
      (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f x)
      (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f y) ≫
    targetHomTransport (ho x) (ho y)).app q p.2) = _
  simp only [targetHomTransport, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  rfl

end

end DaggerChosenRigidificationNecklace
