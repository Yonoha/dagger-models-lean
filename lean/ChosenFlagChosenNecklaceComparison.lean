import ChosenFlagChosenFunctor
import ChosenFlagLegImage
import ChosenNecklaceFlagChosenIso

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode)

/-- Exact prescribed object map, not an alternative choice of vertices. -/
theorem chosenNecklaceIso_RV_object (x : (toSSet.{u} T).obj (op ⦋0⦌)) :
    (chosenNecklaceIso T).hom.obj (RV T.toSSet x) = ⟨T.verticesEquiv x⟩ := by
  rw [chosenNecklaceIso_objects, canonicalNCObject_vertex]

theorem overChosenFunctor_toNC {a b : (toSSet.{u} T).obj (op ⦋0⦌)}
    (P : NecklacesOver T.toSSet a b) :
    overChosenFunctor P ≫ (chosenNecklaceIso T).hom = generalNCMap P.map := by
  unfold overChosenFunctor
  rw [Category.assoc, chosenNecklaceIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

theorem generalNCMap_over_first {a b : (toSSet.{u} T).obj (op ⦋0⦌)}
    (P : NecklacesOver T.toSSet a b) :
    (generalNCMap P.map).obj (outerLeft P.code) = ⟨T.verticesEquiv a⟩ := by
  apply congrArg NecklaceThickening.mk
  change mapVertices P.map (ULift.up 0) = T.verticesEquiv a
  exact congrArg T.verticesEquiv P.first

theorem generalNCMap_over_last {a b : (toSSet.{u} T).obj (op ⦋0⦌)}
    (P : NecklacesOver T.toSSet a b) :
    (generalNCMap P.map).obj (outerRight P.code) = ⟨T.verticesEquiv b⟩ := by
  apply congrArg NecklaceThickening.mk
  change mapVertices P.map (ULift.up (Fin.last P.code.len)) = T.verticesEquiv b
  exact congrArg T.verticesEquiv P.last

/-- Whole actual-C evaluation equals the complete joint-path flag evaluation on a necklace. -/
theorem chosenFlagFunctor_necklace (T : NecklaceCode) :
    chosenFlagFunctor T.toSSet ≫ (chosenNecklaceIso T).hom = necklaceFlagFunctor.{u} T := by
  have ho : ∀ x : (E (toSSet.{u} T)).Obj,
      (chosenFlagFunctor T.toSSet ≫ (chosenNecklaceIso T).hom).obj x =
        (necklaceFlagFunctor T).obj x := chosenNecklaceIso_RV_object T
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply NatTrans.ext
  funext q t
  induction t using Quot.ind with | _ p
  have hpx := (congrArg (chosenNecklaceIso T).hom.obj
    (overChosenFunctor_first p.1)).trans (ho x)
  have hpy := (congrArg (chosenNecklaceIso T).hom.obj
    (overChosenFunctor_last p.1)).trans (ho y)
  have H := enrichedFunctor_hom_congr_to_fixed (overChosenFunctor_toNC T p.1)
    (outerLeft p.1.code) (outerRight p.1.code) ⟨T.verticesEquiv x⟩ ⟨T.verticesEquiv y⟩
    hpx hpy (generalNCMap_over_first T p.1) (generalNCMap_over_last T p.1)
  have Hleg := chosenFlagLeg_image p.1 (chosenNecklaceIso T).hom
    ⟨T.verticesEquiv x⟩ ⟨T.verticesEquiv y⟩ (ho x) (ho y)
  rw [H] at Hleg
  change ((chosenFlagLeg p.1 ≫ (chosenNecklaceIso T).hom.map (RV T.toSSet x)
    (RV T.toSSet y) ≫ targetHomTransport (ho x) (ho y)).app q p.2) = _
  rw [Hleg]
  refine CategoryTheory.Functor.ext (fun i ↦ JointPath.ext ?_)
  change (((targetHomTransport (generalNCMap_over_first T p.1)
    (generalNCMap_over_last T p.1)).app q
      (((generalNCMap p.1.map).map (outerLeft p.1.code) (outerRight p.1.code)).app q
        ((outerFlagIso p.1.code).hom.app q p.2))).obj i).I = _
  rw [show targetHomTransport (generalNCMap_over_first T p.1)
      (generalNCMap_over_last T p.1) =
    castHom (generalNCMap_over_first T p.1) (generalNCMap_over_last T p.1) from rfl,
    castHom_I]
  rfl

theorem chosenFlagFunctor_necklace_exact (T : NecklaceCode) :
    chosenFlagFunctor T.toSSet = (flagChosenNecklaceIso.{u} T).hom := by
  apply (cancel_mono (chosenNecklaceIso T).hom).mp
  rw [chosenFlagFunctor_necklace]
  change necklaceFlagFunctor T =
    (necklaceFlagFunctor T ≫ (chosenNecklaceIso T).inv) ≫ (chosenNecklaceIso T).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end DaggerChosenRigidificationNecklace
