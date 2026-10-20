import OriginalOrdinaryMovingHomColimitReconciled
import SimplicialIsoHoms
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Original ordinary Hom diagrams along a transfinite composition

The moving source and target objects begin at the actual inverse bottom
isomorphism. Their final labels and Hom cocone retain the original full
transfinite arrow. Every proper limit and the final stage use the accepted
moving-Hom colimit universal property.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerModels.OriginalOrdinaryHomTransfinite

noncomputable section

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : SimplicialCat.{u, u}} {f : X ⟶ Y}
variable (h : CategoryTheory.TransfiniteCompositionOfShape J f)

/-- The original object propagated from the inverse bottom isomorphism. -/
def movingObj (x : X.Obj) (j : J) : (h.F.obj j).Obj :=
  (h.F.map (homOfLE bot_le : ⊥ ⟶ j)).obj (h.isoBot.inv.obj x)

/-- Original transition maps carry each moving object to its next value. -/
theorem moving_naturality (x : X.Obj) {j k : J} (g : j ⟶ k) :
    (h.F.map g).obj (movingObj h x j) = movingObj h x k := by
  change (h.F.map g).obj ((h.F.map (homOfLE bot_le)).obj _) = _
  rw [← SimplicialCat.comp_obj, ← h.F.map_comp]
  rfl

/-- At the bottom, the moving object is literally the inverse-iso image. -/
theorem moving_bot (x : X.Obj) : movingObj h x ⊥ = h.isoBot.inv.obj x := by
  change (h.F.map (homOfLE bot_le : ⊥ ⟶ ⊥)).obj _ = _
  rw [show (homOfLE bot_le : (⊥ : J) ⟶ ⊥) = 𝟙 ⊥ from rfl, h.F.map_id]
  rfl

/-- The actual final cocone sends each moving object to its original endpoint. -/
theorem finalEndpoint (x : X.Obj) (j : J) :
    (h.incl.app j).obj (movingObj h x j) = f.obj x := by
  have hw : h.F.map (homOfLE bot_le : ⊥ ⟶ j) ≫ h.incl.app j = h.incl.app ⊥ := by
    exact (h.incl.naturality (homOfLE bot_le : ⊥ ⟶ j)).trans (Category.comp_id _)
  exact (congrArg (fun g : h.F.obj ⊥ ⟶ Y ↦ g.obj (h.isoBot.inv.obj x)) hw).trans
    (congrArg (fun g : X ⟶ Y ↦ g.obj x) h.fac)

/-- The original moving-endpoint Hom diagram, with both endpoint casts. -/
def homDiagram (x y : X.Obj) : J ⥤ SSet.{u} :=
  OriginalOrdinaryMovingHomColimits.homDiagram h.F (movingObj h x) (movingObj h y)
    (moving_naturality h x) (moving_naturality h y)

/-- The actual final cocone of original Hom maps and endpoint casts. -/
def homCocone (x y : X.Obj) : Cocone (homDiagram h x y) :=
  OriginalOrdinaryMovingHomColimits.homCocone h.F (movingObj h x) (movingObj h y)
    (moving_naturality h x) (moving_naturality h y) (Cocone.mk Y h.incl)
    (f.obj x) (f.obj y) (finalEndpoint h x) (finalEndpoint h y)

/-- The full final original Hom cocone universal property. -/
def finalIsColimit (x y : X.Obj) : IsColimit (homCocone h x y) :=
  OriginalOrdinaryMovingHomColimits.homIsColimit h.isColimit
    (movingObj h x) (movingObj h y)
    (moving_naturality h x) (moving_naturality h y)
    (f.obj x) (f.obj y) (finalEndpoint h x) (finalEndpoint h y)

/-- Every proper-limit original Hom cocone has its full universal property. -/
def limitIsColimit (x y : X.Obj) (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone (homDiagram h x y)) := by
  letI : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
  exact OriginalOrdinaryMovingHomColimits.homIsColimit
    (h.F.isColimitOfIsWellOrderContinuous m hm)
    (fun j ↦ movingObj h x j.val) (fun j ↦ movingObj h y j.val)
    (fun g ↦ moving_naturality h x ((Set.principalSegIio m).monotone.functor.map g))
    (fun g ↦ moving_naturality h y ((Set.principalSegIio m).monotone.functor.map g))
    (movingObj h x m) (movingObj h y m)
    (fun j ↦ moving_naturality h x (homOfLE j.property.le))
    (fun j ↦ moving_naturality h y (homOfLE j.property.le))

/-- The moving Hom diagram is well-order-continuous at all proper limits. -/
instance homWellOrderContinuous (x y : X.Obj) : (homDiagram h x y).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨limitIsColimit h x y m hm⟩

/-- The bottom Hom isomorphism uses the actual ordinary enriched iso map. -/
def isoBot (x y : X.Obj) : (homDiagram h x y).obj ⊥ ≅ X.enriched.Hom x y :=
  eqToIso (congrArg₂ (h.F.obj ⊥).enriched.Hom (moving_bot h x) (moving_bot h y)) ≪≫
    (DaggerSimplicialIsoHoms.homIso h.isoBot.symm x y).symm

/-- Its inverse is the original inverse Hom map followed by bottom casts. -/
theorem isoBot_inv (x y : X.Obj) :
    (isoBot h x y).inv = h.isoBot.inv.map x y ≫
      eqToHom (congrArg₂ (h.F.obj ⊥).enriched.Hom
        (moving_bot h x).symm (moving_bot h y).symm) := rfl

end

end DaggerModels.OriginalOrdinaryHomTransfinite
