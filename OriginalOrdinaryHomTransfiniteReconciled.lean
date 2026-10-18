import OriginalOrdinaryTransfiniteHomDiagramReconciled
import OriginalOrdinaryHomRetractsReconciled

/-!
# Original ordinary Hom maps along a transfinite composition

The full original transfinite arrow induces a transfinite composition of its
actual Hom maps. The bottom and final maps retain the original arrow, while
successor endpoint casts preserve the supplied local anodyne property.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels OriginalOrdinaryMovingHomColimits

universe u

namespace DaggerModels.OriginalOrdinaryHomTransfinite

noncomputable section

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : SimplicialCat.{u, u}} {f : X ⟶ Y}
variable (h : CategoryTheory.TransfiniteCompositionOfShape J f)

/-- The forward bottom iso map is the original full enriched map with endpoint casts. -/
theorem isoBot_hom (x y : X.Obj) :
    (isoBot h x y).hom =
      castMap h.isoBot.hom (movingObj h x ⊥) (movingObj h y ⊥) x y
        ((congrArg h.isoBot.hom.obj (moving_bot h x)).trans
          (congrArg (fun g : X ⟶ X ↦ g.obj x) h.isoBot.inv_hom_id))
        ((congrArg h.isoBot.hom.obj (moving_bot h y)).trans
          (congrArg (fun g : X ⟶ X ↦ g.obj y) h.isoBot.inv_hom_id)) := by
  apply (cancel_mono (isoBot h x y).inv).1
  rw [Iso.hom_inv_id, isoBot_inv]
  change 𝟙 _ = castMap h.isoBot.hom _ _ x y _ _ ≫
    castMap h.isoBot.inv x y _ _ (moving_bot h x).symm (moving_bot h y).symm
  rw [← castMap_comp]
  rw [castMap_congr h.isoBot.hom_inv_id (movingObj h x ⊥) (movingObj h y ⊥)
    (movingObj h x ⊥) (movingObj h y ⊥)
    (congrArg (fun g : h.F.obj ⊥ ⟶ h.F.obj ⊥ ↦ g.obj (movingObj h x ⊥))
      h.isoBot.hom_inv_id)
    (congrArg (fun g : h.F.obj ⊥ ⟶ h.F.obj ⊥ ↦ g.obj (movingObj h y ⊥))
      h.isoBot.hom_inv_id) rfl rfl]
  simp [castMap]

/-- The full Hom factorization is the same original `f.map x y`. -/
theorem hom_fac (x y : X.Obj) :
    (isoBot h x y).inv ≫ (homCocone h x y).ι.app ⊥ = f.map x y := by
  rw [isoBot_inv]
  change castMap h.isoBot.inv x y _ _ (moving_bot h x).symm (moving_bot h y).symm ≫
    castMap (h.incl.app ⊥) (movingObj h x ⊥) (movingObj h y ⊥) (f.obj x) (f.obj y)
      (finalEndpoint h x ⊥) (finalEndpoint h y ⊥) = f.map x y
  rw [← castMap_comp]
  rw [castMap_congr h.fac x y (f.obj x) (f.obj y)
    (congrArg (fun g : X ⟶ Y ↦ g.obj x) h.fac)
    (congrArg (fun g : X ⟶ Y ↦ g.obj y) h.fac) rfl rfl]
  simp [castMap]

variable (hlocal : ∀ j, ¬IsMax j →
  OriginalOrdinaryHomRetracts.localHomProperty SSet.anodyneExtensions.{u}
    (h.F.map (homOfLE (Order.le_succ j))))

include hlocal in
/-- The original successor Hom map is anodyne after both endpoint transports. -/
theorem successor_anodyne (x y : X.Obj) (j : J) (hj : ¬IsMax j) :
    SSet.anodyneExtensions ((homDiagram h x y).map (homOfLE (Order.le_succ j))) := by
  let e := eqToIso (congrArg₂ (h.F.obj (Order.succ j)).enriched.Hom
    (moving_naturality h x (homOfLE (Order.le_succ j)))
    (moving_naturality h y (homOfLE (Order.le_succ j))))
  let i := (h.F.map (homOfLE (Order.le_succ j))).map (movingObj h x j) (movingObj h y j)
  have eArrow : Arrow.mk i ≅
      Arrow.mk ((homDiagram h x y).map (homOfLE (Order.le_succ j))) :=
    Arrow.isoMk (Iso.refl _) e (Category.id_comp _)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff eArrow).1
    (hlocal j hj (movingObj h x j) (movingObj h y j))

/-- The full anodyne transfinite record has the exact original Hom arrow. -/
def homTransfinite (x y : X.Obj) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape J (f.map x y) where
  F := homDiagram h x y
  isoBot := isoBot h x y
  isWellOrderContinuous := homWellOrderContinuous h x y
  incl := (homCocone h x y).ι
  isColimit := finalIsColimit h x y
  fac := hom_fac h x y
  map_mem := successor_anodyne h hlocal x y

end

end DaggerModels.OriginalOrdinaryHomTransfinite
