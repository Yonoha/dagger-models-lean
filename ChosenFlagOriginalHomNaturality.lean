import ChosenFlagOriginalHomIso
import ChosenFlagChosenPostcomp

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable {X Y : SSet.{u}}

/-- The literal original C.map, with both RV endpoint equalities in their actual direction. -/
def originalChosenHomMap (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    (RV X a ⟶[SSet.{u}] RV X b) ⟶ (RV Y (f.app _ a) ⟶[SSet.{u}] RV Y (f.app _ b)) :=
  (C.map f).map (RV X a) (RV X b) ≫ targetHomTransport
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f a)
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality f b)

/-- Both endpoints are transported, even when the original object map identifies them. -/
theorem flagOriginalHomIso_naturality (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    flagHomMap f ≫ (flagOriginalHomIso Y (f.app _ a) (f.app _ b)).hom =
      (flagOriginalHomIso X a b).hom ≫ originalChosenHomMap f a b := by
  ext q t
  induction t using Quot.ind with | _ p
  exact congrFun (NatTrans.congr_app (chosenFlagLeg_postcomp f p.1) q) p.2

/-- The same full inverse square follows from the exact forward square and both inverse laws. -/
theorem flagOriginalHomInverse_naturality (f : X ⟶ Y) (a b : X.obj (op ⦋0⦌)) :
    flagOriginalHomInverse X a b ≫ flagHomMap f =
      originalChosenHomMap f a b ≫ flagOriginalHomInverse Y (f.app _ a) (f.app _ b) := by
  rw [← flagOriginalHomIso_inv X a b,
    ← flagOriginalHomIso_inv Y (f.app _ a) (f.app _ b)]
  apply (cancel_mono (flagOriginalHomIso Y (f.app _ a) (f.app _ b)).hom).mp
  rw [Category.assoc, flagOriginalHomIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem flagOriginalHomInverse_apply_hom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) (p : (flagHom X a b).obj q) :
    (flagOriginalHomInverse X a b).app q ((flagOriginalHomIso X a b).hom.app q p) = p :=
  congrFun (NatTrans.congr_app (flagOriginalHomInverse_left X a b) q) p

theorem flagOriginalHomIso_apply_inverse (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) (p : (RV X a ⟶[SSet.{u}] RV X b).obj q) :
    (flagOriginalHomIso X a b).hom.app q ((flagOriginalHomInverse X a b).app q p) = p :=
  congrFun (NatTrans.congr_app (flagOriginalHomInverse_right X a b) q) p

end

end DaggerChosenRigidificationNecklace
