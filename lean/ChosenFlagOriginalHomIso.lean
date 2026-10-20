import ChosenFlagChosenIso
import SimplicialIsoHoms

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- The full SSet isomorphism has literally the specified original enriched map as its hom. -/
def flagOriginalHomIso : flagHom X a b ≅ (RV X a ⟶[SSet.{u}] RV X b) :=
  DaggerSimplicialIsoHoms.homIso (flagChosenIso X) a b

theorem flagOriginalHomIso_hom : (flagOriginalHomIso X a b).hom = chosenFlagHom X a b := rfl

def flagInverseEndpoint (a : X.obj (op ⦋0⦌)) :
    (flagChosenIso X).inv.obj (RV X a) = a :=
  (flagChosenIso_inv_obj X (RV X a)).trans ((RV X).symm_apply_apply a)

/-- The prescribed inverse, retaining the same original θ.inv map and both endpoint casts. -/
def flagOriginalHomInverse : (RV X a ⟶[SSet.{u}] RV X b) ⟶ flagHom X a b :=
  (flagChosenIso X).inv.map (RV X a) (RV X b) ≫
    targetHomTransport (flagInverseEndpoint X a) (flagInverseEndpoint X b)

theorem flagOriginalHomInverse_left :
    (flagOriginalHomIso X a b).hom ≫ flagOriginalHomInverse X a b = 𝟙 _ := by
  have H := enrichedFunctor_hom_congr (flagChosenIso X).hom_inv_id a b
    (flagInverseEndpoint X a) (flagInverseEndpoint X b)
  change ((flagChosenIso X).hom.map a b ≫
    (flagChosenIso X).inv.map (RV X a) (RV X b)) ≫
      targetHomTransport (flagInverseEndpoint X a) (flagInverseEndpoint X b) = 𝟙 _ at H
  simpa only [flagOriginalHomIso, DaggerSimplicialIsoHoms.homIso, asIso_hom,
    flagOriginalHomInverse, Category.assoc] using H

/-- Inverse uniqueness identifies the full natural inverse, rather than only degree bijections. -/
theorem flagOriginalHomIso_inv :
    (flagOriginalHomIso X a b).inv = flagOriginalHomInverse X a b := by
  apply (cancel_epi (flagOriginalHomIso X a b).hom).mp
  rw [Iso.hom_inv_id, flagOriginalHomInverse_left]

theorem flagOriginalHomInverse_right :
    flagOriginalHomInverse X a b ≫ (flagOriginalHomIso X a b).hom = 𝟙 _ := by
  rw [← flagOriginalHomIso_inv]
  exact Iso.inv_hom_id _

theorem flagOriginalHomIso_raw (P : NecklacesOver X a b) (q : SimplexCategoryᵒᵖ)
    (p : NecklaceCode.Flag.{u} P.code q.unop.len) :
    (flagOriginalHomIso X a b).hom.app q (Quot.mk _ ⟨P, p⟩) =
      (chosenFlagLeg P).app q p := rfl

theorem flagOriginalHomIso_operator {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : (flagHom X a b).obj q) :
    (flagOriginalHomIso X a b).hom.app r ((flagHom X a b).map α p) =
      (RV X a ⟶[SSet.{u}] RV X b).map α ((flagOriginalHomIso X a b).hom.app q p) :=
  congrFun ((flagOriginalHomIso X a b).hom.naturality α) p

theorem flagOriginalHomInverse_operator {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : (RV X a ⟶[SSet.{u}] RV X b).obj q) :
    (flagOriginalHomInverse X a b).app r ((RV X a ⟶[SSet.{u}] RV X b).map α p) =
      (flagHom X a b).map α ((flagOriginalHomInverse X a b).app q p) :=
  congrFun ((flagOriginalHomInverse X a b).naturality α) p

theorem flagOriginalHomIso_identity :
    flagIdentity X a ≫ (flagOriginalHomIso X a a).hom = eId SSet (RV X a) :=
  chosenFlagHom_identity X a

theorem flagOriginalHomIso_composition (c : X.obj (op ⦋0⦌)) :
    flagComposition X a b c ≫ (flagOriginalHomIso X a c).hom =
      ((flagOriginalHomIso X a b).hom ⊗ₘ (flagOriginalHomIso X b c).hom) ≫
        eComp SSet (RV X a) (RV X b) (RV X c) := chosenFlagHom_composition X a b c

end

end DaggerChosenRigidificationNecklace
