import ChosenNecklacesOver
import Mathlib.CategoryTheory.Limits.Types.ColimitType

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def flagDegreeDiagram (q : SimplexCategoryᵒᵖ) : NecklacesOver X a b ⥤ Type u where
  obj P := Flag.{u} P.code q.unop.len
  map h := NecklaceCode.Flag.map h.hom
  map_id P := by funext F; exact NecklaceCode.Flag.map_id F
  map_comp h k := by funext F; exact NecklaceCode.Flag.map_comp h.hom k.hom F

/-- Exactly the raw original necklace-over-X flag triples, without flankification. -/
abbrev RawFlag (q : SimplexCategoryᵒᵖ) :=
  Σ P : NecklacesOver X a b, Flag.{u} P.code q.unop.len

def flagRelation (q : SimplexCategoryᵒᵖ) : RawFlag X a b q → RawFlag X a b q → Prop :=
  (flagDegreeDiagram X a b q).ColimitTypeRel

/-- The actual Type-colimit quotient, with every original over-X arrow as a generator. -/
def flagHom : SSet.{u} where
  obj q := Quot (flagRelation X a b q)
  map α := Quot.map (fun p ↦ ⟨p.1, NecklaceCode.Flag.restrict α.unop.toOrderHom p.2⟩) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    refine ⟨h, ?_⟩
    change NecklaceCode.Flag.restrict α.unop.toOrderHom G =
      NecklaceCode.Flag.map h.hom (NecklaceCode.Flag.restrict α.unop.toOrderHom F)
    change G = NecklaceCode.Flag.map h.hom F at he
    rw [he]
    exact NecklaceCode.Flag.restrict_map _ _ _)
  map_id q := by
    funext t
    induction t using Quot.ind with | _ p
    apply congrArg (Quot.mk _)
    apply Sigma.ext rfl
    exact heq_of_eq (NecklaceCode.Flag.ext (fun _ ↦ rfl))
  map_comp α β := by
    funext t
    induction t using Quot.ind with | _ p
    apply congrArg (Quot.mk _)
    apply Sigma.ext rfl
    exact heq_of_eq (NecklaceCode.Flag.ext (fun _ ↦ rfl))

theorem flagHom_degree (q : SimplexCategoryᵒᵖ) :
    (flagHom X a b).obj q = (flagDegreeDiagram X a b q).ColimitType := rfl

def flagLeg (P : NecklacesOver X a b) : flagSSet P.code ⟶ flagHom X a b where
  app _ F := Quot.mk _ ⟨P, F⟩
  naturality _ _ _ := rfl

def flagCocone : Cocone (NecklacesOver.flagDiagram X a b) where
  pt := flagHom X a b
  ι :=
    { app := flagLeg X a b
      naturality P Q h := by
        ext q F
        exact (Quot.sound ⟨h, rfl⟩).symm }

/-- Full arbitrary-target descent uses the supplied original cocone legs at every degree. -/
def flagDesc (s : Cocone (NecklacesOver.flagDiagram X a b)) : flagHom X a b ⟶ s.pt where
  app q := Quot.lift (fun p ↦ (s.ι.app p.1).app q p.2) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    change G = NecklaceCode.Flag.map h.hom F at he
    rw [he]
    exact (congrFun (NatTrans.congr_app (s.ι.naturality h) q) F).symm)
  naturality p q α := by
    funext t
    induction t using Quot.ind with | _ t
    exact congrFun ((s.ι.app t.1).naturality α) t.2

def flagIsColimit : IsColimit (flagCocone X a b) where
  desc := flagDesc X a b
  fac s P := rfl
  uniq s k hk := by
    ext q t
    induction t using Quot.ind with | _ t
    exact congrFun (NatTrans.congr_app (hk t.1) q) t.2

end

end DaggerChosenRigidificationNecklace
