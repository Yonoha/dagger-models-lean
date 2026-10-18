import OriginalGateMonicRepresentative
import OriginalFlagFiberTerminal

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (S : Set (X.obj (op ⦋0⦌)))

/-- All original over-X arrows between monomorphic necklaces containing the given joints. -/
def monicGatePredicate : ObjectProperty (NecklacesOver X a b) :=
  fun P ↦ Mono P.map ∧ S ⊆ necklaceJointImage P

abbrev MonicGateNecklaces := (monicGatePredicate a b S).FullSubcategory

/-- The restriction of the original flag diagram, with every arrow of the full subcategory. -/
def monicGateFlagDiagram : MonicGateNecklaces a b S ⥤ SSet.{u} :=
  (monicGatePredicate a b S).ι ⋙ NecklacesOver.flagDiagram X a b

def monicGateDegreeDiagram (q : SimplexCategoryᵒᵖ) : MonicGateNecklaces a b S ⥤ Type u where
  obj P := Flag.{u} P.obj.code q.unop.len
  map h := NecklaceCode.Flag.map h.hom.hom
  map_id P := by funext F; exact NecklaceCode.Flag.map_id F
  map_comp h k := by funext F; exact NecklaceCode.Flag.map_comp h.hom.hom k.hom.hom F

/-- Raw flags on the specified full subcategory; no flank restriction is imposed. -/
abbrev MonicGateRawFlag (q : SimplexCategoryᵒᵖ) :=
  Σ P : MonicGateNecklaces a b S, Flag.{u} P.obj.code q.unop.len

def monicGateRelation (q : SimplexCategoryᵒᵖ) : MonicGateRawFlag a b S q → MonicGateRawFlag a b S q → Prop :=
  (monicGateDegreeDiagram a b S q).ColimitTypeRel

/-- The degreewise colimit quotient of the restricted original flag diagram. -/
def monicGateHom : SSet.{u} where
  obj q := Quot (monicGateRelation a b S q)
  map α := Quot.map (fun p ↦ ⟨p.1, NecklaceCode.Flag.restrict α.unop.toOrderHom p.2⟩) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    refine ⟨h, ?_⟩
    change NecklaceCode.Flag.restrict α.unop.toOrderHom G =
      NecklaceCode.Flag.map h.hom.hom (NecklaceCode.Flag.restrict α.unop.toOrderHom F)
    change G = NecklaceCode.Flag.map h.hom.hom F at he
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

theorem monicGateHom_degree (q : SimplexCategoryᵒᵖ) :
    (monicGateHom a b S).obj q = (monicGateDegreeDiagram a b S q).ColimitType := rfl

def monicGateLeg (P : MonicGateNecklaces a b S) : flagSSet P.obj.code ⟶ monicGateHom a b S where
  app _ F := Quot.mk _ ⟨P, F⟩
  naturality _ _ _ := rfl

def monicGateCocone : Cocone (monicGateFlagDiagram a b S) where
  pt := monicGateHom a b S
  ι :=
    { app := monicGateLeg a b S
      naturality P Q h := by
        ext q F
        exact (Quot.sound ⟨h, rfl⟩).symm }

/-- Full arbitrary-target descent uses the supplied original cocone legs at every degree. -/
def monicGateDesc (s : Cocone (monicGateFlagDiagram a b S)) : monicGateHom a b S ⟶ s.pt where
  app q := Quot.lift (fun p ↦ (s.ι.app p.1).app q p.2) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    change G = NecklaceCode.Flag.map h.hom.hom F at he
    rw [he]
    exact (congrFun (NatTrans.congr_app (s.ι.naturality h) q) F).symm)
  naturality p q α := by
    funext t
    induction t using Quot.ind with | _ t
    exact congrFun ((s.ι.app t.1).naturality α) t.2

def monicGateIsColimit : IsColimit (monicGateCocone a b S) where
  desc := monicGateDesc a b S
  fac s P := rfl
  uniq s k hk := by
    ext q t
    induction t using Quot.ind with | _ t
    exact congrFun (NatTrans.congr_app (hk t.1) q) t.2

end

end DaggerOriginalProductGadget
