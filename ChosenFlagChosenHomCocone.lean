import ChosenNecklaceOverChosenFunctor
import ChosenNecklaceOuterMapTransport
import ChosenFlagHomColimit

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- Same original supplied necklace map, original flags and both endpoint transports. -/
def chosenFlagLeg (P : NecklacesOver X a b) :
    flagSSet.{u} P.code ⟶ (RV X a ⟶[SSet.{u}] RV X b) :=
  (outerFlagIso P.code).hom ≫
    (overChosenFunctor P).map (outerLeft P.code) (outerRight P.code) ≫
      targetHomTransport (overChosenFunctor_first P) (overChosenFunctor_last P)

theorem chosenFlagLeg_naturality {P Q : NecklacesOver X a b} (h : P ⟶ Q) :
    flagMap h.hom ≫ chosenFlagLeg Q = chosenFlagLeg P := by
  let F := overChosenFunctor Q
  let hx := congrArg F.obj (NCMap_outerLeft h.hom)
  let hy := congrArg F.obj (NCMap_outerRight h.hom)
  let hcx := hx.trans (overChosenFunctor_first Q)
  let hcy := hy.trans (overChosenFunctor_last Q)
  have H := enrichedFunctor_hom_congr_to_fixed (overChosenFunctor_naturality h)
    (outerLeft P.code) (outerRight P.code) (RV X a) (RV X b)
    hcx hcy (overChosenFunctor_first P) (overChosenFunctor_last P)
  unfold chosenFlagLeg
  simp only [← Category.assoc]
  rw [outerFlagIso_naturality]
  simp only [Category.assoc]
  rw [outerMap_original]
  have Hcast :
      targetHomTransport (NCMap_outerLeft h.hom) (NCMap_outerRight h.hom) ≫
          F.map (outerLeft Q.code) (outerRight Q.code) ≫
            targetHomTransport (overChosenFunctor_first Q) (overChosenFunctor_last Q) =
        F.map ((NCMap h.hom).obj (outerLeft P.code))
            ((NCMap h.hom).obj (outerRight P.code)) ≫ targetHomTransport hcx hcy := by
    rw [← Category.assoc, enriched_map_endpoint_transport, Category.assoc,
      targetHomTransport_trans]
  simp only [Category.assoc]
  rw [Hcast]
  simp only [← Category.assoc]
  change (outerFlagIso P.code).hom ≫
    ((NCMap h.hom ≫ overChosenFunctor Q).map (outerLeft P.code) (outerRight P.code) ≫
      targetHomTransport hcx hcy) = _
  rw [H]
  rfl

def chosenFlagHomCocone (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    Cocone (NecklacesOver.flagDiagram X a b) where
  pt := (RV X a ⟶[SSet.{u}] RV X b)
  ι := { app := chosenFlagLeg, naturality _ _ h := chosenFlagLeg_naturality h }

/-- Actual quotient descent, with all-degree and full simplex naturality already in flagDesc. -/
def chosenFlagHom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    flagHom X a b ⟶ (RV X a ⟶[SSet.{u}] RV X b) :=
  flagDesc X a b (chosenFlagHomCocone X a b)

theorem chosenFlagHom_leg (P : NecklacesOver X a b) :
    flagLeg X a b P ≫ chosenFlagHom X a b = chosenFlagLeg P := rfl

theorem chosenFlagHom_operator {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (x : (flagHom X a b).obj q) :
    (RV X a ⟶[SSet.{u}] RV X b).map α ((chosenFlagHom X a b).app q x) =
      (chosenFlagHom X a b).app r ((flagHom X a b).map α x) :=
  (congrFun ((chosenFlagHom X a b).naturality α) x).symm

end

end DaggerChosenRigidificationNecklace
