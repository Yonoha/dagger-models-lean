import ChosenNecklaceChosenNaturality
import ChosenNecklacesOver
import ChosenEnrichedFunctorMapEquality

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The original NC-to-chosen-C inverse followed by the supplied map to X. -/
def overChosenFunctor (P : NecklacesOver X a b) : NC.{u} P.code ⟶ C.obj X :=
  (chosenNecklaceIso P.code).inv ≫ C.map P.map

theorem overChosenFunctor_obj (P : NecklacesOver X a b) (v : (NC.{u} P.code).Obj) :
    (overChosenFunctor P).obj v =
      RV X (P.map.app _ (P.code.verticesEquiv.symm v.as)) := by
  change (C.map P.map).obj ((chosenNecklaceIso P.code).inv.obj v) = _
  rw [chosenNecklaceIso_inv_objects]
  exact DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality _ _

theorem overChosenFunctor_first (P : NecklacesOver X a b) :
    (overChosenFunctor P).obj ⟨ULift.up 0⟩ = RV X a := by
  rw [overChosenFunctor_obj]
  exact congrArg (RV X) P.first

theorem overChosenFunctor_last (P : NecklacesOver X a b) :
    (overChosenFunctor P).obj ⟨ULift.up (Fin.last P.code.len)⟩ = RV X b := by
  rw [overChosenFunctor_obj]
  exact congrArg (RV X) P.last

theorem overChosenFunctor_naturality {P Q : NecklacesOver X a b} (h : P ⟶ Q) :
    NCMap h.hom ≫ overChosenFunctor Q = overChosenFunctor P := by
  unfold overChosenFunctor
  rw [← generalNCMap_of_hom, ← Category.assoc, chosenNecklaceIso_inv_naturality,
    Category.assoc, ← C.map_comp, h.w]

end

end DaggerChosenRigidificationNecklace
