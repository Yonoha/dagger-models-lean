import ChosenFlagChosenIdentity
import ChosenFlagChosenComposition

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

/-- The original raw flag quotient evaluated in the actual chosen C, without a UP premise. -/
def chosenFlagFunctor (X : SSet.{u}) : E X ⟶ C.obj X where
  obj := RV X
  map := chosenFlagHom X
  map_id := chosenFlagHom_identity X
  map_comp := chosenFlagHom_composition X

theorem chosenFlagFunctor_objects (X : SSet.{u}) (x : X.obj (op ⦋0⦌)) :
    (chosenFlagFunctor X).obj x = RV X x := rfl

theorem chosenFlagFunctor_hom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    (chosenFlagFunctor X).map a b = chosenFlagHom X a b := rfl

theorem chosenFlagFunctor_raw (X : SSet.{u}) {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) (q : SimplexCategoryᵒᵖ)
    (p : NecklaceCode.Flag.{u} P.code q.unop.len) :
    ((chosenFlagFunctor X).map a b).app q (Quot.mk _ ⟨P, p⟩) =
      (chosenFlagLeg P).app q p := rfl

end

end DaggerChosenRigidificationNecklace
