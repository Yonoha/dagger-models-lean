import ChosenFlagHomComposition

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

variable (X : SSet.{u})

def flagIdentity (a : X.obj (op ⦋0⦌)) : 𝟙_ SSet.{u} ⟶ flagHom X a a where
  app q _ := flagIdApp a q
  naturality _ _ α := by
    funext x
    exact (flagIdApp_operator α a).symm

def flagComposition (a b c : X.obj (op ⦋0⦌)) :
    flagHom X a b ⊗ flagHom X b c ⟶ flagHom X a c where
  app _ x := flagCompApp x.1 x.2
  naturality _ _ α := by
    funext x
    exact (flagCompApp_operator α x.1 x.2).symm

/-- The full simplicial enrichment retains every original vertex and every unflanked flag. -/
instance flagEnriched : EnrichedCategory SSet.{u} (X.obj (op ⦋0⦌)) where
  Hom := flagHom X
  id := flagIdentity X
  comp := flagComposition X
  id_comp a b := by
    ext q x
    exact flagCompApp_id_left x
  comp_id a b := by
    ext q x
    exact flagCompApp_id_right x
  assoc a b c d := by
    ext q x
    exact flagCompApp_assoc x.1 x.2.1 x.2.2

/-- Bundled original simplicial category; its object type is literally X in degree zero. -/
def E : DaggerModels.SimplicialCat.{u,u} := DaggerModels.SimplicialCat.of (X.obj (op ⦋0⦌))

theorem E_obj : (E X).Obj = X.obj (op ⦋0⦌) := rfl

theorem E_hom (a b : X.obj (op ⦋0⦌)) : (E X).enriched.Hom a b = flagHom X a b := rfl

theorem E_id_app (a : X.obj (op ⦋0⦌)) (q : SimplexCategoryᵒᵖ) :
    (eId SSet a).app q PUnit.unit = flagIdApp a q := rfl

theorem E_comp_app (a b c : X.obj (op ⦋0⦌)) (q : SimplexCategoryᵒᵖ)
    (x : (flagHom X a b).obj q) (y : (flagHom X b c).obj q) :
    (eComp SSet a b c).app q (x,y) = flagCompApp x y := rfl

end

end DaggerChosenRigidificationNecklace
