import ChosenFlagSimplexNaturality

open CategoryTheory Functor Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

/-- The same full inverse on each original representable. -/
def simplexFlagUnit : T.{u} ⟶ uliftYoneda.{u} ⋙ flagCategoryFunctor where
  app n := (flagSimplexIso n.len).inv
  naturality n m α := by
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    exact flagSimplexIso_inv_naturality α

/-- Original simplex legs, with the supplied simplex map and the specified full inverse. -/
def simplexFlagLeg (X : SSet.{u}) (σ : SimplexIndex X) : T.obj σ.left ⟶ E X :=
  simplexFlagUnit.app σ.left ≫ EMap σ.hom

/-- The actual full enriched simplex cocone; its UP is a separate obligation. -/
def flagSimplexCocone (X : SSet.{u}) : Cocone (simplexDiagram X) :=
  (LeftExtension.mk flagCategoryFunctor simplexFlagUnit).coconeAt X

theorem flagSimplexCocone_pt (X : SSet.{u}) : (flagSimplexCocone X).pt = E X := rfl

theorem flagSimplexCocone_leg (X : SSet.{u}) (σ : SimplexIndex X) :
    (flagSimplexCocone X).ι.app σ = simplexFlagLeg X σ := rfl

theorem simplexFlagLeg_obj (X : SSet.{u}) (σ : SimplexIndex X)
    (a : (T.obj σ.left).Obj) :
    (simplexFlagLeg X σ).obj a =
      σ.hom.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.{u}.symm a.as.down) := by
  change σ.hom.app (op ⦋0⦌) ((flagSimplexIso σ.left.len).inv.obj a) = _
  rw [flagSimplexIso_inv_obj]
  rfl

theorem simplexFlagLeg_naturality (X : SSet.{u}) {σ τ : SimplexIndex X} (f : σ ⟶ τ) :
    T.map f.left ≫ simplexFlagLeg X τ = simplexFlagLeg X σ :=
  (flagSimplexCocone X).ι.naturality f

end

end DaggerChosenRigidificationNecklace
