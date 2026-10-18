import ChosenFlagChosenSimplex
import ChosenFlagEndomorphismExt

open CategoryTheory Functor Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

/-- The original chosen-C simplex descent, using the exact flag simplex cocone. -/
def chosenFlagInverse (X : SSet.{u}) : C.obj X ⟶ E X :=
  simplexDesc X (flagSimplexCocone X)

theorem chosenFlagInverse_fac (X : SSet.{u}) (σ : SimplexIndex X) :
    thickeningUnit.app σ.left ≫ C.map σ.hom ≫ chosenFlagInverse X = simplexFlagLeg X σ :=
  simplexDesc_fac X (flagSimplexCocone X) σ

theorem chosenFlagInverse_forward (X : SSet.{u}) :
    chosenFlagInverse X ≫ chosenFlagFunctor X = 𝟙 (C.obj X) := by
  apply (simplexCoconeIsColimit X).hom_ext
  intro σ
  change (thickeningUnit.app σ.left ≫ C.map σ.hom) ≫
    (chosenFlagInverse X ≫ chosenFlagFunctor X) =
      (thickeningUnit.app σ.left ≫ C.map σ.hom) ≫ 𝟙 _
  rw [← Category.assoc, Category.assoc (thickeningUnit.app σ.left) (C.map σ.hom),
    chosenFlagInverse_fac X σ, simplexFlagLeg_chosen, Category.comp_id]

theorem chosenFlagInverse_obj (X : SSet.{u}) (x : (C.obj X).Obj) :
    (chosenFlagInverse X).obj x = (RV X).symm x := by
  apply (RV X).injective
  rw [Equiv.apply_symm_apply]
  exact congrArg (fun F ↦ F.obj x) (chosenFlagInverse_forward X)

def mappedSimplex {X Y : SSet.{u}} (f : X ⟶ Y) (σ : SimplexIndex X) : SimplexIndex Y :=
  CostructuredArrow.mk (σ.hom ≫ f)

theorem chosenFlagInverse_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    C.map f ≫ chosenFlagInverse Y = chosenFlagInverse X ≫ EMap f := by
  apply (simplexCoconeIsColimit X).hom_ext
  intro σ
  change (thickeningUnit.app σ.left ≫ C.map σ.hom) ≫
    (C.map f ≫ chosenFlagInverse Y) =
      (thickeningUnit.app σ.left ≫ C.map σ.hom) ≫ (chosenFlagInverse X ≫ EMap f)
  have HL := chosenFlagInverse_fac Y (mappedSimplex f σ)
  change thickeningUnit.app σ.left ≫ C.map (σ.hom ≫ f) ≫ chosenFlagInverse Y =
    simplexFlagUnit.app σ.left ≫ EMap (σ.hom ≫ f) at HL
  rw [← Category.assoc, ← Category.assoc,
    Category.assoc (thickeningUnit.app σ.left) (C.map σ.hom) (chosenFlagInverse X),
    chosenFlagInverse_fac X σ]
  simp only [Category.assoc]
  rw [← Category.assoc (C.map σ.hom) (C.map f), ← C.map_comp, HL]
  unfold simplexFlagLeg
  rw [EMap_comp]
  exact Category.assoc _ _ _

end

end DaggerChosenRigidificationNecklace
