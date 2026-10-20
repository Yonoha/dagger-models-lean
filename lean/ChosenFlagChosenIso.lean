import ChosenFlagChosenInverse

open CategoryTheory Functor Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

/-- Literal necklace comparison supplies the same inverse equation, not a separate choice. -/
theorem chosenFlagFunctor_necklace_inverse (T : NecklaceCode) :
    chosenFlagFunctor T.toSSet ≫ chosenFlagInverse T.toSSet = 𝟙 (E T.toSSet) := by
  haveI : IsIso (chosenFlagFunctor T.toSSet) := by
    rw [chosenFlagFunctor_necklace_exact]
    infer_instance
  apply (cancel_mono (chosenFlagFunctor T.toSSet)).mp
  rw [Category.assoc, chosenFlagInverse_forward, Category.comp_id, Category.id_comp]

/-- The second full inverse law uses every original quotient representative. -/
theorem chosenFlagFunctor_inverse (X : SSet.{u}) :
    chosenFlagFunctor X ≫ chosenFlagInverse X = 𝟙 (E X) := by
  apply flagEndomorphism_eq_id X
  · intro x
    change (chosenFlagInverse X).obj (RV X x) = x
    rw [chosenFlagInverse_obj, Equiv.symm_apply_apply]
  · intro a b P
    rw [← Category.assoc, chosenFlagFunctor_naturality, Category.assoc,
      chosenFlagInverse_naturality, ← Category.assoc, chosenFlagFunctor_necklace_inverse,
      Category.id_comp]

/-- Full original chosen-C comparison, with both equations and the specified original objects. -/
def flagChosenIso (X : SSet.{u}) : E X ≅ C.obj X where
  hom := chosenFlagFunctor X
  inv := chosenFlagInverse X
  hom_inv_id := chosenFlagFunctor_inverse X
  inv_hom_id := chosenFlagInverse_forward X

/-- All X maps and simplex operators are retained by the same full natural comparison. -/
def flagChosenNatIso : flagCategoryFunctor.{u} ≅ C :=
  NatIso.ofComponents flagChosenIso (fun f ↦ chosenFlagFunctor_naturality f)

theorem flagChosenIso_obj (X : SSet.{u}) (x : (E X).Obj) :
    (flagChosenIso X).hom.obj x = RV X x := rfl

theorem flagChosenIso_inv_obj (X : SSet.{u}) (x : (C.obj X).Obj) :
    (flagChosenIso X).inv.obj x = (RV X).symm x := chosenFlagInverse_obj X x

theorem flagChosenIso_simplex_leg (X : SSet.{u}) (σ : SimplexIndex X) :
    simplexFlagLeg X σ ≫ (flagChosenIso X).hom =
      thickeningUnit.app σ.left ≫ C.map σ.hom := simplexFlagLeg_chosen X σ

theorem flagChosenIso_simplex_inverse_leg (X : SSet.{u}) (σ : SimplexIndex X) :
    thickeningUnit.app σ.left ≫ C.map σ.hom ≫ (flagChosenIso X).inv =
      simplexFlagLeg X σ := chosenFlagInverse_fac X σ

end

end DaggerChosenRigidificationNecklace
