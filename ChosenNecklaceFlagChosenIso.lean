import ChosenNecklaceFlagGeneralNaturality
import ChosenNecklaceChosenNaturality

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- Whole original quotient enrichment compared with the actual chosen C on a necklace. -/
def flagChosenNecklaceIso (T : NecklaceCode) : E (toSSet.{u} T) ≅ C.obj T.toSSet :=
  necklaceFlagIso T ≪≫ (chosenNecklaceIso T).symm

theorem flagChosenNecklaceIso_obj (T : NecklaceCode) (x : (E (toSSet.{u} T)).Obj) :
    (flagChosenNecklaceIso T).hom.obj x = RV T.toSSet x := by
  change (chosenNecklaceIso T).inv.obj ⟨T.verticesEquiv x⟩ = _
  rw [chosenNecklaceIso_inv_objects, Equiv.symm_apply_apply]

theorem flagChosenNecklaceIso_inv_obj (T : NecklaceCode)
    (x : (C.{u}.obj T.toSSet).Obj) :
    (flagChosenNecklaceIso T).inv.obj x = (RV T.toSSet).symm x := by
  change (necklaceFlagInverse T).obj ((chosenNecklaceIso T).hom.obj x) = _
  rw [chosenNecklaceIso_objects]
  change T.verticesEquiv.symm (T.verticesEquiv ((RV T.toSSet).symm x)) = _
  exact T.verticesEquiv.symm_apply_apply _

/-- Every actual map, including collapsing maps and non-outer endpoint maps. -/
theorem flagChosenNecklaceIso_naturality {T U : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    EMap f ≫ (flagChosenNecklaceIso U).hom =
      (flagChosenNecklaceIso T).hom ≫ C.map f := by
  change EMap f ≫ (necklaceFlagFunctor U ≫ (chosenNecklaceIso U).inv) =
    (necklaceFlagFunctor T ≫ (chosenNecklaceIso T).inv) ≫ C.map f
  rw [← Category.assoc, necklaceFlagFunctor_general_naturality, Category.assoc,
    chosenNecklaceIso_inv_naturality, ← Category.assoc]

theorem flagChosenNecklaceIso_inv_naturality {T U : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    C.map f ≫ (flagChosenNecklaceIso U).inv =
      (flagChosenNecklaceIso T).inv ≫ EMap f := by
  apply (cancel_epi (flagChosenNecklaceIso T).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← flagChosenNecklaceIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end DaggerChosenRigidificationNecklace
