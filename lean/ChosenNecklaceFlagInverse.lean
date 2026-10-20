import ChosenNecklaceInverseHom

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode)

/-- Invert the same original evaluation, using its specified vertex inverse and Hom inverses. -/
def necklaceFlagInverse : NC.{u} T ⟶ E (toSSet.{u} T) where
  obj a := T.verticesEquiv.symm a.as
  map a b := (necklaceInverseHomIso T a b).inv
  map_id a := by
    change pathId a ≫ (necklaceInverseHomIso T a a).inv =
      flagIdentity (toSSet T) (T.verticesEquiv.symm a.as)
    apply (cancel_mono (necklaceInverseHomIso T a a).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, necklaceInverseHomIso_identity]
  map_comp a b c := by
    change pathComp a b c ≫ (necklaceInverseHomIso T a c).inv =
      ((necklaceInverseHomIso T a b).inv ⊗ₘ (necklaceInverseHomIso T b c).inv) ≫
        flagComposition (toSSet T) (T.verticesEquiv.symm a.as) (T.verticesEquiv.symm b.as)
          (T.verticesEquiv.symm c.as)
    apply (cancel_mono (necklaceInverseHomIso T a c).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, necklaceInverseHomIso_composition, ← Category.assoc,
      tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id]
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp]

theorem necklaceFlagInverse_obj (a : NecklaceThickening.{u} T) :
    (necklaceFlagInverse T).obj a = T.verticesEquiv.symm a.as := rfl

theorem necklaceFlagInverse_original_hom (a b : NecklaceThickening.{u} T) :
    (necklaceFlagInverse T).map a b = (necklaceInverseHomIso T a b).inv := rfl

end

end DaggerChosenRigidificationNecklace
