import ChosenNecklaceChosenComparison
import ChosenNecklaceGeneralNCMap
import ChosenNecklaceMapInclusion

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- Whole comparison on every actual SSet map of necklaces, even without outer-endpoint preservation. -/
theorem chosenNecklaceIso_naturality {T U : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    C.map f ≫ (chosenNecklaceIso U).hom =
      (chosenNecklaceIso T).hom ≫ generalNCMap f := by
  apply forgetNC_cancel U
  rw [Category.assoc, chosenNecklaceIso_inclusion, Category.assoc, generalNCMap_forget]
  rw [← Category.assoc (chosenNecklaceIso T).hom (forgetNC T),
    chosenNecklaceIso_inclusion, Category.assoc]
  let α : ⦋T.len⦌ ⟶ ⦋U.len⦌ := SimplexCategory.Hom.mk (orderMap f)
  have hρ := ρ.hom.naturality α
  change C.map (SSet.stdSimplex.map α) ≫ (ρ.app ⦋U.len⦌).hom =
    (ρ.app ⦋T.len⦌).hom ≫ DaggerChosenRigidificationNecklace.T.map α at hρ
  rw [← hρ]
  simp only [← Category.assoc, ← C.map_comp]
  rw [map_inclusion]

theorem chosenNecklaceIso_inv_naturality {T U : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    generalNCMap f ≫ (chosenNecklaceIso U).inv =
      (chosenNecklaceIso T).inv ≫ C.map f := by
  apply (cancel_epi (chosenNecklaceIso T).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← chosenNecklaceIso_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem chosenNecklaceIso_hom_naturality {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    C.map f.map ≫ (chosenNecklaceIso U).hom = (chosenNecklaceIso T).hom ≫ NCMap f := by
  rw [← generalNCMap_of_hom]
  exact chosenNecklaceIso_naturality f.map

end

end DaggerChosenRigidificationNecklace
